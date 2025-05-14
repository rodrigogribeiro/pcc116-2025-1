-- Aula 04. Programação funcional e recursividade 

import Mathlib.Tactic.Basic

-- 1. Números Naturais (definidos na biblioteca: Tipo Nat)

inductive N where 
| zero : N 
| succ : N → N 
deriving Repr 
-- zero, succ zero, succ (succ zero), ...

-- convertendo entre N e Nat 

def toN (n : Nat) : N := 
  match n with 
  | 0 => N.zero 
  | k + 1 => N.succ (toN k)

#eval toN 3

-- definindo a adição 

def plus (n m : N) : N := 
  match n with 
  | N.zero => m                       -- 1
  | N.succ n' => N.succ (plus n' m)   -- 2 

open N 

infixl:60 " .+. " => plus 

-- Lousa: execução de 
--    (succ (succ zero)) .+. (succ zero) 
-- representando N como números 
/-
(succ (succ zero)) .+. (succ zero) =  
-/
-- Primeiro lemma simples 

-- obter uma igualdade trivial (x = x) por simplificação 
-- dizemos que essa igualdade vale por *definição*

lemma plus_0_l (n : N) 
  : zero .+. n = n := by
  sorry  

-- Segundo lemma 

lemma plus_0_r (n : N) 
  : n .+. zero = n := by
    sorry 

lemma plus_succ m n 
  : succ (m .+. n) = m .+. succ n := by
    sorry 

theorem plus_comm (n m : N) 
  : n .+. m = m .+. n := by 
  sorry 

theorem plus_assoc (n m p) 
  : n .+. m .+. p = n .+. (m .+. p) := by
  sorry 

-- implementar multiplicação e sua prova de comutatividade 
-- e associatividade. 

def mult (n m : N) : N := 
  match n with 
  | N.zero => N.zero 
  | N.succ n' => m .+. (mult n' m)

infix:65 " .*. " => mult

-- * Exercício 01: prove que a multiplicação é comutativa

lemma mult_0_r (n : N) : n .*. N.zero = N.zero := by 
  sorry 

lemma mult_succ (m n : N) : 
  m .*. succ n = m .+. m .*. n := by 
  sorry    

theorem mult_comm (n m : N) 
  : n .*. m = m .*. n := by 
  sorry 

-- definição de double 

def double (n : N) : N := 
  match n with 
  | zero => zero 
  | succ n' => succ (succ (double n'))

lemma double_correct n
  : double n = n .+. n := by 
  sorry 

lemma double_correct1 n : double n = (toN 2) .*. n := by 
  sorry 

-- teste de igualdade 

-- Prop ≃ Bool: isomorficas. 

def eqN (n m : N) : Bool := 
  match n , m with 
  | zero, zero => true 
  | succ n', succ m' => eqN n' m' 
  | _ , _ => false 

lemma eqN_refl n : eqN n n = true := by
  induction n with 
  | zero => simp [eqN] 
  | succ n' IH => simp [eqN, IH]

-- generalizar a hipótese de indução.

/-
∀ (x : A), P x -- mais geral 

A → P = ∀ (_ : A), P -- x não ocorre em P
-/

lemma eqN_sound n m
  : eqN n m = true → n = m := by 
  sorry 

lemma eqN_complete n m 
  : n = m → eqN n m = true := by
  sorry 

lemma eqN_sound_neq n m 
  : eqN n m = false → n ≠ m := sorry 

lemma eqN_complete_neq n m 
  : n ≠ m → eqN n m = false := sorry 

def leb (n m : N) : Bool := 
  match n, m with 
  | N.zero, _ => true 
  | N.succ _, N.zero => false 
  | N.succ n', N.succ m' => leb n' m' 

infix:60 " .<=. " => leb 

lemma leb_refl n : n .<=. n = true := by 
  sorry 


lemma leb_trans n : ∀ m p, n .<=. m → 
                           m .<=. p → 
                           n .<=. p := by
  sorry 

-- * Exercício 02: prove que ≤ é anti simétrica.

lemma leb_antisym n : ∀ m, n .<=. m → 
                           m .<=. n → 
                           n = m := by 
  sorry 

lemma le_plus_l : ∀ n m, n .<=. (n .+. m) := by
  sorry 

-- * Exercício 03: Prove o seguinte lema.

lemma plus_le_compat 
  : ∀ n m p, n .<=. m → 
             (n .+. p) .<=. (m .+. p) := by 
  sorry 


lemma involution_injective (f : N → N) 
  : (∀ n, n = (f (f n))) → 
    ∀ n1 n2, f n1 = f n2 → n1 = n2 := by
    intros H n1 n2 H1 
    rw [H n1]
    rw [H n2]
    rw [H1]

-- Exercícios: Números em binário
/-
Considere o tipo de dados seguinte que representa 
números em binário de forma que o bit mais significativo 
esteja mais a direita e não à esquerda, como usual. 
-/

inductive B where
| Z : B 
| B0 : B → B 
| B1 : B → B 
deriving Repr 

/-
A seguir, mostramos alguns exemplos de números naturais
e sua representação usando o tipo B 

Número natural  Valor do tipo B 
0               Z 
1               B1 Z 
2               B0 (B1 Z)
3               B1 (B1 Z)
4               B0 (B0 (B1 Z))
...
-/

/-
Desenvolva a função incr que incrementa de um 
um valor de tipo B. 
-/

def incr (b : B) : B := sorry 

/-
Desenvolva a função B2N que converte um valor de 
tipo B em um equivalente de tipo N.
-/

def B2N (b : B) : N := sorry 

/-
Desenvolva a função N2B que converte um valor de 
tipo N em um equivalente de tipo B. Dica: use a 
função incr. 
-/

def N2B (n : N) : B := sorry 

/-
Prove que a operação incr preserva a função 
B2N.
-/

lemma incr_preserves_b2n b : 
  B2N (incr b) = succ (B2N b) := sorry 

/-
Utilizando o lema anterior, prove que as funções 
B2N e N2B são inversas.
-/

theorem N2B2N n : B2N (N2B n) = n := sorry 
