module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open

inductive Letter : Type
  | g
  | gi
  | y
  deriving DecidableEq

@[expose] def Letter.eval {M : Type*} [Group M] (g y : M) : Letter → M
  | .g => g
  | .gi => g⁻¹
  | .y => y

@[expose] def wordEval {M : Type*} [Group M] (g y : M) (w : List Letter) : M :=
  (w.map (Letter.eval g y)).prod

@[expose] def yCount (w : List Letter) : ℕ :=
  w.count .y

@[expose] def stabStep {m : ℕ} (ψ zmul : Fin 8 → Fin 8) (σ : Fin m → Fin 8 → Fin 8) :
    Option (Fin m) → Fin 8 × Bool → Fin 8 × Bool
  | none, (e, ε) => (if ε then zmul (ψ e) else ψ e, ε)
  | some j, (e, ε) => (σ j e, ε)

@[expose] def stabRun {m : ℕ} (ψ zmul : Fin 8 → Fin 8) (σ : Fin m → Fin 8 → Fin 8)
    (word : List (Option (Fin m))) (s : Fin 8 × Bool) : Fin 8 × Bool :=
  word.foldr (stabStep ψ zmul σ) s

structure InnerData {G : Type*} [Group G] (L : Subgroup G) (z : G) where
  g₁ : G
  a : G
  g₁_mem : g₁ ∈ L ⊓ centralizer ({z} : Set G)
  a_mem : a ∈ L ⊓ centralizer ({z} : Set G)
  orderOf_g₁ : orderOf g₁ = 5
  order_five : ∀ x ∈ L ⊓ centralizer ({z} : Set G), orderOf x = 5 →
    ∃ c ∈ L ⊓ centralizer ({z} : Set G), c * x * c⁻¹ = g₁
  h : G
  h_mem : h ∈ L ⊓ centralizer ({z} : Set G)
  h_comm : h * g₁ = g₁ * h
  ys : Fin 4 → G
  ys_mem : ∀ i, ys i ∈ L ⊓ centralizer ({z} : Set G)
  filter : ∀ y ∈ L ⊓ centralizer ({z} : Set G),
    (∀ w : List Letter, wordEval g₁ y w = 1 ↔ wordEval g₁ a w = 1) →
      ∃ (k : ℕ) (i : Fin 4), h ^ k * y * (h ^ k)⁻¹ = ys i
  a_conj : ∃ k ∈ L, k * z * k⁻¹ = a
  eW : Fin 4 → List Letter
  E_elemAbelian : IsElemAbelian 2 (closure (Set.range fun j => wordEval g₁ a (eW j)))
  E_card : Nat.card (closure (Set.range fun j => wordEval g₁ a (eW j))) = 16
  z_mem_E : z ∈ closure (Set.range fun j => wordEval g₁ a (eW j))
  E_conj : ∀ e ∈ closure (Set.range fun j => wordEval g₁ a (eW j)), e ≠ 1 →
    ∃ k ∈ L, k * z * k⁻¹ = e
  pres : ∀ i : Fin 4, i.val < 2 → (∃ k ∈ L, k * z * k⁻¹ = ys i) ∧
    ∃ c ∈ L ⊓ centralizer ({z} : Set G), ∀ j, c * wordEval g₁ (ys i) (eW j) * c⁻¹ ∈
      closure (Set.range fun j => wordEval g₁ a (eW j))
  wb : List Letter
  wb_odd : Odd (yCount wb)
  invol : ∀ x ∈ L, x ≠ 1 → x * x = 1 →
    (∃ k ∈ L, k * z * k⁻¹ = x) ∨ ∃ k ∈ L, k * wordEval g₁ a wb * k⁻¹ = x
  not_conj : ∀ k ∈ L, k * z * k⁻¹ ≠ wordEval g₁ a wb
  u : G
  u_mem : u ∈ L
  u_comm : u * wordEval g₁ a wb = wordEval g₁ a wb * u
  u_sq : u * u = 1
  u_ne_one : u ≠ 1
  u_ne_b : u ≠ wordEval g₁ a wb
  u_conj : ∃ k ∈ L, k * wordEval g₁ a wb * k⁻¹ = u
  ub_conj : ∃ k ∈ L, k * wordEval g₁ a wb * k⁻¹ = u * wordEval g₁ a wb
  swap_ys : ∀ i : Fin 4, 2 ≤ i.val → ∃ k ∈ L, k * wordEval g₁ a wb * k⁻¹ = ys i
  swap_b : ∀ i : Fin 4, 2 ≤ i.val → ∃ k ∈ L, k * z * k⁻¹ = wordEval g₁ (ys i) wb
  yW : Fin 8 → List Letter
  zmul : Fin 8 → Fin 8
  zmul_spec : ∀ e, wordEval g₁ a (yW e) * z = wordEval g₁ a (yW (zmul e))
  eOne : Fin 8
  eOne_spec : wordEval g₁ a (yW eOne) = 1
  eA : Fin 8
  eA_spec : wordEval g₁ a (yW eA) = a
  stab : ∀ i : Fin 4, 2 ≤ i.val → ∃ (c : G) (ψ : Fin 8 → Fin 8) (m : ℕ) (gs : Fin m → G)
      (σ : Fin m → Fin 8 → Fin 8) (word : List (Option (Fin m))) (x : Fin 8),
    c ∈ L ⊓ centralizer ({z} : Set G) ∧
    (∀ e, c * wordEval g₁ (ys i) (yW e) * c⁻¹ = wordEval g₁ a (yW (ψ e))) ∧
    (∀ j, gs j ∈ L ∧ ∀ e, gs j * wordEval g₁ a (yW e) * (gs j)⁻¹ = wordEval g₁ a (yW (σ j e))) ∧
    stabRun ψ zmul σ word (eOne, true) = (eOne, true) ∧
    stabRun ψ zmul σ word (eA, false) = (x, false) ∧
    ∃ k ∈ L, k * wordEval g₁ a wb * k⁻¹ = wordEval g₁ a (yW x)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
