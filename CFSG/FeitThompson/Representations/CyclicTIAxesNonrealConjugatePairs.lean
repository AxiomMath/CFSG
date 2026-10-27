module

public import CFSG.FeitThompson.Representations.TIRectangleCoefficientExchange
public import CFSG.FeitThompson.Representations.CyclicTIIsometryConjugation
import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.DegreeZeroIsometryDisjointConjPairs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {X : Type*} [Group X]

def starIrr [Finite X] (χ : Irr X) : Irr X := ⟨star (χ : X → ℂ), star_mem_Irr χ.2⟩

@[simp]
theorem coe_starIrr [Finite X] (χ : Irr X) :
    ((starIrr χ : Irr X) : X → ℂ) = star (χ : X → ℂ) := (rfl)

theorem coe_starIrr_eq [Finite X] (χ : Irr X) :
    ((starIrr χ : Irr X) : X → ℂ) = fun x => conj ((χ : X → ℂ) x) := (rfl)

@[simp]
theorem starIrr_starIrr [Finite X] (χ : Irr X) : starIrr (starIrr χ) = χ :=
  Subtype.ext (by simp)

@[simp]
theorem starIrr_principalIrr [Finite X] : starIrr (principalIrr X) = principalIrr X :=
  Subtype.ext (by simp)

theorem coe_ne_one_of_ne_principalIrr {χ : Irr X} (hχ : χ ≠ principalIrr X) :
    (χ : X → ℂ) ≠ 1 := fun h => hχ (Subtype.ext (by rw [h, coe_principalIrr]))

theorem starIrr_ne_self [Finite X] (hodd : Odd (Nat.card X)) {χ : Irr X}
    (hχ : χ ≠ principalIrr X) : starIrr χ ≠ χ := by
  intro he
  refine ne_conj_of_mem_Irr_of_ne_one_of_odd hodd χ.2 (coe_ne_one_of_ne_principalIrr hχ) ?_
  have h := congrArg (fun c : Irr X => (c : X → ℂ)) he
  simp only [coe_starIrr] at h
  exact h.symm

theorem starIrr_ne_principalIrr [Finite X] {χ : Irr X} (hχ : χ ≠ principalIrr X) :
    starIrr χ ≠ principalIrr X := fun he => hχ (by simpa using congrArg starIrr he)

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G}

namespace IsCyclicTIPair

theorem star_prodChar (hW : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) :
    star (hW.prodChar lam mu) = hW.prodChar (star lam) (star mu) := by
  funext z
  simp [prodChar_apply, star_mul']

theorem starₗ_basisProdIrr (hW : IsCyclicTIPair W W1 W2) {i k : Irr ↥W1} {j l : Irr ↥W2}
    (hik : (k : ↥W1 → ℂ) = star (i : ↥W1 → ℂ)) (hjl : (l : ↥W2 → ℂ) = star (j : ↥W2 → ℂ)) :
    classFun.starₗ ↥W (hW.basisProdIrr (i, j)) = hW.basisProdIrr (k, l) := by
  refine Subtype.ext ?_
  rw [classFun.coe_starₗ, coe_basisProdIrr_apply, coe_basisProdIrr_apply, hW.star_prodChar,
    hik, hjl]

theorem odd_card_Irr_left (hW : IsCyclicTIPair W W1 W2) : Odd (Nat.card (Irr ↥W1)) := by
  rw [hW.card_Irr_left]; exact hW.odd_natCard_left

theorem odd_card_Irr_right (hW : IsCyclicTIPair W W1 W2) : Odd (Nat.card (Irr ↥W2)) := by
  rw [hW.card_Irr_right]; exact hW.odd_natCard_right

theorem three_le_card_Irr_left (hW : IsCyclicTIPair W W1 W2) : 3 ≤ Nat.card (Irr ↥W1) := by
  rw [hW.card_Irr_left]; exact hW.three_le_natCard_left

theorem three_le_card_Irr_right (hW : IsCyclicTIPair W W1 W2) : 3 ≤ Nat.card (Irr ↥W2) := by
  rw [hW.card_Irr_right]; exact hW.three_le_natCard_right

theorem exists_conj_index_left (hW : IsCyclicTIPair W W1 W2) {i : Irr ↥W1}
    (hi : i ≠ principalIrr ↥W1) :
    ∃ k : Irr ↥W1, (k : ↥W1 → ℂ) = (fun x => conj ((i : ↥W1 → ℂ) x)) ∧
      k ≠ i ∧ k ≠ principalIrr ↥W1 := by
  have := hW.finite_left
  exact ⟨starIrr i, coe_starIrr_eq i, starIrr_ne_self hW.odd_natCard_left hi,
    starIrr_ne_principalIrr hi⟩

theorem exists_conj_index_right (hW : IsCyclicTIPair W W1 W2) {j : Irr ↥W2}
    (hj : j ≠ principalIrr ↥W2) :
    ∃ l : Irr ↥W2, (l : ↥W2 → ℂ) = (fun y => conj ((j : ↥W2 → ℂ) y)) ∧
      l ≠ j ∧ l ≠ principalIrr ↥W2 := by
  have := hW.finite_right
  exact ⟨starIrr j, coe_starIrr_eq j, starIrr_ne_self hW.odd_natCard_right hj,
    starIrr_ne_principalIrr hj⟩

variable [Fintype G] [Fintype ↥W] {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem star_prodCharEta (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    {i k : Irr ↥W1} {j l : Irr ↥W2}
    (hik : (k : ↥W1 → ℂ) = star (i : ↥W1 → ℂ)) (hjl : (l : ↥W2 → ℂ) = star (j : ↥W2 → ℂ)) :
    star (hW.prodCharEta σ i j) = hW.prodCharEta σ k l := by
  rw [prodCharEta_eq_coe_apply, prodCharEta_eq_coe_apply, ← hW.starₗ_basisProdIrr hik hjl,
    hσ.map_starₗ hW, classFun.coe_starₗ]

open scoped Classical in
theorem cfInner_prodCharEta_row (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i i' : Irr ↥W1) :
    cfInner (hW.prodCharEta σ i (principalIrr ↥W2))
      (hW.prodCharEta σ i' (principalIrr ↥W2)) = if i = i' then 1 else 0 := by
  rw [hW.cfInner_prodCharEta hσ]
  simp

open scoped Classical in
theorem cfInner_prodCharEta_col (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (j j' : Irr ↥W2) :
    cfInner (hW.prodCharEta σ (principalIrr ↥W1) j)
      (hW.prodCharEta σ (principalIrr ↥W1) j') = if j = j' then 1 else 0 := by
  rw [hW.cfInner_prodCharEta hσ]
  simp

theorem conj_prodCharEta_row (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {i k : Irr ↥W1}
    (hik : (k : ↥W1 → ℂ) = fun x => conj ((i : ↥W1 → ℂ) x)) :
    (fun g => conj (hW.prodCharEta σ i (principalIrr ↥W2) g))
      = hW.prodCharEta σ k (principalIrr ↥W2) :=
  hW.star_prodCharEta hσ hik (by simp)

theorem conj_prodCharEta_col (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {j l : Irr ↥W2}
    (hjl : (l : ↥W2 → ℂ) = fun y => conj ((j : ↥W2 → ℂ) y)) :
    (fun g => conj (hW.prodCharEta σ (principalIrr ↥W1) j g))
      = hW.prodCharEta σ (principalIrr ↥W1) l :=
  hW.star_prodCharEta hσ (by simp) hjl

theorem conj_prodCharEta_row_ne (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {i : Irr ↥W1} (hi : i ≠ principalIrr ↥W1) :
    (fun g => conj (hW.prodCharEta σ i (principalIrr ↥W2) g))
      ≠ hW.prodCharEta σ i (principalIrr ↥W2) := by
  have := hW.finite_left
  intro he
  rw [hW.conj_prodCharEta_row hσ (k := starIrr i) (coe_starIrr_eq i)] at he
  have h1 := hW.cfInner_prodCharEta_row hσ (starIrr i) i
  rw [he, if_neg (starIrr_ne_self hW.odd_natCard_left hi), hW.cfInner_prodCharEta_row hσ,
    if_pos rfl] at h1
  exact one_ne_zero h1

theorem conj_prodCharEta_col_ne (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {j : Irr ↥W2} (hj : j ≠ principalIrr ↥W2) :
    (fun g => conj (hW.prodCharEta σ (principalIrr ↥W1) j g))
      ≠ hW.prodCharEta σ (principalIrr ↥W1) j := by
  have := hW.finite_right
  intro he
  rw [hW.conj_prodCharEta_col hσ (l := starIrr j) (coe_starIrr_eq j)] at he
  have h1 := hW.cfInner_prodCharEta_col hσ (starIrr j) j
  rw [he, if_neg (starIrr_ne_self hW.odd_natCard_right hj), hW.cfInner_prodCharEta_col hσ,
    if_pos rfl] at h1
  exact one_ne_zero h1

end IsCyclicTIPair

end CFSG.FeitThompson

end
