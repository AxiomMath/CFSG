module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.Words
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.Quad

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph


@[expose] def dW : List ℕ := [12, 17, 13, 18, 15, 20]

@[expose] def y0W : List ℕ := [2, 8]

@[expose] def qW : List ℕ := [3, 5, 15, 0, 7]

@[expose] def rW : List ℕ := qW ++ dW ++ qW.reverse

@[expose] def gpW (w : List ℕ) : List ℕ := y0W ++ w.map rhoIdx ++ y0W.reverse

@[expose] def FixB (w : List ℕ) : Prop := wordN (gpW w) = wordN w

@[expose] def CentB (x w : List ℕ) : Prop := wordN (x ++ w ++ x.reverse) = wordN w

@[expose] def ConjB (x w : List ℕ) : Prop := wordN (x ++ gpW w ++ x.reverse) = wordN w

@[expose] def ConjInvB (x w : List ℕ) : Prop := wordN (x.reverse ++ gpW w ++ x) = wordN w

instance (w : List ℕ) : Decidable (FixB w) := by unfold FixB; infer_instance
instance (x w : List ℕ) : Decidable (CentB x w) := by unfold CentB; infer_instance
instance (x w : List ℕ) : Decidable (ConjB x w) := by unfold ConjB; infer_instance
instance (x w : List ℕ) : Decidable (ConjInvB x w) := by unfold ConjInvB; infer_instance

variable {K : Type} [Field K] [Finite K]

@[expose] def Letters (w : List ℕ) : Prop := w.all (· < 24) = true

instance (w : List ℕ) : Decidable (Letters w) := by unfold Letters; infer_instance

theorem letters_append {v w : List ℕ} (hv : Letters v) (hw : Letters w) : Letters (v ++ w) := by
  unfold Letters at *
  rw [List.all_append, hv, hw]
  rfl

theorem letters_reverse {w : List ℕ} (hw : Letters w) : Letters w.reverse := by
  unfold Letters at *
  rw [List.all_reverse, hw]

theorem letters_map_rhoIdx {w : List ℕ} (hw : Letters w) : Letters (w.map rhoIdx) := by
  unfold Letters at *
  rw [List.all_eq_true] at hw ⊢
  intro a ha
  have := rhoIdx_lt (rt_lt_of_mem (by rw [List.all_eq_true]; exact hw)) a ha
  simpa using this

theorem letters_gpW {w : List ℕ} (hw : Letters w) : Letters (gpW w) :=
  letters_append (letters_append rfl (letters_map_rhoIdx hw)) rfl

theorem gammaP_wordG (hK : Nat.card K = 2) {w : List ℕ} (hw : Letters w) :
    gammaP K (uSL 1 * vSL 1) (wordG K w) = wordG K (gpW w) :=
  gammaP_uv_wordG (two_eq_zero_of_card_two' hK) (rt_lt_of_mem hw)

theorem mem_fix_of_wordN (hK : Nat.card K = 2) {w : List ℕ} (hw : Letters w) (h : FixB w) :
    wordG K w ∈ fixedSubgroup (gammaP K (uSL 1 * vSL 1)) := by
  rw [mem_fixedSubgroup, gammaP_wordG hK hw]
  exact wordG_eq (two_eq_zero_of_card_two' hK) (letters_gpW hw) hw h

theorem mem_centralizer_of_wordN (hK : Nat.card K = 2) {x w : List ℕ} (hx : Letters x)
    (hw : Letters w) (h : CentB x w) :
    wordG K w ∈ Subgroup.centralizer ({wordG K x} : Set ↥(adjointGroup Tag.D4 K)) := by
  have h2 := two_eq_zero_of_card_two' hK
  rw [mem_centralizer_iff_conj, MulAut.conj_apply, conj_wordG h2]
  exact wordG_eq h2 (letters_append (letters_append hx hw) (letters_reverse hx)) hw h

theorem mem_fix_conj_of_wordN (hK : Nat.card K = 2) {x w : List ℕ} (hx : Letters x)
    (hw : Letters w) (h : ConjB x w) :
    wordG K w ∈ fixedSubgroup (MulAut.conj (wordG K x) * gammaP K (uSL 1 * vSL 1)) := by
  have h2 := two_eq_zero_of_card_two' hK
  rw [mem_fixedSubgroup, MulAut.mul_apply, gammaP_wordG hK hw, MulAut.conj_apply, conj_wordG h2]
  exact wordG_eq h2 (letters_append (letters_append hx (letters_gpW hw)) (letters_reverse hx))
    hw h

theorem mem_fix_conj_inv_of_wordN (hK : Nat.card K = 2) {x w : List ℕ} (hx : Letters x)
    (hw : Letters w) (h : ConjInvB x w) :
    wordG K w ∈ fixedSubgroup ((MulAut.conj (wordG K x))⁻¹ * gammaP K (uSL 1 * vSL 1)) := by
  have h2 := two_eq_zero_of_card_two' hK
  rw [mem_fixedSubgroup, MulAut.mul_apply, gammaP_wordG hK hw, ← map_inv, wordG_inv h2,
    MulAut.conj_apply, conj_wordG h2, List.reverse_reverse]
  exact wordG_eq h2 (letters_append (letters_append (letters_reverse hx) (letters_gpW hw)) hx)
    hw h

theorem d_mem (hK : Nat.card K = 2) : wordG K dW ∈ fixedSubgroup (gammaP K (uSL 1 * vSL 1)) :=
  mem_fix_of_wordN hK (by decide) (by decide +kernel)

theorem y₀_mem (hK : Nat.card K = 2) : wordG K y0W ∈ fixedSubgroup (gammaP K (uSL 1 * vSL 1)) :=
  mem_fix_of_wordN hK (by decide) (by decide +kernel)

theorem q_mem (hK : Nat.card K = 2) : wordG K qW ∈ fixedSubgroup (gammaP K (uSL 1 * vSL 1)) :=
  mem_fix_of_wordN hK (by decide) (by decide +kernel)

theorem r_eq (hK : Nat.card K = 2) : wordG K rW = wordG K qW * wordG K dW * (wordG K qW)⁻¹ := by
  rw [conj_wordG (two_eq_zero_of_card_two' hK)]
  rfl

theorem r_mem (hK : Nat.card K = 2) : wordG K rW ∈ fixedSubgroup (gammaP K (uSL 1 * vSL 1)) := by
  rw [r_eq hK]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (q_mem hK) (d_mem hK))
    (Subgroup.inv_mem _ (q_mem hK))

theorem y₀_eq : wordG K y0W = sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1) :=
  sl2At_uv_eq_wordG.2.2.1.symm

theorem d_pow_three (hK : Nat.card K = 2) : wordG K dW ^ 3 = 1 := by
  rw [pow_succ, pow_two, ← wordG_append, ← wordG_append, ← wordG_nil]
  exact wordG_eq (two_eq_zero_of_card_two' hK) (by decide) (by decide) (by decide +kernel)

theorem y₀_pow_three (hK : Nat.card K = 2) : wordG K y0W ^ 3 = 1 := by
  rw [pow_succ, pow_two, ← wordG_append, ← wordG_append, ← wordG_nil]
  exact wordG_eq (two_eq_zero_of_card_two' hK) (by decide) (by decide) (by decide +kernel)

theorem r_pow_three (hK : Nat.card K = 2) : wordG K rW ^ 3 = 1 := by
  rw [r_eq hK, conj_pow, d_pow_three hK]
  group

theorem d_comm_r (hK : Nat.card K = 2) : wordG K dW * wordG K rW = wordG K rW * wordG K dW := by
  rw [← wordG_append, ← wordG_append]
  exact wordG_eq (two_eq_zero_of_card_two' hK) (by decide) (by decide) (by decide +kernel)

theorem d_comm_y₀ (hK : Nat.card K = 2) :
    wordG K dW * wordG K y0W = wordG K y0W * wordG K dW := by
  rw [← wordG_append, ← wordG_append]
  exact wordG_eq (two_eq_zero_of_card_two' hK) (by decide) (by decide) (by decide +kernel)

theorem y₀_conj_r (hK : Nat.card K = 2) :
    wordG K y0W * wordG K rW * (wordG K y0W)⁻¹ = wordG K rW * wordG K dW := by
  rw [conj_wordG (two_eq_zero_of_card_two' hK), ← wordG_append]
  exact wordG_eq (two_eq_zero_of_card_two' hK) (by decide) (by decide) (by decide +kernel)

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
