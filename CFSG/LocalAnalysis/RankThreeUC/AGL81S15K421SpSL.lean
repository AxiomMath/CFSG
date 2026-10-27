module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpSLProof

theorem isSimpleGroup_sl2_charTwo_aux1 {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨r, hr, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    rcases sq_eq_one_iff.1 hr with h | h
    · exact h
    · rw [h]
      exact CharTwo.neg_eq 1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, ← hs, hr1, map_one]

theorem isSimpleGroup_sl2_charTwo_aux2 {F : Type} [Field F] [CharP F 2]
    (hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  haveI := hsimple
  have hcenter := isSimpleGroup_sl2_charTwo_aux1 (F := F)
  let π : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) g).1 hg
    rw [hcenter, Subgroup.mem_bot] at hmem
    exact hmem
  exact (MulEquiv.ofBijective π ⟨hinj, QuotientGroup.mk'_surjective _⟩).isSimpleGroup

theorem isSimpleGroup_sl2_charTwo {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have : Fintype F := Fintype.ofFinite F
  have hs4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) le_rfl (Or.inr hs4)
  exact isSimpleGroup_sl2_charTwo_aux2 hsimple

theorem sl2_dvd_card_of_dvd_succ {F : Type} [Field F] [Finite F] {p : ℕ}
    (hpF : p ∣ Nat.card F + 1) :
    p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
  have hsq : ∀ Q : ℕ, Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    intro Q
    rcases Nat.eq_zero_or_pos Q with h | h
    · subst h
      norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, Q = m + 1 := ⟨Q - 1, by omega⟩
      have h2 : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
      rw [h2, Nat.add_sub_cancel, Nat.add_sub_cancel]
  rw [hsq]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpF _) _

theorem sl2_card_ne_of_dvd_succ {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F + 1) (h4 : 4 ≤ Nat.card F) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ≠ p := by
  intro h
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F] at h
  have hle : p ≤ Nat.card F + 1 := Nat.le_of_dvd (by omega) hpF
  have hQ2 : 4 * Nat.card F ≤ Nat.card F ^ 2 := by nlinarith
  have h3 : 3 * Nat.card F ≤ Nat.card F ^ 2 - 1 := by omega
  have h5 : Nat.card F * (3 * Nat.card F) ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
    Nat.mul_le_mul le_rfl h3
  nlinarith

end K421SpSLProof

end CFSG.LocalAnalysis.RankThreeUC.S15
