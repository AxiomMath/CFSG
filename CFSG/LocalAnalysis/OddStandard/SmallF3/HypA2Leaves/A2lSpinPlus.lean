module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpinIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowOmegaE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpinBlock

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CliffordAlgebra CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Steinberg
open scoped MatrixGroups

section General

theorem a2l_sl2_center_cases {E : Type} [Field E] {w : SL(2, E)} (hw : w ∈ center SL(2, E)) :
    w = 1 ∨ w = a2lNegOne E := by
  obtain ⟨r, hr, hrw⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hw
  rw [Fintype.card_fin] at hr
  have hr2 : r * r = 1 := by rw [← pow_two]; exact hr
  rcases mul_self_eq_one_iff.1 hr2 with h | h
  · left
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_one, ← hrw, h, map_one]
  · right
    refine Subtype.ext ?_
    change (w : Matrix (Fin 2) (Fin 2) E) = -1
    rw [← hrw, h, map_neg, map_one]

theorem a2l_injective_comp_of_ker_le_center {E M K : Type} [Field E] [Group M] [Group K]
    (ψ : SL(2, E) →* M) (hψ : Function.Injective ψ) (α : M →* K) (hle : α.ker ≤ center M)
    (hα : α (ψ (a2lNegOne E)) ≠ 1) : Function.Injective (α.comp ψ) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hmem : ψ w ∈ center M := hle (MonoidHom.mem_ker.2 hw)
  have hwc : w ∈ center SL(2, E) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hψ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hmem (ψ g)
  rcases a2l_sl2_center_cases hwc with h | h
  · exact h
  · exfalso
    apply hα
    rw [h] at hw
    exact hw

@[expose] noncomputable def a2lEquivOfKerEq {M K P : Type} [Group M] [Group K] [Group P]
    (α : M →* K) (β : M →* P) (hα : Function.Surjective α) (hβ : Function.Surjective β)
    (h : α.ker = β.ker) : K ≃* P :=
  (QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβ))

end General

section Plus

variable (F : Type) [Field F]

theorem a2l_finite_spinPlus [Finite F] (n : ℕ) [NeZero n] : Finite (spinGroup (quadPlus n F)) :=
  finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus

theorem a2l_card_center_spinPlus_le_four [Finite F] :
    Nat.card (center (spinGroup (quadPlus 4 F))) ≤ 4 := by
  haveI := a2l_finite_spinPlus F 4
  obtain ⟨-, hcomap, hcen⟩ := spinToStatedProj_quadPlus (n := 4) (K := F) (by norm_num)
  rw [← hcen, hcomap]
  exact card_comap_statedScalars_le_four (coe_quadPlus 4 F)
    (exists_map_ne_zero_of_hypPair _ (plusPair F (⟨0, by omega⟩ : Fin 4)))
    (range_spinMatrix_quadPlus (by norm_num)) coe_ker_spinMatrix_quadPlus

@[expose] noncomputable def a2lSpinToElementary {n : ℕ} (hn : 3 ≤ n) :
    spinGroup (quadPlus n F) →* ↥(elementaryGroup (quadPlus n F)) :=
  (spinAction (quadPlus n F)).codRestrict _ fun x => by
    rw [← range_spinAction_quadPlus hn]
    exact ⟨x, rfl⟩

theorem a2lSpinToElementary_surjective {n : ℕ} (hn : 3 ≤ n) :
    Function.Surjective (a2lSpinToElementary F hn) := by
  intro y
  obtain ⟨x, hx⟩ : y.1 ∈ (spinAction (quadPlus n F)).range := by
    rw [range_spinAction_quadPlus hn]
    exact y.2
  exact ⟨x, Subtype.ext hx⟩

theorem ker_a2lSpinToElementary {n : ℕ} (hn : 3 ≤ n) :
    (a2lSpinToElementary F hn).ker = (spinMatrix (quadPlus n F)).ker := by
  rw [ker_spinMatrix]
  exact MonoidHom.ker_codRestrict _ _ _

theorem a2l_nonempty_equiv_elementary [Finite F] {K : Type} [Group K]
    (α : spinGroup (quadPlus 4 F) →* K) (hα : Function.Surjective α)
    (hle : (spinMatrix (quadPlus 4 F)).ker ≤ α.ker) (hcard : Nat.card α.ker ≤ 2)
    (hne : (spinMatrix (quadPlus 4 F)).ker ≠ ⊥) :
    Nonempty (K ≃* ↥(elementaryGroup (quadPlus 4 F))) := by
  haveI := a2l_finite_spinPlus F 4
  have h2 : 2 ≤ Nat.card (spinMatrix (quadPlus 4 F)).ker := by
    have := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    omega
  have hker : (spinMatrix (quadPlus 4 F)).ker = α.ker :=
    Subgroup.eq_of_le_of_card_ge hle (hcard.trans h2)
  exact ⟨a2lEquivOfKerEq α (a2lSpinToElementary F (n := 4) (by norm_num)) hα
    (a2lSpinToElementary_surjective F (n := 4) (by norm_num))
    (hker.symm.trans (ker_a2lSpinToElementary F (n := 4) (by norm_num)).symm)⟩

end Plus

section Embeddings

theorem a2l_exists_spinPlus_sl2
    {F : Type} [Field F] [Fintype F] (hF3 : Fintype.card F = 3) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E) (ψ : SL(2, E) →* spinGroup (quadPlus 4 F)),
      Fintype.card E = 9 ∧ Function.Injective ψ ∧
        ((ψ (a2lNegOne E) : spinGroup (quadPlus 4 F)) : CliffordAlgebra (quadPlus 4 F)) = -1 := by
  have hk : ringChar F ≠ 2 := a2l_ringChar_ne_two (by rw [hF3]; decide)
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hk
  have hirr := a2l_irr_zero_one hF3 h2F
  obtain ⟨E, _, _, Θ, hEc, hΘinj, hΘneg⟩ :=
    a2l_exists_spinMinus_sl2 hirr h2F 3 (⟨1, by decide⟩ : Fin (3 - 1))
  have h3 : Nat.card F = 3 := by rw [Nat.card_eq_fintype_card, hF3]
  refine ⟨E, inferInstance, inferInstance, (a2lMinusToPlus F).spinGroupMap.comp Θ, ?_,
    (a2l_spinGroupMap_minusToPlus_injective F h2F hirr).comp hΘinj,
    a2l_coe_spinGroupMap_eq_neg_one _ hΘneg⟩
  rw [hEc, h3] <;> norm_num

theorem a2l_exists_sl2_elementary_plus {F : Type} [Field F] [Fintype F]
    (hF3 : Fintype.card F = 3) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E)
      (φ : SL(2, E) →* ↥(elementaryGroup (quadPlus 4 F))),
      Fintype.card E = 9 ∧ Function.Injective φ ∧
        φ (a2lNegOne E) ∈ center ↥(elementaryGroup (quadPlus 4 F)) := by
  haveI := Fintype.ofFinite (GaloisField 3 2)
  have hF9 : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, CFSG.RankThree.PartTwo.Census.card_galoisField_three_two]
  refine ⟨GaloisField 3 2, inferInstance, inferInstance,
    (a2lNineLevi hF3).codRestrict _ (a2lNineLevi_mem_elementary hF3), hF9, ?_, ?_⟩
  · intro a b h
    exact a2lNineLevi_injective hF3 (congrArg Subtype.val h)
  · rw [Subgroup.mem_center_iff]
    intro g
    refine Subtype.ext ?_
    change (g : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) *
        a2lNineLevi hF3 (a2lNegOne (GaloisField 3 2)) =
      a2lNineLevi hF3 (a2lNegOne (GaloisField 3 2)) *
        (g : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F))
    rw [a2lNineLevi_negOne hF3]
    exact (a2l_neg_mul_comm _).symm

end Embeddings

end CFSG.OddStandard.SmallF3.HypA2Leaves
