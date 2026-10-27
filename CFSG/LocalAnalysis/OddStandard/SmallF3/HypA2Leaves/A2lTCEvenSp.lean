module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCOrder
public import CFSG.RankThree.PartOne.KF.U4Model

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial

theorem a2l_statedSp_tc (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K] {f r : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 1 ≤ r) (M : Subgroup (StatedSp r K))
    (hM : IsPComponent 2 M) (hS : TCSmall (M ⧸ Open.fusionZStar M)) : r = 2 ∧ f = 1 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (GL (Fin r ⊕ Fin r) K) := Finite.of_injective Units.val Units.val_injective
  have hSp := SymplecticFlag.card_statedSp (K := K) r
  rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
  · exfalso
    rcases (by omega : f = 1 ∨ 2 ≤ f) with rfl | hf2
    · have hcard : Nat.card (StatedSp 1 K) = 2 ^ 1 * 3 ^ 1 := by
        rw [hSp, hK]
        decide
      have : Fintype (StatedSp 1 K) := Fintype.ofFinite _
      have : Group.IsSolvable (StatedSp 1 K) :=
        Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])
      exact GrSLit.not_isPComponent_of_isSolvable M hM
    · obtain ⟨e₂⟩ := RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := K)
      have h4 : 4 ≤ 2 ^ f :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have hadm : StatedLieAdmissible .PSL 2 2 f := ⟨Nat.prime_two, hf, le_rfl,
        fun h => by rw [Prod.mk.injEq] at h; omega,
        fun h => by rw [Prod.mk.injEq] at h; omega⟩
      have hstated : StatedClassicalModel (StatedProj (StatedSL 2 K)) .PSL 2 2 f :=
        ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
      have := (LieType.Simplicity.fam_PSL_simplicity _ 2 2 f hstated).2
      have hXY := (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm.trans e₂
      have hm : Blueprint.LieModel (StatedProj (StatedSL 2 K)) .PSL 2 2 f :=
        Or.inl ⟨by decide, hstated⟩
      have : IsSimpleGroup (StatedSp 1 K) := hXY.isSimpleGroup
      have hMt : M = ⊤ := GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hM
      obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hM
        (((MulEquiv.subgroupCongr hMt).trans Subgroup.topEquiv).trans hXY)
      have hc := a2l_card_tcSmall (hS.of_mulEquiv eZ)
      exact absurd (a2l_lieModel_two_card hO hadm hm hc).2.1 (by decide)
  · by_cases h21 : r = 2 ∧ f = 1
    · exact h21
    · exfalso
      have hcond : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
          (Nat.card K = 2 ∧ 3 ≤ r) := by
        rcases (by omega : f = 1 ∨ 2 ≤ f) with rfl | hf2
        · exact Or.inr (Or.inr ⟨by rw [hK, pow_one], by omega⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hK]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r hr hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
          (X := StatedSp r K) hK hr ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 f := ⟨Nat.prime_two, hf, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact h21 ⟨rfl, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩⟩
      have hm : Blueprint.LieModel (StatedProj (StatedSp r K)) .PSp r 2 f :=
        Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
      have : IsSimpleGroup (StatedSp r K) := eProj.symm.isSimpleGroup
      have hMt : M = ⊤ := GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hM
      obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hM
        (((MulEquiv.subgroupCongr hMt).trans Subgroup.topEquiv).trans eProj.symm)
      have hc := a2l_card_tcSmall (hS.of_mulEquiv eZ)
      exact absurd (a2l_lieModel_two_card hO hadm hm hc).2.1 (by decide)

end CFSG.OddStandard.SmallF3.HypA2Leaves
