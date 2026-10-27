module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenBasic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Burnside
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Even

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial

theorem statedSp_five (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K] {f r : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 1 ≤ r) (M : Subgroup (StatedSp r K))
    (hM : IsPComponent 2 M)
    (hA : Nonempty (M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin 5))) : r = 1 ∧ f = 2 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (GL (Fin r ⊕ Fin r) K) := Finite.of_injective Units.val Units.val_injective
  have hSp := SymplecticFlag.card_statedSp (K := K) r
  rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
  · refine ⟨rfl, ?_⟩
    rcases (by omega : f = 1 ∨ 2 ≤ f) with rfl | hf2
    · exfalso
      have hcard : Nat.card (StatedSp 1 K) = 2 ^ 1 * 3 ^ 1 := by
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
      obtain ⟨e5⟩ := hA
      exact (lieModel_card_sixty_even hO hadm hm (card_alt_five (eZ.symm.trans e5))).2.2
  · exfalso
    by_cases h21 : r = 2 ∧ f = 1
    · obtain ⟨rfl, rfl⟩ := h21
      have := Fintype.ofFinite K
      have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
      obtain ⟨eS⟩ := RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (k := K)
        (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
      obtain ⟨eA⟩ := RankThree.CASymplecticSubfield.nonempty_commutator_mulEquiv_alternating eS
      obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv_of_derived (MulEquiv.refl _) eA hM
      obtain ⟨e5⟩ := hA
      have h5 := card_alt_five e5
      have h6 := card_alt_six eZ
      omega
    · have hcond : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
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
      obtain ⟨e5⟩ := hA
      have := (lieModel_card_sixty_even hO hadm hm (card_alt_five (eZ.symm.trans e5))).1
      exact absurd this (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat.Even
