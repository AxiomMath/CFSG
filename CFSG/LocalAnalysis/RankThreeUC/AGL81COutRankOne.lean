module

public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K7145Comp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenOneThreeRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Main

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81COutRankOne

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree

noncomputable abbrev Out (C : Type*) [Group C] : Type _ :=
  MulAut C ⧸ (MulAut.conj : C →* MulAut C).range

theorem outer_comm_of_outCommInner {X : Type*} [Group X] (h : OutCommInner X) :
    ∀ a b : Outer X, a * b = b * a := by
  intro a b
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner X) a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective (inner X) b
  have h1 : QuotientGroup.mk' (inner X) (α * β * α⁻¹ * β⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (α * β * α⁻¹ * β⁻¹)).mpr (h α β)
  rw [← map_mul, ← map_mul]
  rw [show α * β = (α * β * α⁻¹ * β⁻¹) * (β * α) by group, map_mul, h1, one_mul]

theorem sylow_normal_of_outCommInner {X : Type*} [Group X] (h : OutCommInner X) {p : ℕ}
    (S : Sylow p (Outer X)) : (S : Subgroup (Outer X)).Normal :=
  sylow_normal_of_comm (fun a b => outer_comm_of_outCommInner h a b) S

@[expose] def SimpleOutCommInnerRankOne : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup S → CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1 →
      OutCommInner S

theorem sylow_normal_out_of_pRank3_le_one_of_simple
    (hSimple : SimpleOutCommInnerRankOne)
    {C : Type} [Group C] [Finite C] (hQ : CFSG.Open.IsQuasisimple C)
    (hK : CFSG.Open.IsKGroup C) {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup C) ≤ 1) :
    ∀ S : Sylow p (Out C), (S : Subgroup (Out C)).Normal := by
  haveI : Group.IsPerfect C := Group.isPerfect_def.mpr hQ.1
  have hsimple : IsSimpleGroup (C ⧸ Subgroup.center C) := hQ.2
  let Q := C ⧸ Subgroup.center C
  haveI : IsSimpleGroup Q := hsimple
  have hnab : ∃ a b : Q, a * b ≠ b * a :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.quotient_center_nonabelian hQ
  let φ : ↥(⊤ : Subgroup C) →* Q :=
    (QuotientGroup.mk' (Subgroup.center C)).comp (⊤ : Subgroup C).subtype
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center C) y
    exact ⟨⟨c, Subgroup.mem_top c⟩, rfl⟩
  have hcat : CFSG.Open.IsCatalogGroup Q := hK.isCatalogGroup_of_surjective ⊤ hnab φ hφ
  have h3C : CFSG.pRank 3 C ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact h3
  have h3Q : CFSG.Open.pRank 3 (⊤ : Subgroup Q) ≤ 1 := by
    have h := CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      (p := 3) Nat.prime_three (by norm_num) h3C
      (QuotientGroup.mk' (Subgroup.center C)) (QuotientGroup.mk'_surjective _)
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  have hcomm : OutCommInner Q := hSimple Q hsimple hnab hcat h3Q
  have hOutQ : ∀ S : Sylow p (Outer Q), (S : Subgroup (Outer Q)).Normal :=
    fun S => sylow_normal_of_outCommInner hcomm S
  exact CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo.sylow_normal_of_injective
    (centerQuotient_outer_injective C) hOutQ

section Certified

theorem simpleOutCommInnerRankOne_holds : SimpleOutCommInnerRankOne :=
  fun S _ _ hsimple hnab hcat hr => outCommInner_of_catalog hsimple hnab hcat hr

end Certified

end CFSG.LocalAnalysis.RankThreeUC.AGL81COutRankOne
