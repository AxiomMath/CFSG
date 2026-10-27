module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsGMBound

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34GM

section Center

variable (X : Type*) [Group X] [Finite X]

theorem not_two_dvd_card_ker_mk : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 X)).ker := by
  rw [QuotientGroup.ker_mk']
  exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card

theorem fusionZStar_eq_comap :
    Open.fusionZStar X = (center (X ⧸ pPrimeCore 2 X)).comap (QuotientGroup.mk' _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← HarrisLit.fusionZStar_eq_center_of_pPrimeCore_eq_bot
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)]
  exact (GSThmB.OddQuot.comap_fusionZStar_of_surjective _ (QuotientGroup.mk'_surjective _)
    (not_two_dvd_card_ker_mk X)).symm

theorem mem_fusionZStar_iff (x : X) :
    x ∈ Open.fusionZStar X ↔
      QuotientGroup.mk' (pPrimeCore 2 X) x ∈ center (X ⧸ pPrimeCore 2 X) := by
  rw [fusionZStar_eq_comap X]
  exact Iff.rfl

noncomputable def centerMap : ↥(Open.fusionZStar X) →* ↥(center (X ⧸ pPrimeCore 2 X)) :=
  ((QuotientGroup.mk' (pPrimeCore 2 X)).comp (Open.fusionZStar X).subtype).codRestrict _
    fun u => (mem_fusionZStar_iff X u).mp u.2

theorem centerMap_surjective : Function.Surjective (centerMap X) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  exact ⟨⟨x, (mem_fusionZStar_iff X x).mpr hz⟩, rfl⟩

theorem not_two_dvd_card_ker_centerMap : ¬ 2 ∣ Nat.card (centerMap X).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.card_ker_mul_card_range (centerMap X)
  rw [MonoidHom.range_eq_top_of_surjective _ (centerMap_surjective X), card_top,
    HarrisLit.card_fusionZStar_of_surjective _ (QuotientGroup.mk'_surjective _)
      (not_two_dvd_card_ker_mk X),
    HarrisLit.fusionZStar_eq_center_of_pPrimeCore_eq_bot
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2)] at h1
  rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos h1]
  exact not_two_dvd_card_ker_mk X

theorem pRank_center_eq :
    pRank 2 ↥(center (X ⧸ pPrimeCore 2 X)) = pRank 2 ↥(Open.fusionZStar X) := by
  have hq := GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
    (centerMap X).ker (not_two_dvd_card_ker_centerMap X)
  have e := QuotientGroup.quotientKerEquivOfSurjective (centerMap X) (centerMap_surjective X)
  refine le_antisymm ?_ ?_
  · exact (pRank_two_le_of_injective e.symm.toMonoidHom e.symm.injective).trans hq.le
  · exact hq.symm.le.trans (pRank_two_le_of_injective e.toMonoidHom e.injective)

end Center

theorem pRank_fusionZStar_congr {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ⧸ pPrimeCore 2 X ≃* Y ⧸ pPrimeCore 2 Y) :
    pRank 2 ↥(Open.fusionZStar X) = pRank 2 ↥(Open.fusionZStar Y) := by
  let f : ↥(center (X ⧸ pPrimeCore 2 X)) ≃* ↥(center (Y ⧸ pPrimeCore 2 Y)) :=
    (MulEquiv.subgroupMap e (center _)).trans (MulEquiv.subgroupCongr (Subgroup.map_center_eq e))
  rw [← pRank_center_eq X, ← pRank_center_eq Y]
  exact le_antisymm (pRank_two_le_of_injective f.toMonoidHom f.injective)
    (pRank_two_le_of_injective f.symm.toMonoidHom f.symm.injective)

variable {G : Type} [Group G] [Finite G]

end CFSG.ComponentClassification.GrSLit.L34Sec5S
