module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_map_fixSubgroup)

theorem k1419ClsTransJ_holds : K1419ClsTransJFact := by
  intro Q _ _ β J hβ hJ hZ
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  let π : Q →* PQ Q ⧸ Subgroup.center (PQ Q) :=
    (QuotientGroup.mk' (Subgroup.center (PQ Q)) : PQ Q →* PQ Q ⧸ Subgroup.center (PQ Q)).comp
      (QuotientGroup.mk' (GLAPPrimeCore 3 Q) : Q →* PQ Q)
  have hcomp : GLAPComponent 3 (fixSubgroup (K1419ClsAlpha β)) (J.map π) := by
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 Q)) := CFSG.pPrimeCore_coprime_card
    have hker : Nat.Coprime 3
        (Nat.card ↥(fixSubgroup β ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 Q) : Q →* PQ Q).ker)) := by
      rw [QuotientGroup.ker_mk']
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hcop
    have hJ1 := glaPComponent_map hp (QuotientGroup.mk' (GLAPPrimeCore 3 Q) : Q →* PQ Q) hker hJ
    rw [H1419.map_fixSubgroup_eq β hβ] at hJ1
    have hker2 : (QuotientGroup.mk' (Subgroup.center (PQ Q)) :
        PQ Q →* PQ Q ⧸ Subgroup.center (PQ Q)).ker ≤ Subgroup.center (PQ Q) :=
      (QuotientGroup.ker_mk' _).le
    have hαβ : ∀ y : PQ Q, (QuotientGroup.mk' (Subgroup.center (PQ Q)) :
        PQ Q →* PQ Q ⧸ Subgroup.center (PQ Q)) (H1419.betaBar β y) =
        K1419ClsAlpha β ((QuotientGroup.mk' (Subgroup.center (PQ Q)) :
          PQ Q →* PQ Q ⧸ Subgroup.center (PQ Q)) y) := by
      intro y
      rw [K1419ClsAlpha]
      rfl
    have hJ2 := glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center (PQ Q)) :
      PQ Q →* PQ Q ⧸ Subgroup.center (PQ Q)) hker2 (H1419.betaBar β) (K1419ClsAlpha β) hαβ
      (QuotientGroup.mk'_surjective _) hp hJ1
    dsimp only [π]
    rw [← Subgroup.map_map]
    exact hJ2
  refine ⟨J.map π, hcomp, ?_⟩
  have hJq : CFSG.Open.IsQuasisimple (PQuot 3 J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hJ'q : CFSG.Open.IsQuasisimple (PQuot 3 (J.map π)) :=
    isQuasisimple_pQuot_of_glaPComponent hp hcomp
  have hB : Nontrivial (PQuot 3 (J.map π)) := isQuasisimple_nontrivial hJ'q
  let φ : ↥J →* ↥(J.map π) := π.subgroupMap J
  have hφ : Function.Surjective φ := π.subgroupMap_surjective J
  have hkerle : (pQuotMapOfSurjective hp φ hφ).ker ≤ Subgroup.center (PQuot 3 J) :=
    ker_pQuotMapOfSurjective_le_center hp φ hφ hJq hB
  have hkerbot : (pQuotMapOfSurjective hp φ hφ).ker = ⊥ := by
    rw [hZ] at hkerle
    exact le_bot_iff.mp hkerle
  have hinj : Function.Injective (pQuotMapOfSurjective hp φ hφ) :=
    (MonoidHom.ker_eq_bot_iff _).mp hkerbot
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, pQuotMapOfSurjective_surjective hp φ hφ⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.K1419
