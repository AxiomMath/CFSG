module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGTwoCore
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeEscape
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrG2
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwoModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem parabLeviData (h4 : 4 ≤ Nat.card K) {A : Subgroup (adjointGroup .G2 K)}
    (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A) {i : Fin (Tag.rank .G2)}
    (hI : negIndices (g2Datum K) A = {i}) :
    ParabLeviData A (rankOne (g2Datum K).rootGroup i) (posUnipotentExcept (g2Datum K) i)
      (⨆ k, torus (τ := .G2) K k) (CFSG.Open.pCoreOf 2 A) := by
  haveI : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 _
  have hB := borelQuotient_g2 (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K).symm
  set M := rankOne (g2Datum K).rootGroup i with hMdef
  set U := posUnipotentExcept (g2Datum K) i with hUdef
  set T := ⨆ k, torus (τ := .G2) K k with hTdef
  set O := CFSG.Open.pCoreOf 2 A with hOdef
  obtain ⟨hMs, hnc⟩ := rankOne_simple h4 i
  have hMA : M ≤ A := rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  have hUA : U ≤ A := CFSG.AGLEmbedding.LeviBlock.posUnipotentExcept_le_of_borel_le hBA i
  have hAU := CFSG.AGLEmbedding.LeviBlock.le_normalizer_posUnipotentExcept_of_negIndices_eq hB
    hBA hI
  have hUO : U ≤ O := le_pCoreOf hUA
    (fun a ha n hn => (Subgroup.mem_normalizer_iff.1 (hAU ha) n).1 hn)
    (CFSG.AGLEmbedding.LeviBlock.isPGroup_posUnipotentExcept hB i)
  have hMO : M ⊓ O = ⊥ := CFSG.AGLEmbedding.LeviBlock.inf_eq_bot_of_simple_of_isPGroup hnc
    (fun m hm => Subgroup.mem_normalizer_fintype fun o ho => conj_mem_pCoreOf (hMA hm) ho)
    (isPGroup_pCoreOf A)
  have hTA : T ≤ A := (le_sup_left (b := posUnipotent (g2Datum K))).trans hBA
  have hTM : T ≤ Subgroup.normalizer (M : Set (adjointGroup .G2 K)) :=
    iSup_torus_le_normalizer_rankOne hB.ct i
  have hTU : T ≤ Subgroup.normalizer (U : Set (adjointGroup .G2 K)) :=
    CFSG.AGLEmbedding.ToralCensus.iSup_torus_le_normalizer_posUnipotentExcept hB.ct i
  have hTN : T ≤ Subgroup.normalizer ((M ⊔ U : Subgroup (adjointGroup .G2 K)) :
      Set (adjointGroup .G2 K)) := fun t ht =>
    CFSG.AGLEmbedding.ParabAutIrr.mem_normalizer_sup (hTM ht) (hTU ht)
  have hMU : M ≤ Subgroup.normalizer (U : Set (adjointGroup .G2 K)) :=
    rankOne_le_normalizer_posUnipotentExcept hB.ct hB.extras i
  have hZ : Subgroup.center ↥M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥M) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnc
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab
  refine
    { L_le := hMA
      U_le := hUO
      T_le := hTA
      O_norm := fun a ha o ho => conj_mem_pCoreOf ha ho
      U_norm := fun a ha u hu => (Subgroup.mem_normalizer_iff.1 (hAU ha) u).1 hu
      T_norm := fun t ht m hm => (Subgroup.mem_normalizer_iff.1 (hTM ht) m).1 hm
      L_inf_O := fun x hx hxO => ?_
      center_L := fun c hc hcs => ?_
      T_comm := fun a ha b hb => hB.torus_mul_comm ha hb
      decomp := fun g hg => ?_ }
  · have hx' : x ∈ M ⊓ O := ⟨hx, hxO⟩
    rwa [hMO, Subgroup.mem_bot] at hx'
  · have hcen : (⟨c, hc⟩ : ↥M) ∈ Subgroup.center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext (hcs s s.2).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · have hg' : g ∈ ((T ⊔ (M ⊔ U) : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K)) :=
      CFSG.AGLEmbedding.LeviBlock.le_torus_sup_of_negIndices_eq hB hBA hI hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T (M ⊔ U) hTN] at hg'
    obtain ⟨t, ht, w, hw, rfl⟩ := hg'
    have hw' : w ∈ ((M ⊔ U : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) := hw
    rw [Subgroup.coe_mul_of_left_le_normalizer_right M U hMU] at hw'
    obtain ⟨m, hm, u, hu, rfl⟩ := hw'
    exact ⟨t, ht, m, hm, u, hu, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo
