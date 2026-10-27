module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormW
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWLevi

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

theorem wSup_normal (Q : Type) [Group Q] : (wSup Q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h := map_wSup_eq (MulAut.conj g)
  rw [← h]
  exact ⟨n, hn, by simp [MulAut.conj_apply]⟩

theorem isSylowTwoOf_of_le {A : Type*} [Group A] {T P Y : Subgroup A} (hT : IsSylowTwoOf T Y)
    (hTP : T ≤ P) (hPY : P ≤ Y) : IsSylowTwoOf T P := by
  refine ⟨hTP, hT.2.1, fun h2 => hT.2.2 ?_⟩
  have h := Subgroup.relIndex_mul_relIndex T P Y hTP hPY
  change 2 ∣ T.relIndex Y
  rw [← h]
  exact Dvd.dvd.mul_right h2 _

theorem isSylowTwoOf_pCoreOf_of_le_normalizer {A : Type*} [Group A] [Finite A]
    {T P Y : Subgroup A} (hT : IsSylowTwoOf T Y) (hTP : T ≤ P) (hPY : P ≤ Y)
    (hPN : P ≤ Subgroup.normalizer (T : Set A)) : IsSylowTwoOf (pCoreOf 2 P) Y := by
  have hTle : T ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTP hPN hT.2.1
  refine ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans hPY,
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P, fun h2 => hT.2.2 ?_⟩
  exact h2.trans (Subgroup.relIndex_dvd_of_le_left Y hTle)

theorem conj_mem_sylow_of_wCent {A : Type} [Group A] [Finite A] {Y P T : Subgroup A} {β : A}
    (hT : IsSylowTwoOf T Y) (hTP : T ≤ P) (hPY : P ≤ Y)
    (hodd : ¬ 2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index)
    (hW : ParabComm.WCent P β) : ∀ t ∈ T, β * t * β⁻¹ ∈ T := by
  intro t ht
  have htP : t ∈ P := hTP ht
  have hRT : pCoreOf 2 P ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hT hTP hPY)
  obtain ⟨k, hk⟩ := hT.2.1 ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨t, htP⟩ ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
    haveI := wSup_normal (↥P ⧸ CFSG.pCore 2 ↥P)
    refine ParabCensus.mem_of_pow_two_pow_eq_one hodd (k := k) ?_
    rw [← map_pow]
    have h1 : (⟨t, htP⟩ : ↥P) ^ 2 ^ k = 1 := Subtype.ext (by simpa using htk)
    rw [h1, map_one]
  have hc := hW t htP hmem
  have hconj : β * t * β⁻¹ = (β * t * β⁻¹ * t⁻¹) * t := by group
  rw [hconj]
  exact T.mul_mem (hRT hc) ht

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small
