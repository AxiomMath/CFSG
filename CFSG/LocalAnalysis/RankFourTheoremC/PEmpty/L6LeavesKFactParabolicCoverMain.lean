module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverSeitz
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverAbstract
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverBender

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (seitz2313Even_holds)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenScope)

theorem kxSection_of_normal {A : Type} [Group A] [Finite A] {K₀ H N : Subgroup A} {z : A}
    {p f : ℕ} [Fact p.Prime] (hK₀ : CFSG.Open.pRank p K₀ ≤ 1) (hHK₀ : H ≤ K₀)
    (hHn : (H.subgroupOf K₀).Normal) (hs : S622IsSimpleSection H N) (hfd : f ∣ N.relIndex H)
    (hpd : p ∣ N.relIndex H) (hpN : ¬ p ∣ Nat.card N) (hzK₀ : z ∈ K₀) (hz : orderOf z = p) :
    KxSection z K₀ f := by
  have hpH : p ∣ Nat.card H := hpd.trans (Subgroup.relIndex_dvd_card N H)
  have hzH : z ∈ H := KPCov.mem_of_normal_of_dvd hK₀ hHK₀ hHn hpH hzK₀ hz
  have hzN : z ∉ N := by
    intro hzN
    apply hpN
    have h2 : orderOf (⟨z, hzN⟩ : ↥N) = p := by rw [← Subgroup.orderOf_coe]; exact hz
    exact h2 ▸ orderOf_dvd_natCard _
  exact ⟨H, N, hHK₀, hs, hzH, hzN, hfd⟩

theorem kFactParabolicCover_of_inputs
    (hLevi : KFactParabolicLevi) (hRad : KFactParabolicRadical) (hOut : KFactSeitzOutside) :
    KFactParabolicCover := by
  intro A _ _ K K₀ z p hK hp hp5 hrk hz hzK₀ hpar hne hSyl
  have hB : ¬ fusionIsBenderGroup ↥K := fun hB =>
    KPCov.false_of_bender hp (by omega) hB hpar hne hSyl
  obtain ⟨f, H, N, hf, hf2, hfp, hrank, hHK₀, hHn, hs, hfd, hpd, hpN⟩ :=
    hLevi A K K₀ p hK hB hp hp5 hrk hpar hne hSyl
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀K : K₀ ≤ K := hpar.1
  have hK₀p : CFSG.Open.pRank p K₀ ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hK₀K).trans hrk
  refine ⟨f, hf, hf2, hfp, kxSection_of_normal hK₀p hHK₀ hHn hs hfd hpd hpN hzK₀ hz, ?_⟩
  have hfK₀ : f ∣ Nat.card K₀ :=
    hfd.trans ((Subgroup.relIndex_dvd_card N H).trans (Subgroup.card_dvd_of_le hHK₀))
  have hO : pCoreOf 2 K₀ ≠ ⊥ := hRad A K K₀ hK hB hpar hne
  have hO2 : IsPGroup 2 (pCoreOf 2 K₀) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀
  have hOK : pCoreOf 2 K₀ ≤ K := (CFSG.LieType.BorelTits.pCoreOf_le 2 K₀).trans hK₀K
  have hN : K₀ ≤ normalizer (pCoreOf 2 K₀ : Set A) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  refine KPCov.exists_conj_inf_dvd hK₀K hne hfK₀ hrank fun E hEK₀ hEab hEcard => ?_
  by_cases hin : ∃ d : TauCeti.ValidLieTypeIndex,
      EvenScope d.1 ∧ Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
  · obtain ⟨d, hs, hd⟩ := hin
    exact KPCov.hyperGenSet_of_seitz2313Even seitz2313Even_holds hf hf2 hd hs
      (hEK₀.trans hK₀K) hEab hEcard hOK hO hO2 (hEK₀.trans hN)
  · exact hOut A K E (pCoreOf 2 K₀) f hK hB (fun d hs hd => hin ⟨d, hs, hd⟩) hf hf2
      (hEK₀.trans hK₀K) hEab hEcard hOK hO hO2 (hEK₀.trans hN)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
