module

public import CFSG.LieType.SeitzGeneration.QuasiHigh5Rest
import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListLie

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central

theorem not_excIndex_three_twistedA_two {q : TauCeti.PrimePower} (h8 : q.card ≠ 8) :
    ¬ CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.ExcIndex 3 (.twistedA 2 q) := by
  intro hX
  rcases hX with hB | ⟨-, hL | hG | hB2 | hT | hS⟩
  · simp only [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Index] at hB
    rcases hB with ⟨-, ⟨-, hB⟩ | ⟨-, hB⟩⟩
    · exact hB (by norm_num)
    · omega
  · simp [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsL2EightIndex] at hL
  · simp only [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Index] at hG
    obtain ⟨-, n, hn3, hn⟩ := hG
    omega
  · simp [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIndex] at hB2
  · simp [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsTwistedE6FourIndex] at hT
  · rcases hS with hF | hD | hF4
    · simp [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsF4EightIndex] at hF
    · simp [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsD4FourIndex] at hD
    · simp only [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.FourIndex] at hF4
      obtain ⟨hp, he⟩ := hF4.1
      exact h8 (by rw [TauCeti.PrimePower.card_def, hp, he]; norm_num)

theorem seitzHyperGamma_eq_top_of_linThree
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A 2 q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group)
    (h3 : 3 ∣ q.card - 1) (h4 : q.card ≠ 4) {A : Subgroup (MulAut K)}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ 2) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 A = ⊤ :=
  CFSG.LieType.SeitzGeneration.QuasiHigh5.seitzHyperGamma_eq_top_linear Nat.prime_three
    (by norm_num) hperf e (GL83.I243.CoverList.three_ne_p_of_dvd_pred h3)
    (show 3 ∣ 2 + 1 ∧ 3 ∣ q.card - 1 from ⟨by norm_num, h3⟩)
    (fun h => h4 h.2.2) hA hcard

theorem seitzHyperGamma_eq_top_of_unitaryThree
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)
    (h3 : 3 ∣ q.card + 1) (h8 : q.card ≠ 8) {A : Subgroup (MulAut K)}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ 2) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 A = ⊤ :=
  CFSG.LieType.SeitzGeneration.QuasiHigh5.seitzHyperGamma_eq_top_unitary Nat.prime_three
    (by norm_num) hperf e (GL83.I243.CoverList.three_ne_p_of_dvd_succ h3)
    (show 3 ∣ 2 + 1 ∧ 3 ∣ q.card + 1 from ⟨by norm_num, h3⟩) hA hcard
    (Or.inl (not_excIndex_three_twistedA_two h8))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central
