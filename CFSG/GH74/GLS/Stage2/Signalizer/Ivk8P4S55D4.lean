module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55D4Par
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55D4Three

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab


theorem outerFalse_d4_three_model {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 1 ≤ f)
    (hm : LieModel Y .trialityD4 0 3 f) : OuterFalse 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htw : TwistedChevalleyModel Y .D4 (3 ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_three hf htw
  exact OuterFalse.of_mulEquiv e (outerFalse_d4_three_native hf hM σ hσ)

theorem defData_d4 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 p f) : DefData p Y := by
  refine ⟨borelTitsConcl_d4 hm, evenParabolics_d4 hp hp2 hf hm, ?_⟩
  by_cases hp3 : p = 3
  · subst hp3
    exact outerFalse_d4_three_model hf hm
  · have h3p : 3 < p := by
      have := hp.two_le
      have : p ≠ 3 := hp3
      rcases Nat.lt_or_ge 3 p with h | h
      · exact h
      · interval_cases p <;> simp_all
    exact outerFalse_d4_large_model hp hp2 h3p hf hm

theorem def55_d4 : Def55 FD4d :=
  def55_of_defData fun _ _ _ _ hp hp2 _ ⟨_, hf, hm⟩ => defData_d4 hp hp2 hf hm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
