module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.CtxHolds
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem card_quot_center_dvd_card {S : Type} [Group S] [Finite S] (J : Subgroup S) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card S :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J)

section Certified

set_option linter.unusedSectionVars false


theorem card_of_catalogIs_isL2n_of_ne_two {G : Type} [Group G] [Finite G] {k : ℕ} (hk2 : k ≠ 2)
    (h : catalogIs G (S10.isL2n k)) :
    1 ≤ k ∧ Nat.card G = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S10.isL2n] at hi
  | alternating m hm =>
    simp only [S10.isL2n] at hi
    exact absurd hi.1 hk2
  | sporadic s => simp [S10.isL2n] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases r with _ | _ | r <;> simp [S10.isL2n] at hi
      obtain ⟨hp, hn⟩ := hi
      have hk : 1 ≤ k := by
        have := q.exponent_pos
        omega
      refine ⟨hk, ?_⟩
      rw [CatDistinct.ctx_holds.bridge ⟨.A 1 q, hv⟩ G ⟨e⟩]
      show orderA 1 q.card = _
      rw [TauCeti.PrimePower.card_def, hp, hn]
      exact CatDistinct.orderA_one_eq hk
    | _ => simp [S10.isL2n] at hi

end Certified

end CFSG.LocalAnalysis.GLTheoremA.T1428
