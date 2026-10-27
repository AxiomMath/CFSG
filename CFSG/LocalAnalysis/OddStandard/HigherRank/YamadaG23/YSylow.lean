module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem sylowIn_eq_of_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {V P Q : Subgroup G} (hP : IsSylowIn p V P) (hQ : IsPGroup p Q) (hQV : Q ≤ V)
    (hPQ : P ≤ Q) : P = Q := by
  have hprod : P.relIndex Q * Q.relIndex V = P.relIndex V :=
    Subgroup.relIndex_mul_relIndex (H := P) (K := Q) (L := V) hPQ hQV
  have hdvd : P.relIndex Q ∣ P.relIndex V := ⟨Q.relIndex V, hprod.symm⟩
  obtain ⟨n, hn⟩ := hQ.index (P.subgroupOf Q)
  have hrel : P.relIndex Q = p ^ n := by
    rw [Subgroup.relIndex]
    exact hn
  have hodd : ¬ p ∣ P.relIndex Q := fun hp => hP.2.2 (hp.trans hdvd)
  have hn0 : n = 0 := by
    by_contra h0
    exact hodd (hrel.symm ▸ dvd_pow_self p h0)
  have hone : P.relIndex Q = 1 := by rw [hrel, hn0, pow_zero]
  exact le_antisymm hPQ (Subgroup.relIndex_eq_one.mp hone)

end CFSG.OddStandard.HigherRank.YamadaG23
