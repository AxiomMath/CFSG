module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversExclusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversUnitary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold
public import Certificates.Certificate113
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.Walter.Defs

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

theorem benderCoverFacts_of_isBenderGroup {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K)
    (hL : IsEmpty (K ≃* CFSG.Theory.Comparator.PSL2Model 2))
    (hS : IsEmpty (K ≃* ↥(CFSG.Theory.Comparator.SzModel 1))) (Q : Sylow 2 K) :
    BenderCoverFacts K (Q : Subgroup K) := by
  cases hK with
  | isPSL2 n hn e =>
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact (hL.false e).elim
    · exact benderCoverFacts_sylow_of_mulEquiv e
        ⟨Classical.arbitrary _, benderCoverFacts_psl2Model h _⟩ Q
  | isSuzuki n hn e =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact (hS.false e).elim
    · exact benderCoverFacts_sylow_of_mulEquiv e (suzukiCoverFacts h) Q
  | isPSU3 n hn e => exact benderCoverFacts_sylow_of_mulEquiv e (unitaryCoverFacts hn) Q

theorem bender_cover_quotient
    {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤)
    (hZ2 : Nat.card (Subgroup.center J) = 2)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (J ⧸ Subgroup.center J)) :
    Nonempty ((J ⧸ Subgroup.center J) ≃* CFSG.Theory.Comparator.PSL2Model 2) ∨
    Nonempty ((J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) := by
  rcases isEmpty_or_nonempty ((J ⧸ Subgroup.center J) ≃* CFSG.Theory.Comparator.PSL2Model 2)
    with hL | hL
  · rcases isEmpty_or_nonempty ((J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1))
      with hS | hS
    · exfalso
      obtain ⟨Q⟩ : Nonempty (Sylow 2 J) := inferInstance
      have hBF := benderBorelFactsHold _ hB
        (Q.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)))
      rw [Sylow.coe_mapSurjective] at hBF
      have hCF := benderCoverFacts_of_isBenderGroup hB hL hS
        (Q.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)))
      rw [Sylow.coe_mapSurjective] at hCF
      exact CoverExclusion.false_of_benderCoverFacts hperf hZ2 Q hBF hCF
    · exact Or.inr hS
  · exact Or.inl hL

end CFSG.ProperTwoGeneratedCore.Lemma37
