module

public import CFSG.RankThree.PartOne.KS.Basic
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.RankThree.PartOne (SectionsForceEvenRankFour)
open CFSG.RankThree.GroupTheory
  (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four)
open scoped MatrixGroups

@[expose] def IsRankTwoSEGroupE3 (p : ℕ) (K : Type) [Group K] : Prop :=
  (∃ _ : Fact p.Prime, Nonempty (K ≃* PSL(2, GaloisField p 2))) ∨
  (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoLie K (.twistedA 2 q)) ∨
  (p = 5 ∧ (Nonempty (K ≃* alternatingGroup (Fin 10)) ∨ IsoLie K .tits ∨
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group))) ∨
  (p = 11 ∧ Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group))

theorem false_of_section_fi22 {G : Type} [Group G] [Finite G]
    (he : CFSG.Open.evenRank G = 3) (hsec : SectionsForceEvenRankFour (Carrier .Fi22))
    (hbr : IsSimpleGroup (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group →
      Nonempty ((TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group ≃* Carrier .Fi22))
    {H : Subgroup G} {K : Subgroup H} [K.Normal] (hs : IsSimpleGroup (↥H ⧸ K))
    (e : (↥H ⧸ K) ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) : False := by
  have : IsSimpleGroup (↥H ⧸ K) := hs
  have : IsSimpleGroup (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group :=
    e.symm.isSimpleGroup
  obtain ⟨b⟩ := hbr this
  have h4 := hsec G H K ⟨e.trans b⟩
  have h3 : CFSG.Assembly.evenRank G = 3 := he
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
