module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Three
public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapAll
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem d2U3Three_of_strong (hstrong : D2U3ThreeStrong) (hKU : UnitaryBorelKFacts)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) : D2U3Three := by
  intro d hd G _ _ hglob hD1 p ⟨hpc, hp3⟩ P M A H R hesc hmax hβ Rbar K hRbar hK he
  subst hp3
  obtain ⟨e⟩ := he
  obtain ⟨hdu, hnu⟩ := isUnitaryIndex_of_case hpc hd
  have hdata :=
    hesc.heisData_of_u3 hKU hglob.toAGLGlobal hRbar hK hdu hnu e
  exact hstrong d hd G hglob hD1 3 ⟨hpc, rfl⟩ P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩
    (hesc.stronglyEmbedded_of_pair hglob hβ hdata.pair h84 (hD2.noXBlockFor hglob.toD1Global))

theorem d2U3ThreeStrong_of (h : ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    d.1.characteristic = 3 → D2IndexCaseStrongAt (.lie d)) : D2U3ThreeStrong := by
  intro d hd G _ _ hglob hD1 p ⟨hpc, hp3⟩ P M A H R hesc hmax hβ Rbar K hRbar hK he hstr
  subst hp3
  exact h d hd hpc.symm G hglob hD1 P M A H R hesc hmax hβ hstr Rbar K hRbar hK he

theorem d2ComponentCase_of_all'' (hrank : KFactLieCharRank) (hS : D2SeitzCross)
    (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hAlt5 : D2AltFive) (hA6S : D2IndexCaseStrongAt (.alternating 6 (by norm_num)))
    (hThreeS : D2U3ThreeStrong)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hHB5 : ∀ i p, HB i p → 5 ≤ p)
    (TB : TauCeti.CFSGIndex → ℕ → Prop) (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hTB5 : ∀ i p, TB i p → 5 ≤ p)
    (RK : TauCeti.CFSGIndex → ℕ → Prop)
    (hRK : ∀ (i : TauCeti.CFSGIndex) (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) →
      ∀ p, RK i p → 3 ≤ Open.pRank p (⊤ : Subgroup K))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p =>
        IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p ∧ ¬ TB (.lie d) p ∧ ¬ RK (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt (.sporadic s) fun p =>
        ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p ∧ ¬ RK (.sporadic s) p) :
    D2ComponentCase :=
  d2ComponentCase_of_all hrank hS hSch hα h84 h85 h86 h93 hCGT hD2 hK2 hC3 hK5 hKin hKP hC3p
    hK5p hAlt5 (d2AltSixCase_of_strong h84 hD2 hA6S)
    (d2U3Three_of_strong hThreeS unitaryBorelKFacts h84 hD2)
    HB hHB hHB5 TB hTB hTB5 RK hRK hexc hSpor

theorem d2_of_all'' (hrank : KFactLieCharRank) (hS : D2SeitzCross)
    (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hAlt5 : D2AltFive) (hA6S : D2IndexCaseStrongAt (.alternating 6 (by norm_num)))
    (hThreeS : D2U3ThreeStrong)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hHB5 : ∀ i p, HB i p → 5 ≤ p)
    (TB : TauCeti.CFSGIndex → ℕ → Prop) (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hTB5 : ∀ i p, TB i p → 5 ≤ p)
    (RK : TauCeti.CFSGIndex → ℕ → Prop)
    (hRK : ∀ (i : TauCeti.CFSGIndex) (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) →
      ∀ p, RK i p → 3 ≤ Open.pRank p (⊤ : Subgroup K))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p =>
        IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p ∧ ¬ TB (.lie d) p ∧ ¬ RK (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt (.sporadic s) fun p =>
        ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p ∧ ¬ RK (.sporadic s) p)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M :=
  d2_of_componentCase (d2ComponentCase_of_all'' hrank hS hSch hα h84 h85 h86 h93 hCGT hD2 hK2
    hC3 hK5 hKin hKP hC3p hK5p hAlt5 hA6S hThreeS HB hHB hHB5 TB hTB hTB5 RK hRK hexc hSpor) G
    hnonab hK hchar he hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ hQrank hQM H hH hQH

end CFSG.AGLEmbeddingD2
