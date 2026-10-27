module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_27Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvClosed

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.J3OuterInv CFSG.Open

theorem centralizer_le_of_outerSetup {J : Type*} [Group J] {T Z : Subgroup J} {φ : MulAut J}
    (H : OuterSetup J T Z φ) {z : J} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set J) ≤ T := by
  have hTC : T ≤ Subgroup.centralizer ({z} : Set J) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (H.Zc z hz x hx)
  rcases H.overgroup _ hTC with hCN | hCtop
  · exact H.cent z hz hz1 hCN
  · exact absurd (H.cen z fun x => Subgroup.mem_centralizer_singleton_iff.1
      (hCtop ▸ Subgroup.mem_top x)) hz1

theorem planeCondP_J3
    (J : Type) [Group J] [Finite J]
    (hJ : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) : PlaneCondP 3 J := by
  obtain ⟨T, Z, φ, H⟩ := CFSG.RankThree.PartTwo.Sec4.Item434SporJ3.exists_outerSetup
    (kFactJ3OuterRank_closed CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv) J hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine planeCondP_of_sylow Nat.prime_three T Z ⟨H.Zcomm, H.Z3⟩ H.Z9 H.Zc fun z hz hz1 => ?_
  exact (T.isPGroup').to_le (centralizer_le_of_outerSetup H hz hz1)

theorem oPrimeCoreTrivialAt_J3
    (J : Type) [Group J] [Finite J]
    (hJ : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) : OPrimeCoreTrivialAt 3 J :=
  oPrimeCoreTrivialAt_of_planeCond Nat.prime_three
    (PlaneCondP.planeCond Nat.prime_three (planeCondP_J3 J hJ))

theorem noOuterFixesCentralizer_J3
    (J : Type) [Group J] [Finite J]
    (hJ : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) :
    NoOuterFixesCentralizer 3 J :=
  noOuterFixesCentralizer_of_planeCond
    (PlaneCondP.planeCond Nat.prime_three (planeCondP_J3 J hJ))
    (fun σ hσ hσi E hE hcard => kFactJ3OuterInvolution J hJ σ hσ hσi E hE hcard)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
