module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.RankThree.PartOne.SEITZ12.Consumer
public import CFSG.RankThree.PartOne.SEITZ12.Final

public section

namespace CFSG.HardMathSupport.Malle.OvergroupTransport

open CFSG.AGLEmbedding

theorem closure_cenGen_eq_top_of_catGroup
    {K : Type} [Group K] [Finite K]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsReeFFourFiveIndex d) (e : K ≃* CatGroup d)
    (E : Subgroup K) (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hEc : Nat.card E = 5 ^ 2) :
    Subgroup.closure {k : K | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have : IsSimpleGroup K := by
    have := isSimpleGroup_of_catGroup_reeF4 hd
    exact e.isSimpleGroup
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.reeF4 2) := by
    obtain ⟨x, hv⟩ := d
    obtain rfl : x = TauCeti.LieTypeIndex.reeF4 2 := hd
    exact ⟨hv, ⟨e⟩⟩
  exact CFSG.RankThree.PartOne.SEITZ12.phi4_closure_cenGen_eq_top_of_ambient
    (fun m K _ _ _ hm hK => CFSG.RankThree.PartOne.SEITZ12.phi4_ambient_holds hm hK) hiso
    Nat.prime_five (by norm_num) (by norm_num) E hE5 hEc

end CFSG.HardMathSupport.Malle.OvergroupTransport
