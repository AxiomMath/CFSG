module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.CoverNotCaseTwo
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfig3.false_of_cyclic_of_surjective (hSch : KFactCatalogSchreier)
    (hcfg : D1ComponentConfig3 p P M H R Rbar)
    (hall : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p)))
    {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a)
    {Jt Xt : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (φ : Jt →* L) (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hXR : Xt ≤ Rbar) (hncl : nclIn Jt Xt = Jt) (hXJ : Xt ≤ Jt) (hXnc : ¬ IsCyclic Xt) :
    False := by
  haveI : Fact p.Prime := ⟨hcfg.red.prime⟩
  exact Hyp111.ReducedNongeneration.false_of_surjective_of_cyclic hcfg.red hall
    hcfg.exists_isComponentOf
    (fun L' hL' =>
      have h := hcfg.red.isSimpleGroup_of_isCyclic hcfg.catalog hL' (hall L' hL')
      hSch L' h.1 h.2.1 h.2.2.1)
    hL hLnab φ hφ hcop hXR hncl hXJ hXnc

end CFSG.LocalAnalysis.RankThreeTheoremC

