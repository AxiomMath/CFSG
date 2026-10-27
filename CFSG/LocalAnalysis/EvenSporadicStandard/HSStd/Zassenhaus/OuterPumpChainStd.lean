module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerComponent

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G]

theorem standard_of_maximalF_pumpType [Finite G] (ctx : PumpCtx G) (h13 : FS79Thm13UseSec G)
    (hrank : KGPumpRank) {M : Subgroup G} (hM : MaximalF M) (hp : PumpType (↥M ⧸ center ↥M)) :
    CFSG.Open.standardComponentIsStandard M := by
  obtain ⟨t, ht, hMt⟩ := hM.1
  exact standardComponentIsStandard_of_stdBare ht hMt
    (stdBare_of_maximalF_pumpType ctx h13 hrank hM hp)

theorem exists_standard_maximal_pump_above [Finite G] (ctx : PumpCtx G) (hTab : KGPumpTable)
    (h13 : FS79Thm13UseSec G) (hrank : KGPumpRank) {K₀ : Subgroup G} (h₀ : InLF K₀)
    (hp : PumpType (↥K₀ ⧸ center ↥K₀)) (g : G)
    (hc : ⁅K₀, K₀.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    ∃ M : Subgroup G, TransGen LtF K₀ M ∧ K₀ ≠ M ∧ MaximalF M ∧
      PumpType (↥M ⧸ center ↥M) ∧ StdBare M ∧ CFSG.Open.standardComponentIsStandard M := by
  obtain ⟨M, hT, hne, hmax, hpM, hstd⟩ := exists_maximal_pump_above ctx hTab h13 hrank h₀ hp g hc
  exact ⟨M, hT, hne, hmax, hpM, hstd, standard_of_maximalF_pumpType ctx h13 hrank hmax hpM⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
