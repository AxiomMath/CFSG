module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem s7f_hyp62 (hZ : Asc82ZExists) (h76c : Asc82Lemma76Choice) (h79a : Asc82Lemma79a)
    {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) :
    Asc82Hyp62 G := by
  intro X hX hΩ
  obtain ⟨y, hy, hXy⟩ := hX
  have hF : InF X := ⟨hXy.isQuasisimple, Or.inl (Or.inr (Or.inl hΩ))⟩
  have hS' : Sec3SettingLB G y X := sec3SettingLB_of_component hS hy hXy hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSyl⟩ : ∃ S : Subgroup G, IsSylow2Of S (centralizer ({y} : Set G)) :=
    ⟨_, isSylow2Of_map_sylow (Classical.arbitrary (Sylow 2 ↥(centralizer ({y} : Set G))))⟩
  obtain ⟨z, hz⟩ := hZ G y X hS' S hSyl
  have hctx : Sec7Ctx G y X S z :=
    { toSec3SettingLB := hS', toAsc82Notation := hz, omega6 := hΩ }
  obtain ⟨g, B, hc⟩ := h76c G y X S z hctx
  exact h79a G y X S z g B hc

end CFSG.OddStandard.SmallF3.Omega
