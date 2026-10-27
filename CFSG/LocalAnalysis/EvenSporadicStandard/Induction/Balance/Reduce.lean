module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FStar

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Blueprint

variable {H : Type} [Group H] {N : Subgroup H}

theorem index_eq_one_or_two [Finite H] (hidx : N.index ≤ 2) : N.index = 1 ∨ N.index = 2 := by
  have : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem eq_top_of_index_ne_two [Finite H] (hidx : N.index ≤ 2) (h2 : N.index ≠ 2) : N = ⊤ := by
  rcases index_eq_one_or_two hidx with h | h
  · exact Subgroup.index_eq_one.1 h
  · exact absurd h h2

theorem catalog_of_index_two (hN : FStarSimple N) (hidx : N.index = 2)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) : CFSG.Blueprint.Catalog ↥N := by
  have hNtop : N ≠ ⊤ := fun h => by rw [h, Subgroup.index_top] at hidx; omega
  have := hN.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hN.nonabelian
  let e : (↥N ⧸ (⊥ : Subgroup H).subgroupOf N) ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf N)).trans
      QuotientGroup.quotientBot
  have : ((⊥ : Subgroup H).subgroupOf N).Normal := by
    rw [Subgroup.bot_subgroupOf N]
    infer_instance
  have hsimple : IsSimpleGroup (↥N ⧸ (⊥ : Subgroup H).subgroupOf N) := e.isSimpleGroup
  have hcat := hK N ⊥ hNtop bot_le hsimple
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact CFSG.SectionRank.catalog_of_mulEquiv e.symm hcat

end CFSG.EvenSporadicStandard.Induction.Balance
