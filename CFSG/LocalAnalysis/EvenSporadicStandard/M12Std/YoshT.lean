module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModel

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup

@[expose] noncomputable def tK : Subgroup ↥yK := Spec.tK.subgroupOf yK

theorem mem_tK_iff {y : ↥yK} : y ∈ tK ↔ (y : Equiv.Perm (Fin 14)) ∈ Spec.tK :=
  Subgroup.mem_subgroupOf

section Certified

set_option linter.unusedSectionVars false


theorem card_tK : Nat.card tK = 128 := by
  rw [tK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Spec.tK_le).toEquiv]
  exact yFacts.card_tK

theorem exists_order_eight : ∃ t ∈ tK, t ^ 4 ≠ 1 := by
  obtain ⟨t, ht, h4⟩ := yFacts.t8
  refine ⟨⟨t, Spec.tK_le ht⟩, mem_tK_iff.2 ht, fun h => h4 ?_⟩
  have := congrArg Subtype.val h
  simpa using this

theorem swap_preserves_tK (ψ : MulAut ↥yK) (he : ψ Spec.eK = Spec.eK * Spec.cK)
    (hc : ψ Spec.cK = Spec.cK) (hs : ψ Spec.sK = Spec.sK) (hinv : ∀ y, ψ (ψ y) = y)
    {y : ↥yK} (hy : y ∈ tK) : ψ y ∈ tK :=
  mem_tK_iff.2 (yFacts.pt ψ ⟨he, hc, hs, hinv⟩ y (mem_tK_iff.1 hy))

end Certified

end CFSG.EvenSporadicStandard.M12Std.Yosh
