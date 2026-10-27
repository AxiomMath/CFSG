module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutInput
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutJanko
public import CFSG.Sporadic.ONOddCore.FixedRankOne
public import CFSG.Walter.J1Props.Elt

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

theorem exists_involution_fixSub
    {G : Type} [Group G] (hG : Nonempty (G ≃* NativeSporadic.ON))
    (α : MulAut G) (hα2 : α * α = 1) : ∃ z : fixSub α, orderOf z = 2 := by
  obtain ⟨⟨V, hVfix, hVea, hV4⟩, -⟩ :=
    Sporadic.ONOddCore.glq_sporadic_outer_involution_fixed_rank_one_ON_exclusion hG α hα2
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV4
    exact absurd hV4 (by norm_num)
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hv2 : v ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian v hvV
  refine ⟨⟨v, hVfix hvV⟩, orderOf_eq_prime (Subtype.ext hv2) fun h => hv1 (Subtype.ext ?_)⟩
  have h' : v = 1 := congrArg Subtype.val h
  exact h'

theorem nonempty_fixSub_equiv_walterJ1_of_local
    (hloc : ONOuterLocalInput) {G : Type} [Group G]
    (hG : Nonempty (G ≃* NativeSporadic.ON)) (α : MulAut G) (hα2 : α * α = 1)
    (hα : α ∉ inner G) : Nonempty (fixSub α ≃* CFSG.Open.walterJ1) := by
  obtain ⟨ψ⟩ := hG
  have : Finite G := Finite.of_equiv _ (ψ.trans ONSchreier.onEquivPv).symm.toEquiv
  obtain ⟨z, hz⟩ := exists_involution_fixSub ⟨ψ⟩ α hα2
  obtain ⟨hJ⟩ := ONOut.nonempty_jankoHyp₀ (hloc G ⟨ψ⟩ α hα2 hα) hz
  exact hJ.nonempty_mulEquiv_walterJ1

theorem card_fixSub_of_local
    (hloc : ONOuterLocalInput) {G : Type} [Group G]
    (hG : Nonempty (G ≃* NativeSporadic.ON)) (α : MulAut G) (hα2 : α * α = 1)
    (hα : α ∉ inner G) : Nat.card (fixSub α) = 175560 := by
  obtain ⟨e⟩ := nonempty_fixSub_equiv_walterJ1_of_local hloc hG α hα2 hα
  rw [Nat.card_congr e.toEquiv]
  exact Walter.J1Props.card_walterJ1

end CFSG.ComponentClassification.SolMax
