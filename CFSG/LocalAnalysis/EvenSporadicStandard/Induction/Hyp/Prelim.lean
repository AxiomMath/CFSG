module

import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.SolStdInL
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] {N : Subgroup H}

omit [Group H] in
theorem center_eq_bot_of_simple {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hna : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    exact hab (mem_center_iff.1 (h1 ▸ mem_top b) a)

theorem eq_bot_of_isCompIn_fStarSimple [Finite H] (hN : FStarSimple N) {T : Subgroup H}
    (hT : IsCompIn N (centralizer (T : Set H))) : T = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxC : x ∈ centralizer (N : Set H) := mem_centralizer_iff.2 fun m hm =>
    (mem_centralizer_iff.1 (hT.1 hm) x hx).symm
  have hxN : x ∈ N := hN.centralizer_le hxC
  have hz : (⟨x, hxN⟩ : ↥N) ∈ center ↥N := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hxC g g.2)
  have hc : center ↥N = ⊥ := center_eq_bot_of_simple hN.isSimpleGroup hN.nonabelian
  rw [hc, Subgroup.mem_bot] at hz
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)

theorem solStd_of_inL_of_stdBare [Finite H] {L : Subgroup H} (hL : InL L) (hstd : StdBare L) :
    SolStd L :=
  hL.solStd hstd

end CFSG.EvenSporadicStandard.Induction.Hyp
