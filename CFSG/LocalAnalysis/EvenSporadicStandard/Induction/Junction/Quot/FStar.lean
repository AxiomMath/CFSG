module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Lift

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {G : Type} [Group G] (M : Subgroup G) [M.Normal]

theorem ker_cqOn_eq_center : (cqOn M M).ker = center ↥M := by
  refine le_antisymm (ker_cqOn_le_center M le_rfl) fun x hx => ?_
  rw [MonoidHom.mem_ker]
  refine Subtype.ext ?_
  show cq M x = 1
  rw [cq_eq_one_iff]
  refine mem_centralizer_iff.2 fun y hy => ?_
  exact congrArg Subtype.val (mem_center_iff.1 hx ⟨y, hy⟩)

noncomputable def cqEquivCenter : (↥M ⧸ center ↥M) ≃* ↥(M.map (cq M)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_cqOn_eq_center M).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (cqOn M M) (cqOn_surjective M M))

theorem centralizer_cq_le (hMp : ⁅M, M⁆ = M) :
    centralizer ((M.map (cq M) : Subgroup (CQ M)) : Set (CQ M)) ≤ ⊥ := by
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : M.map (cq M) ≤ centralizer (((zpowers g).map (cq M) : Subgroup (CQ M)) :
      Set (CQ M)) := by
    rw [Subgroup.le_centralizer_iff, MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact hy
  have h2 := le_centralizer_of_map_le M le_rfl hMp h1
  have h3 : g ∈ centralizer (M : Set G) := (Subgroup.le_centralizer_iff.1 h2) (mem_zpowers g)
  exact Subgroup.mem_bot.2 ((cq_eq_one_iff M).2 h3)

theorem fStarSimple_cq [Finite G] (hMq : CFSG.IsQuasisimple ↥M) :
    FStarSimple (M.map (cq M)) := by
  have hMn : (M.map (cq M)).Normal := Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  have e := cqEquivCenter M
  have hs : IsSimpleGroup ↥(M.map (cq M)) := by
    have := hMq.2.1
    exact MulEquiv.isSimpleGroup e.symm
  have hna : ∃ a b : ↥(M.map (cq M)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hMq.2.2
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa [map_mul] using h))⟩
  exact fStarSimple_of_normal_simple hs hna
    ((centralizer_cq_le M (Subgroup.isPerfect_iff.1 hMq.1)).trans bot_le)

end CFSG.EvenSporadicStandard.Induction.Junction
