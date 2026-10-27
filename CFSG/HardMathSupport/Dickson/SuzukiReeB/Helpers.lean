module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion

public section

namespace CFSG.HardMathSupport.Dickson.SuzukiReeB

open CFSG.HardMathSupport.Solomon.Coordinator

private theorem dickson_open_isQuasisimple {Q : Type*} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Open.IsQuasisimple Q := by
  obtain ⟨hp, hs, -⟩ := h
  exact ⟨hp.commutator_eq_top, hs⟩

theorem perfectInLayer_of_isSolvable {S : Type*} [Group S] (β : MulAut S)
    (h : Group.IsSolvable ↥(fixSubgroup β)) : PerfectInLayer β := by
  intro P hPC hP
  haveI := h
  have hbot : P ≤ ⊥ := by
    intro x hx
    have h1 := LieSemisimple.map_eq_one_of_perfect hPC hP (MonoidHom.id ↥(fixSubgroup β)) x hx
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  exact hbot.trans bot_le

theorem perfectInLayer_of_normal_quasisimple {S : Type*} [Group S] [Finite S] (β : MulAut S)
    {N : Subgroup S} (hN : N ≤ fixSubgroup β) (hNn : (N.subgroupOf (fixSubgroup β)).Normal)
    (hq : CFSG.IsQuasisimple ↥N)
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β))) :
    PerfectInLayer β := by
  intro P hPC hP
  have hPN : P ≤ N := LieSemisimple.perfect_le_of_solvable_quotient hN hsol hPC hP
  have hcomp : CFSG.Open.IsComponentOf N (fixSubgroup β) :=
    ⟨hN, CFSG.Open.IsSubnormal.step hN hNn (CFSG.Open.IsSubnormal.refl _),
      dickson_open_isQuasisimple hq⟩
  exact hPN.trans (le_sSup (show N ∈ {K : Subgroup S | CFSG.Open.IsComponentOf K (fixSubgroup β)}
    from hcomp))

theorem exists_eq_conj_of_mem_range {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) {p : ℕ}
    {β : MulAut S} (hin : β ∈ (MulAut.conj : S →* MulAut S).range) (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) : ∃ x : S, β = MulAut.conj x ∧ x ^ p = 1 ∧ x ≠ 1 := by
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hin
  refine ⟨x, rfl, ?_, fun h => hβ1 (by rw [h, map_one])⟩
  have h1 : (MulAut.conj (x ^ p) : MulAut S) = 1 := by rw [map_pow]; exact hβ
  have hmem : x ^ p ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun f : MulAut S => f g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x ^ p = (x ^ p * g * (x ^ p)⁻¹) * x ^ p := by rw [this]
      _ = x ^ p * g := by group
  rw [hZ] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem fixSubgroup_conj {S' : Type*} [Group S'] (x : S') :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set S') :=
  b3Lie_fixSubgroup_conj x

end CFSG.HardMathSupport.Dickson.SuzukiReeB
