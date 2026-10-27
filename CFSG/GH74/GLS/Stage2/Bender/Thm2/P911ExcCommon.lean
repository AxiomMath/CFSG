module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2Three

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem fixOddFree_of_simple_nonabelian {Y : Type} [Group Y] [Finite Y] (α : MulAut Y)
    (hs : IsSimpleGroup ↥(fixSub α)) (hnab : ∃ a b : ↥(fixSub α), a * b ≠ b * a) :
    FixOddFree α := by
  intro N hN hNn hNodd
  have hnorm : (N.subgroupOf (fixSub α)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (fixSub α)) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hN hx⟩ : ↥(fixSub α)) ∈ N.subgroupOf (fixSub α) := hx
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  · exfalso
    have hcard : Nat.card ↥(N.subgroupOf (fixSub α)) = Nat.card ↥(fixSub α) := by
      rw [h, Subgroup.card_top]
    have h2 : Nat.card ↥(N.subgroupOf (fixSub α)) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
    rw [h2] at hcard
    have hoddF : Odd (Nat.card ↥(fixSub α)) := hcard ▸ hNodd
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddF) a b)

theorem isCyclic_outer_of_hom {Γ : Type} [Group Γ] {H : Type} [Group H] [IsCyclic H]
    (Θ : MulAut Γ →* H) (hΘ : Θ.ker = (MulAut.conj : Γ →* MulAut Γ).range) :
    IsCyclic (Outer Γ) := by
  have hker : Θ.ker = inner Γ := hΘ
  have : IsCyclic (MulAut Γ ⧸ Θ.ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift Θ) (QuotientGroup.kerLift_injective Θ)
  exact (QuotientGroup.quotientMulEquivOfEq hker).isCyclic.mp this

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
