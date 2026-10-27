module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L128

open Subgroup CFSG CFSG.Blueprint

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := ⟨h.1⟩
  refine ⟨hperf, h.2, ?_⟩
  by_contra hab
  have hcomm : ∀ x y : Q ⧸ center Q, x * y = y * x := by
    intro x y
    by_contra hne
    exact hab ⟨x, y, hne⟩
  have hsimple : IsSimpleGroup (Q ⧸ center Q) := h.2
  have hperf' : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (G := Q) (G' := Q ⧸ center Q) (f := QuotientGroup.mk' (center Q))
      (QuotientGroup.mk'_surjective _)
  have hbot : _root_.commutator (Q ⧸ center Q) = ⊥ := by
    rw [_root_.commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcomm y x
  have htop : (⊤ : Subgroup (Q ⧸ center Q)) = ⊥ :=
    (Group.IsPerfect.commutator_eq_top (G := Q ⧸ center Q)).symm.trans hbot
  have := hsimple.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ center Q)
  have hxbot : x ∈ (⊥ : Subgroup (Q ⧸ center Q)) := htop ▸ Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp hxbot)

section LyJ

theorem all_involutions_conj :
    ∀ u : CFSG.Sporadic.Ly.J, orderOf u = 2 → ∃ c : CFSG.Sporadic.Ly.J, u = c * ClassicalInvolution.LyProof.zJ * c⁻¹ := by
  obtain ⟨hSp, hidx⟩ := ClassicalInvolution.LyProof.S_sylow
  obtain ⟨-, hcover⟩ := ClassicalInvolution.LyProof.S_facts
  have key := ClassicalInvolution.cover_of_sylow (⊤ : Subgroup CFSG.Sporadic.Ly.J)
    ClassicalInvolution.LyProof.SJ hSp hidx ClassicalInvolution.LyProof.zJ (fun s hs hord => by
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hord, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩)
  intro u hu
  obtain ⟨c, -, hc⟩ := key u (Subgroup.mem_top u) hu
  exact ⟨c, hc⟩

end LyJ

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L128
