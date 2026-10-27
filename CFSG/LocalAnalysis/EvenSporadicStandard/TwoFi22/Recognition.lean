module

public import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open Subgroup CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

variable {G : Type} [Group G]

theorem center_eq_bot_of_nonabelian [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd (mem_center_iff.1 (h ▸ mem_top b) a) hab

theorem commutator_eq_top_of_nonabelian [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hc | hc
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have h : ⁅a, b⁆ ∈ commutator G := commutator_mem_commutator (mem_top a) (mem_top b)
    rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact hab h
  · exact hc

theorem isSimpleGroup_commutator_of_nonabelian [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : IsSimpleGroup (commutator G) :=
  MulEquiv.isSimpleGroup
    ((MulEquiv.subgroupCongr (commutator_eq_top_of_nonabelian hnonab)).trans Subgroup.topEquiv)

theorem closure_conjClass_eq_top [IsSimpleGroup G] {t : G} (ht : t ≠ 1) :
    Subgroup.closure {g | IsConj t g} = ⊤ := by
  have hN : (Subgroup.closure {g | IsConj t g}).Normal := ⟨fun n hn g => by
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      exact subset_closure (IsConj.trans hx (isConj_iff.2 ⟨g, rfl⟩))
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {g | IsConj t g}) with hc | hc
  · have hmem : t ∈ ({g | IsConj t g} : Set G) := IsConj.refl t
    have := Subgroup.subset_closure hmem
    rw [hc, SetLike.mem_coe, mem_bot] at this
    exact absurd this ht
  · exact hc

theorem orderOf_eq_two_of_isConj {t x : G} (ht : orderOf t = 2) (hx : IsConj t x) :
    orderOf x = 2 := by
  obtain ⟨c, hc⟩ := hx
  rw [← SemiconjBy.orderOf_eq _ hc, ht]

theorem isSporadic_fi23_of_threeTransposition
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : CFSG.Open.IsQuasisimple L) {t : G} (ht : orderOf t = 2)
    (hC : centralizer ({t} : Set G) = L) (hQ : IsSporadic (L ⧸ center L) .Fi22)
    (hprod : ∀ d e : G, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    IsSporadic G .Fi23 := by
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hrec := CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_recognition G
    {g | IsConj t g} ⟨t, rfl⟩ (fun d hd => orderOf_eq_two_of_isConj ht hd)
    (fun d hd e he => hprod d e hd he) (closure_conjClass_eq_top ht1)
    (center_eq_bot_of_nonabelian hnonab) (isSimpleGroup_commutator_of_nonabelian hnonab) t
    (IsConj.refl t)
  obtain ⟨-, h23, -⟩ := hrec
  obtain ⟨e⟩ := hQ
  have hsub : CFSG.Open.IsSubnormal L (centralizer ({t} : Set G)) := by
    rw [hC]
    exact CFSG.Open.IsSubnormal.refl L
  obtain ⟨φ⟩ := h23.2 ⟨L, ⟨hC.ge, hsub, hL⟩, ⟨e⟩⟩
  exact ⟨φ⟩

end CFSG.EvenSporadicStandard.TwoFi22
