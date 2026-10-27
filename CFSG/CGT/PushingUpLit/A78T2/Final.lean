module

public import CFSG.CGT.PushingUpLit.A78T2.F
public import CFSG.CGT.PushingUpLit.A78T2.Cut

public section

namespace CFSG.CGT.PushingUpLit.A78T2

open CFSG.Assembly CFSG.ABGLocalTools
open CFSG.CGT.PushingUpLit.A78Sp4 (cj mul_mem_cj mem_cj_iff)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L L₂ V V₂ Z J T S M M₂ : Subgroup G} {e : ℕ}

theorem T2Loc.false (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTJ : T = J := h.T_eq_J
  have hJS : J ≤ S := h.base.J_le_S
  have hne : S ≠ J := by
    intro hSJ
    obtain ⟨s, hs, hsT⟩ := h.base.exists_swap
    exact hsT (hTJ ▸ (hSJ ▸ hs : s ∈ J))
  have hrel : J.relIndex S ≤ 2 := by rw [← hTJ]; exact h.base.index
  have hrel1 : J.relIndex S ≠ 1 := fun h1 => hne (le_antisymm (Subgroup.relIndex_eq_one.1 h1) hJS)
  have hrel0 : J.relIndex S ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hidx : J.relIndex S = 2 := by omega
  have hsq : ∀ y ∈ S, y * y ∈ J := fun y hy =>
    Subgroup.mem_subgroupOf.1
      (Subgroup.mul_self_mem_of_index_two (H := J.subgroupOf S) hidx ⟨y, hy⟩)
  have hex : ∃ n : ℕ, ∃ y ∈ S, y ∉ J ∧ orderOf y = n := by
    obtain ⟨y, hyS, hyJ⟩ : ∃ y ∈ S, y ∉ J := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hcon hJS)
    exact ⟨_, y, hyS, hyJ, rfl⟩
  obtain ⟨x, hxS, hxJ, hxo⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ S, y ∉ J → orderOf x ≤ orderOf y := fun y hy hyJ => by
    rw [hxo]
    exact Nat.find_min' hex ⟨y, hy, hyJ, rfl⟩
  have hxT : x ∉ T := by rw [hTJ]; exact hxJ
  have hconj : ∀ g : G, g⁻¹ * x * g ∉ J := by
    intro g hg
    by_cases hx2 : x * x = 1
    · exact hxJ (h.strongClosure hxS hx2 hg)
    · have hxg2 : g⁻¹ * x * g * (g⁻¹ * x * g) ∈ Z := h.base.sq_mem _ hg
      have hid : g⁻¹ * (x * x) * g = g⁻¹ * x * g * (g⁻¹ * x * g) := by group
      have hZV := h.base.Z_le_V
      have hii : x * x * (x * x) = 1 := by
        have h1 := (h.base.elem_V _ (hZV hxg2) _ (hZV hxg2)).2
        have h2 : x * x * (x * x) = g * (g⁻¹ * x * g * (g⁻¹ * x * g) *
            (g⁻¹ * x * g * (g⁻¹ * x * g))) * g⁻¹ := by group
        rw [h2, h1]
        group
      have hiJ : x * x ∈ J := hsq x hxS
      have hiV : x * x ∈ V ∨ x * x ∈ V₂ := h.base.inv_mem _ hiJ hii
      have hsw := h.base.swap x hxS hxT
      have hcomm : x * (x * x) * x⁻¹ = x * x := by group
      have hiZ : x * x ∈ Z := by
        rw [← h.base.inf]
        rcases hiV with hv | hv
        · refine ⟨hv, ?_⟩
          have := mul_mem_cj x hv
          rwa [hcomm, hsw.1] at this
        · refine ⟨?_, hv⟩
          have := mul_mem_cj x hv
          rwa [hcomm, hsw.2] at this
      have hig : x * x ∈ cj g Z := by
        rw [mem_cj_iff, hid]
        exact hxg2
      have hne' : Z ⊓ cj g Z ≠ ⊥ := by
        intro hbot
        have : x * x ∈ Z ⊓ cj g Z := ⟨hiZ, hig⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact hx2 this
      have hgZ := h.ti g hne'
      have hgN : g ∈ Subgroup.normalizer (J : Set G) :=
        h.normalizer_Z_le (CFSG.CGT.PushingUpLit.A78Sp4.mem_normalizer_of_cj hgZ)
      apply hxJ
      have e1 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [e1]
      exact (Subgroup.mem_normalizer_iff.1 hgN _).1 hg
  have hSp : IsPGroup 2 S := h.base.isPGroup_S
  have hSidx : ¬ 2 ∣ S.index := by
    have h1 := (isSylowOf_iff.1 h.base.sylow).2.2
    rwa [Subgroup.relIndex_top_right] at h1
  obtain ⟨N, hN, hNi⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hSp hSidx hJS
    hidx hxS hxJ hmin hconj
  rcases h.simple.eq_bot_or_eq_top_of_normal N with hN1 | hN1
  · rw [hN1, Subgroup.index_bot] at hNi
    have h1 := Subgroup.card_le_card_group V
    rw [h.base.card_V, hNi] at h1
    have h2 := h.base.two_le
    have h3 : 2 ^ 2 ≤ 2 ^ (2 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rw [hN1, Subgroup.index_top] at hNi
    omega

theorem t2Chain : T2Chain := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hloc => hloc.false

end CFSG.CGT.PushingUpLit.A78T2
