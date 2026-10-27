module

public import CFSG.CGT.PushingUpLit.A78Sp4.AuxLemmas

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

variable {G : Type} [Group G]

theorem Sp4Base.conj_mem_inf {V V₂ J T S M M₂ : Subgroup G} {e : ℕ}
    (hb : Sp4Base G V V₂ J T S M M₂ e) {s : G} (hs : s ∈ S) {x : G} (hx : x ∈ V ⊓ V₂) :
    s * x * s⁻¹ ∈ V ⊓ V₂ := by
  by_cases hsT : s ∈ T
  · obtain ⟨h1, h2⟩ := hb.T_norm s hsT
    refine ⟨?_, ?_⟩
    · have := mul_mem_cj s hx.1
      rwa [h1] at this
    · have := mul_mem_cj s hx.2
      rwa [h2] at this
  · obtain ⟨h1, h2⟩ := hb.swap s hs hsT
    refine ⟨?_, ?_⟩
    · have := mul_mem_cj s hx.2
      rwa [h2] at this
    · have := mul_mem_cj s hx.1
      rwa [h1] at this

variable [Finite G] {L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem Sp4Loc.conj_utype (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) {s : G} (hs : s ∈ S)
    {x : G} (hx : UType V V₂ Z Z₂ x) : UType V V₂ Z Z₂ (s * x * s⁻¹) := by
  refine ⟨h.base.conj_mem_inf hs hx.1, fun hz => ?_, fun hz => ?_⟩
  · by_cases hsT : s ∈ T
    · rw [← (h.cross.T_normZ s hsT).1, mul_mem_cj_iff] at hz
      exact hx.2.1 hz
    · rw [← (h.cross.swap_Z s hs hsT).2, mul_mem_cj_iff] at hz
      exact hx.2.2 hz
  · by_cases hsT : s ∈ T
    · rw [← (h.cross.T_normZ s hsT).2, mul_mem_cj_iff] at hz
      exact hx.2.2 hz
    · rw [← (h.cross.swap_Z s hs hsT).1, mul_mem_cj_iff] at hz
      exact hx.2.1 hz

theorem Sp4Loc.not_dvd_card_utype (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) :
    ¬ 2 ∣ Nat.card {x : G | UType V V₂ Z Z₂ x} := by
  have hX : {x : G | UType V V₂ Z Z₂ x} =
      ((V ⊓ V₂ : Subgroup G) : Set G) \ ((Z : Set G) ∪ (Z₂ : Set G)) := by
    ext x
    simp [UType]
  have hZE : (Z : Set G) ∪ (Z₂ : Set G) ⊆ ((V ⊓ V₂ : Subgroup G) : Set G) := by
    intro x hx
    rw [SetLike.mem_coe, ← h.cross.sup_Z]
    rcases hx with hx | hx
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right hx
  have h1 := Set.ncard_sdiff_add_ncard_of_subset hZE
  have h2 := Set.ncard_union_add_ncard_inter (Z : Set G) (Z₂ : Set G)
  have hinter : (Z : Set G) ∩ (Z₂ : Set G) = {1} := by
    ext x
    constructor
    · rintro ⟨hz, hz₂⟩
      have hx : x ∈ Z ⊓ Z₂ := ⟨hz, hz₂⟩
      rw [h.cross.inf_Z] at hx
      simpa using hx
    · rintro rfl
      exact ⟨Z.one_mem, Z₂.one_mem⟩
  rw [hinter, Set.ncard_singleton] at h2
  have hcZ : (Z : Set G).ncard = 2 ^ e := h.side₁.card_Z
  have hcZ₂ : (Z₂ : Set G).ncard = 2 ^ e := h.side₂.card_Z
  have hcE : ((V ⊓ V₂ : Subgroup G) : Set G).ncard = 2 ^ (2 * e) := h.base.card_inf
  have hA : 2 ∣ 2 ^ (2 * e) := dvd_pow_self 2 (by have := h.base.two_le; omega)
  rw [hX, Nat.card_coe_set_eq]
  omega

theorem sp4_exists_u_central (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) :
    ∃ u : G, UType V V₂ Z Z₂ u ∧ ∀ s ∈ S, s * u * s⁻¹ = u := by
  obtain ⟨u, hu, hfix⟩ := exists_fixed_conj_of_not_dvd (p := 2) h.base.sylow.isPGroup
    (X := {x : G | UType V V₂ Z Z₂ x}) (fun s hs x hx => h.conj_utype hs hx)
    h.not_dvd_card_utype
  exact ⟨u, hu, hfix⟩

end CFSG.CGT.PushingUpLit.A78Sp4
