module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanBalancedOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.ONanParity

public section

namespace CFSG.QuasithinUnique.ONan

open Module
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X R : Subgroup (V ≃ₗ[ZMod 2] V)} {A C : Submodule (ZMod 2) V}

theorem finite_subgroup (X : Subgroup (V ≃ₗ[ZMod 2] V)) : Finite X := by
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  infer_instance

omit [Finite V] in
theorem Balanced.ne_of_isCompl (h : Balanced X R A C) : A ≠ C := by
  intro hAC
  have h1 : A ⊓ C = ⊥ := h.setting.isCompl.inf_eq_bot
  rw [← hAC, inf_idem] at h1
  have := h.two_le_A
  rw [h1, finrank_bot] at this
  omega

theorem Balanced.orbit_eq (h : Balanced X R A C) : MulAction.orbit X C = {C, A} := by
  have hCorb : C ∈ MulAction.orbit X C := MulAction.mem_orbit_self C
  have hAC : A ≠ C := h.ne_of_isCompl
  have hr4 : 4 ≤ 2 ^ finrank (ZMod 2) C := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ finrank (ZMod 2) C := Nat.pow_le_pow_right (by norm_num) h.two_le
  by_cases hT : MulAction.orbit X C \ {C, A} = ∅
  · have hsub : MulAction.orbit X C ⊆ {C, A} := by
      intro D hD
      by_contra hDn
      have : D ∈ MulAction.orbit X C \ {C, A} := ⟨hD, hDn⟩
      rw [hT] at this
      exact this
    by_cases hAΔ : A ∈ MulAction.orbit X C
    · refine Set.Subset.antisymm hsub ?_
      intro D hD
      rcases hD with rfl | rfl
      · exact hCorb
      · exact hAΔ
    · exfalso
      have hCinv : ∀ x ∈ X, ∀ v ∈ C, x v ∈ C := by
        intro x hx v hv
        have hxC : x • C ∈ MulAction.orbit X C := smul_mem_orbit hx hCorb
        rcases hsub hxC with h1 | h1
        · have : x v ∈ x • C := Submodule.smul_mem_pointwise_smul v x C hv
          rwa [h1] at this
        · exact absurd (h1 ▸ hxC) hAΔ
      rcases h.irreducible C hCinv with h0 | h1
      · have := h.two_le
        rw [h0, finrank_bot] at this
        omega
      · have hfin : finrank (ZMod 2) C = finrank (ZMod 2) V := by rw [h1, finrank_top]
        have := h.finrank_space
        have := h.two_le
        omega
  · exfalso
    have hcard : (MulAction.orbit X C \ {C, A}).ncard = 2 ^ finrank (ZMod 2) C - 1 := by
      rcases h.card_diff with h0 | h0
      · exact absurd ((Set.ncard_eq_zero (Set.toFinite _)).mp h0) hT
      · exact h0
    by_cases hAΔ : A ∈ MulAction.orbit X C
    ·
      have hfinX : Finite X := finite_subgroup X
      have hΔcard : (MulAction.orbit X C).ncard = 2 ^ finrank (ZMod 2) C - 1 + 2 := by
        have hdisj : Disjoint (MulAction.orbit X C \ {C, A}) {C, A} := Set.disjoint_sdiff_left
        have hunion : MulAction.orbit X C \ {C, A} ∪ {C, A} = MulAction.orbit X C := by
          apply Set.sdiff_union_of_subset
          intro D hD
          rcases hD with rfl | rfl
          · exact hCorb
          · exact hAΔ
        rw [← hunion, Set.ncard_union_eq hdisj, hcard, Set.ncard_pair hAC.symm]
      have heven : Even (MulAction.orbit X C).ncard := by
        refine even_ncard_orbit (G := X) C A hAC hAΔ {g : X | (g : V ≃ₗ[ZMod 2] V) ∈ R}
          (fun ρ hρ => h.setting.smul_C hρ) (fun ρ hρ => h.setting.smul_A hρ)
          (fun g hg ρ hρ => h.norm g g.2 hg ρ hρ) ?_
        intro D hD hfix
        exact h.eq_or_eq_of_fixed hD (fun ρ hρ => hfix ⟨ρ, h.setting.le hρ⟩ hρ)
      obtain ⟨k, hk⟩ := heven
      obtain ⟨m, hm⟩ : Even (2 ^ finrank (ZMod 2) C) :=
        Nat.even_pow.mpr ⟨even_two, by have := h.two_le; omega⟩
      omega
    ·
      have hΔeq : MulAction.orbit X C = insert C (MulAction.orbit X C \ {C, A}) := by
        ext D
        constructor
        · intro hD
          by_cases hDC : D = C
          · exact Or.inl hDC
          · right
            refine ⟨hD, ?_⟩
            rintro (h1 | h1)
            · exact hDC h1
            · exact hAΔ (h1 ▸ hD)
        · rintro (rfl | hD)
          · exact hCorb
          · exact hD.1
      have hnot : C ∉ MulAction.orbit X C \ {C, A} := fun hC => hC.2 (Or.inl rfl)
      have hΔcard : (MulAction.orbit X C).ncard = 2 ^ finrank (ZMod 2) C := by
        rw [hΔeq, Set.ncard_insert_of_notMem hnot, hcard]
        omega
      have hS : IsPartialSpread (finrank (ZMod 2) C)
          (fun D : ↥(MulAction.orbit X C) => (D : Submodule (ZMod 2) V)) :=
        ⟨h.finrank_space, fun D => finrank_orbit D.2,
          fun D E hDE => h.inf_eq_bot_of_mem D.2 E.2 (fun heq => hDE (Subtype.ext heq))⟩
      have hcardι : Nat.card ↥(MulAction.orbit X C) = 2 ^ finrank (ZMod 2) C := by
        rw [Nat.card_coe_set_eq]
        exact hΔcard
      obtain ⟨Z, hZdim, hZ⟩ := hS.completion hcardι
      have hZinv : ∀ x ∈ X, ∀ v ∈ Z, x v ∈ Z := by
        intro x hx v hv
        rw [hZ] at hv ⊢
        rcases hv with rfl | hv
        · left
          exact map_zero x
        · right
          rintro ⟨D, hD⟩ hxv
          apply hv ⟨x⁻¹ • D, smul_mem_orbit (X.inv_mem hx) hD⟩
          show v ∈ x⁻¹ • D
          rw [mem_smul_iff]
          simpa using hxv
      rcases h.irreducible Z hZinv with h0 | h1
      · have := h.two_le
        rw [h0, finrank_bot] at hZdim
        omega
      · rw [h1, finrank_top] at hZdim
        have := h.finrank_space
        have := h.two_le
        omega

theorem Balanced.exists_smul_iff (h : Balanced X R A C) (D : Submodule (ZMod 2) V) :
    (∃ x ∈ X, x • C = D) ↔ (D = C ∨ D = A) := by
  rw [← mem_orbit_iff', h.orbit_eq]
  simp

end CFSG.QuasithinUnique.ONan
