module

public import CFSG.LargeExtraspecial.S9GenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Module CFSG.LargeExtraspecial.OrthoF2 MulAction

universe u

variable (V : Type u) [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def ContainsTv (H : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ (c : V) (μ : Dual (ZMod 2) V), μ c = 0 → ∃ h ∈ H, ∀ x, h x = x + μ x • c

variable {V}

theorem exists_mem_apply_eq_of_containsTv {H : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hH : ContainsTv V H) {v x : V} (hv : v ≠ 0) (hx : x ≠ 0) : ∃ h ∈ H, h v = x := by
  by_cases hxv : x = v
  · exact ⟨1, one_mem _, by rw [hxv]; rfl⟩
  have hvc : v ∉ (ZMod 2) ∙ (x + v) := by
    refine not_mem_span_singleton_of_ne hv fun h => hx ?_
    calc x = x + v - v := by abel
      _ = 0 := by rw [← h, sub_self]
  obtain ⟨μ, hμv, hμc⟩ := Submodule.exists_le_ker_of_notMem hvc
  have hμc' : μ (x + v) = 0 := hμc (Submodule.mem_span_singleton_self _)
  obtain ⟨h, hh, he⟩ := hH (x + v) μ hμc'
  refine ⟨h, hh, ?_⟩
  rw [he, zmod2_eq_one_of_ne_zero hμv, one_smul, ← add_assoc, add_comm v x, add_assoc,
    add_self_eq_zero_zmod2, add_zero]

@[expose] noncomputable def stabQuot {H : Subgroup (V ≃ₗ[ZMod 2] V)} (v : V) :
    stabilizer H v →* ((V ⧸ (ZMod 2) ∙ v) ≃ₗ[ZMod 2] (V ⧸ (ZMod 2) ∙ v)) where
  toFun s := Submodule.Quotient.equiv _ _ ((s : H) : V ≃ₗ[ZMod 2] V) (by
    have hs : ((s : H) : V ≃ₗ[ZMod 2] V) v = v := mem_stabilizer_iff.mp s.2
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hs])
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  map_mul' s s' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

theorem stabQuot_mk {H : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V} (s : stabilizer H v) (x : V) :
    stabQuot v s (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (((s : H) : V ≃ₗ[ZMod 2] V) x) :=
  rfl

theorem prod_dvd_card_of_containsTv (k : ℕ) :
    ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W],
      finrank (ZMod 2) W = k → ∀ H : Subgroup (W ≃ₗ[ZMod 2] W), ContainsTv W H →
        (∏ i ∈ Finset.range k, (2 ^ (i + 1) - 1)) ∣ Nat.card H := by
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro W _ _ _ hW H hH
    have : Finite W := Module.finite_of_finite (ZMod 2)
    have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hW]; omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    have horb : orbit H v = ({0}ᶜ : Set W) := by
      ext x
      constructor
      · rintro ⟨h, rfl⟩ h0
        exact hv (((h : H) : W ≃ₗ[ZMod 2] W).injective (h0.trans (map_zero _).symm))
      · intro hx
        obtain ⟨h, hh, he⟩ := exists_mem_apply_eq_of_containsTv hH hv hx
        exact ⟨⟨h, hh⟩, he⟩
    have hcard : (orbit H v).ncard = 2 ^ (k + 1) - 1 := by
      rw [horb, Set.ncard_compl, Set.ncard_singleton, ← FiniteField.pow_finrank_eq_natCard 2 W,
        hW]
    have hmul := Subgroup.card_mul_index (stabilizer H v)
    rw [MulAction.index_stabilizer, hcard] at hmul
    have hfin : finrank (ZMod 2) (W ⧸ (ZMod 2) ∙ v) = k := by
      have := Submodule.finrank_quotient_add_finrank ((ZMod 2) ∙ v)
      rw [finrank_span_singleton hv, hW] at this
      omega
    have hrange : ContainsTv (W ⧸ (ZMod 2) ∙ v) (stabQuot (H := H) v).range := by
      intro c μ hμ
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨h, hh, he⟩ := hH c (μ.comp ((ZMod 2) ∙ v).mkQ) hμ
      have hvfix : h v = v := by
        rw [he, LinearMap.comp_apply, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self v), map_zero,
          zero_smul, add_zero]
      refine ⟨stabQuot v ⟨⟨h, hh⟩, mem_stabilizer_iff.mpr hvfix⟩, ⟨_, rfl⟩, fun x => ?_⟩
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [stabQuot_mk]
        show Submodule.Quotient.mk (h x) = _
        rw [he, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul]
        rfl
    have h1 := ih (W ⧸ (ZMod 2) ∙ v) hfin _ hrange
    rw [Finset.prod_range_succ, ← hmul]
    exact mul_dvd_mul (h1.trans (Subgroup.card_range_dvd _)) dvd_rfl

variable {Γ : Type*} [Group Γ] {ρ : Γ →* (V ≃ₗ[ZMod 2] V)}

theorem exists_actsTv_of_sub_mem {γ : Γ} {c : V} (hc : c ≠ 0)
    (h : ∀ x, ρ γ x - x ∈ (ZMod 2) ∙ c) : ∃ μ : Dual (ZMod 2) V, ActsTv ρ γ c μ := by
  let f : V →ₗ[ZMod 2] (ZMod 2) ∙ c :=
    LinearMap.codRestrict ((ZMod 2) ∙ c) ((ρ γ).toLinearMap - LinearMap.id) h
  refine ⟨(LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V c hc).symm.toLinearMap ∘ₗ f,
    fun x => ?_⟩
  have h1 := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul (ZMod 2) V c hc (f x)
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h1]
  show ρ γ x = x + (ρ γ x - x)
  abel

theorem exists_actsTv_of_eq_or_eq {γ : Γ} {c : V} (hc : c ≠ 0)
    (h : ∀ x, ρ γ x = x ∨ ρ γ x = x + c) : ∃ μ : Dual (ZMod 2) V, ActsTv ρ γ c μ := by
  refine exists_actsTv_of_sub_mem hc fun x => ?_
  rcases h x with h1 | h1
  · rw [h1, sub_self]
    exact zero_mem _
  · rw [h1, add_sub_cancel_left]
    exact Submodule.mem_span_singleton_self c

theorem ActsTv.apply_eq_zero_of_fix {γ : Γ} {c : V} {μ : Dual (ZMod 2) V}
    (h : ActsTv ρ γ c μ) (hc : c ≠ 0) (hfix : ρ γ c = c) : μ c = 0 := by
  rw [h c, add_eq_left] at hfix
  exact (smul_eq_zero.mp hfix).resolve_right hc

theorem ActsTv.apply_ne_zero_of_ne {γ : Γ} {c : V} {μ : Dual (ZMod 2) V}
    (h : ActsTv ρ γ c μ) {v : V} (hv : ρ γ v ≠ v) : μ v ≠ 0 := by
  intro h0
  apply hv
  rw [h v, h0, zero_smul, add_zero]

theorem prod_dvd_card_of_forall_actsTv [FiniteDimensional (ZMod 2) V] {Δ : Subgroup Γ}
    (hΔ : ∀ (c : V) (μ : Dual (ZMod 2) V), μ c = 0 → ∃ δ ∈ Δ, ActsTv ρ δ c μ) :
    (∏ i ∈ Finset.range (finrank (ZMod 2) V), (2 ^ (i + 1) - 1)) ∣ Nat.card Δ := by
  have hH : ContainsTv V (Δ.map ρ) := by
    intro c μ hμ
    obtain ⟨δ, hδ, he⟩ := hΔ c μ hμ
    exact ⟨ρ δ, ⟨δ, hδ, rfl⟩, he⟩
  exact (prod_dvd_card_of_containsTv _ V rfl _ hH).trans (Subgroup.card_map_dvd Δ ρ)

end CFSG.LargeExtraspecial.S9
