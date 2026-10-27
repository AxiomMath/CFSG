module

public import CFSG.LargeExtraspecial.S14NQSixGeom

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.LargeExtraspecial.S2 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_zero_right)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

@[expose] def invNormalizer {W : Type*} [Group W] (z : W) : Subgroup W where
  carrier := {y | y * z * y⁻¹ = z ∨ y * z * y⁻¹ = z⁻¹}
  mul_mem' := by
    rintro x y hx hy
    have e : x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ := by group
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (by rw [e, hy, hx])
    · refine Or.inr ?_
      rw [e, hy, show x * z⁻¹ * x⁻¹ = (x * z * x⁻¹)⁻¹ by group, hx]
    · exact Or.inr (by rw [e, hy, hx])
    · refine Or.inl ?_
      rw [e, hy, show x * z⁻¹ * x⁻¹ = (x * z * x⁻¹)⁻¹ by group, hx, inv_inv]
  one_mem' := Or.inl (by group)
  inv_mem' := by
    rintro x hx
    rcases hx with hx | hx
    · refine Or.inl ?_
      calc x⁻¹ * z * x⁻¹⁻¹ = x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ := by rw [hx]
        _ = z := by group
    · refine Or.inr ?_
      calc x⁻¹ * z * x⁻¹⁻¹ = (x⁻¹ * z⁻¹ * x)⁻¹ := by group
        _ = (x⁻¹ * (x * z * x⁻¹) * x)⁻¹ := by rw [hx]
        _ = z⁻¹ := by group

omit [FiniteDimensional (ZMod 2) V] in
theorem zsmul_zmod2 (n : ℤ) (v : V) : n • v = ((n : ZMod 2)) • v :=
  (Int.cast_smul_eq_zsmul (ZMod 2) n v).symm

namespace HypBasis

variable {p p₁ e₁ f₁ e₂ f₂ : V} (B : HypBasis q p p₁ e₁ f₁ e₂ f₂)
include B

omit [FiniteDimensional (ZMod 2) V]

theorem comm_ab : eichler q e₁ e₂ * eichler q e₁ f₂ = eichler q e₁ f₂ * eichler q e₁ e₂ := by
  rw [eichler_mul B.e₁e₂ B.e₁f₂, eichler_mul B.e₁f₂ B.e₁e₂, add_comm]

theorem comm_ab' : eichler q e₁ e₂ * eichler q f₁ e₂ = eichler q f₁ e₂ * eichler q e₁ e₂ := by
  rw [eichler_comm B.qe₁ B.qe₂ B.e₁e₂, eichler_comm B.qf₁ B.qe₂ B.f₁e₂,
    eichler_mul B.e₂e₁ B.e₂f₁, eichler_mul B.e₂f₁ B.e₂e₁, add_comm]

theorem comm_a'b : eichler q f₁ f₂ * eichler q e₁ f₂ = eichler q e₁ f₂ * eichler q f₁ f₂ := by
  rw [eichler_comm B.qf₁ B.qf₂ B.f₁f₂, eichler_comm B.qe₁ B.qf₂ B.e₁f₂,
    eichler_mul B.f₂f₁ B.f₂e₁, eichler_mul B.f₂e₁ B.f₂f₁, add_comm]

theorem comm_a'b' : eichler q f₁ f₂ * eichler q f₁ e₂ = eichler q f₁ e₂ * eichler q f₁ f₂ := by
  rw [eichler_mul B.f₁f₂ B.f₁e₂, eichler_mul B.f₁e₂ B.f₁f₂, add_comm]

theorem z_apply (x : V) : (eichler q e₁ e₂ * eichler q f₁ f₂) x =
    x + (polar q x f₁ • f₂ + polar q x f₂ • f₁ + (polar q x e₁ + polar q x f₂) • e₂ +
      (polar q x e₂ + polar q x f₁) • e₁) := by
  rw [LinearEquiv.mul_apply, eichler_apply_zmod2 B.qf₁ B.f₁f₂, eichler_apply_zmod2 B.qe₁ B.e₁e₂]
  simp only [polar_add_left, polar_smul_left, smul_eq_mul, B.qf₂, B.qe₂, B.f₂e₁, B.f₁e₁,
    B.f₂e₂, B.f₁e₂, zero_mul, mul_zero, add_zero, mul_one]
  module

theorem z_e₁ : (eichler q e₁ e₂ * eichler q f₁ f₂) e₁ = f₂ := by
  rw [B.z_apply, polar_self_zmod2, B.e₁f₁, B.e₁e₂, B.e₁f₂]
  simp only [zero_smul, one_smul, add_zero, zero_add]
  abel_nf; simp only [zsmul_zmod2]; reduce_mod_char; simp

theorem z_f₂ : (eichler q e₁ e₂ * eichler q f₁ f₂) f₂ = f₂ + e₁ := by
  rw [B.z_apply, polar_self_zmod2, B.f₂e₁, B.f₂f₁, B.f₂e₂]
  simp only [zero_smul, one_smul, add_zero, zero_add]

theorem z_f₁ : (eichler q e₁ e₂ * eichler q f₁ f₂) f₁ = f₁ + e₂ := by
  rw [B.z_apply, polar_self_zmod2, B.f₁e₁, B.f₁e₂, B.f₁f₂]
  simp only [zero_smul, one_smul, add_zero, zero_add]

theorem z_e₂ : (eichler q e₁ e₂ * eichler q f₁ f₂) e₂ = f₁ := by
  rw [B.z_apply, polar_self_zmod2, B.e₂e₁, B.e₂f₁, B.e₂f₂]
  simp only [zero_smul, one_smul, add_zero, zero_add]
  abel_nf; simp only [zsmul_zmod2]; reduce_mod_char; simp

theorem z_norm (v : V) (hv : v = e₁ ∨ v = f₁ ∨ v = e₂ ∨ v = f₂) :
    v + (eichler q e₁ e₂ * eichler q f₁ f₂) v +
      (eichler q e₁ e₂ * eichler q f₁ f₂) ((eichler q e₁ e₂ * eichler q f₁ f₂) v) = 0 := by
  rcases hv with rfl | rfl | rfl | rfl
  · rw [B.z_e₁, B.z_f₂]
    abel_nf; simp only [zsmul_zmod2]; reduce_mod_char; simp
  · rw [B.z_f₁, map_add, B.z_f₁, B.z_e₂]
    abel_nf; simp only [zsmul_zmod2]; reduce_mod_char; simp
  · rw [B.z_e₂, B.z_f₁]
    abel_nf; simp only [zsmul_zmod2]; reduce_mod_char; simp
  · rw [B.z_f₂, map_add, B.z_f₂, B.z_e₁]
    abel_nf; simp only [zsmul_zmod2]; reduce_mod_char; simp

theorem z_pow_three : (eichler q e₁ e₂ * eichler q f₁ f₂) ^ 3 = 1 := by
  set z := eichler q e₁ e₂ * eichler q f₁ f₂ with hz
  have hN : ∀ c₁ c₂ c₃ c₄ : ZMod 2, ∀ w : V, w = c₁ • e₁ + c₂ • f₁ + c₃ • e₂ + c₄ • f₂ →
      w + z w + z (z w) = 0 := by
    intro c₁ c₂ c₃ c₄ w hw
    have h1 := B.z_norm e₁ (Or.inl rfl)
    have h2 := B.z_norm f₁ (Or.inr (Or.inl rfl))
    have h3 := B.z_norm e₂ (Or.inr (Or.inr (Or.inl rfl)))
    have h4 := B.z_norm f₂ (Or.inr (Or.inr (Or.inr rfl)))
    rw [← hz] at h1 h2 h3 h4
    subst hw
    simp only [map_add, map_smul]
    calc _ = c₁ • (e₁ + z e₁ + z (z e₁)) + c₂ • (f₁ + z f₁ + z (z f₁)) +
          c₃ • (e₂ + z e₂ + z (z e₂)) + c₄ • (f₂ + z f₂ + z (z f₂)) := by module
      _ = 0 := by rw [h1, h2, h3, h4]; simp
  have h3 : ∀ x, z (z (z x)) = x := by
    intro x
    set d := polar q x f₁ • f₂ + polar q x f₂ • f₁ + (polar q x e₁ + polar q x f₂) • e₂ +
      (polar q x e₂ + polar q x f₁) • e₁ with hd
    have hzx : z x = x + d := B.z_apply x
    have h0 := hN (polar q x e₂ + polar q x f₁) (polar q x f₂) (polar q x e₁ + polar q x f₂)
      (polar q x f₁) d (by rw [hd]; module)
    rw [hzx, map_add, hzx, map_add, map_add, hzx]
    calc x + d + z d + z (z d) = x + (d + z d + z (z d)) := by abel
      _ = x := by rw [h0, add_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [pow_three]
  exact h3 x

theorem e₁_ne_zero : e₁ ≠ 0 := by
  rintro h
  have := B.e₁f₁
  rw [h, polar_zero_left] at this
  exact zero_ne_one this

theorem f₁_ne_zero : f₁ ≠ 0 := by
  rintro h
  have := B.e₁f₁
  rw [h, polar_zero_right] at this
  exact zero_ne_one this

theorem a_mem : eichler q e₁ e₂ ∈ invNormalizer (eichler q e₁ e₂ * eichler q f₁ f₂) := by
  refine Or.inr ?_
  have ha : eichler q e₁ e₂ * eichler q e₁ e₂ = 1 := eichler_mul_self B.e₁e₂
  have ha' : eichler q f₁ f₂ * eichler q f₁ f₂ = 1 := eichler_mul_self B.f₁f₂
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right ha', ← mul_assoc,
    ha, one_mul]

theorem a'_mem : eichler q f₁ f₂ ∈ invNormalizer (eichler q e₁ e₂ * eichler q f₁ f₂) := by
  refine Or.inr ?_
  have ha : eichler q e₁ e₂ * eichler q e₁ e₂ = 1 := eichler_mul_self B.e₁e₂
  have ha' : eichler q f₁ f₂ * eichler q f₁ f₂ = 1 := eichler_mul_self B.f₁f₂
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right ha', mul_assoc,
    mul_assoc, ha', mul_one]

theorem b_mem : eichler q e₁ f₂ ∈ invNormalizer (eichler q e₁ e₂ * eichler q f₁ f₂) := by
  refine Or.inl ?_
  calc eichler q e₁ f₂ * (eichler q e₁ e₂ * eichler q f₁ f₂) * (eichler q e₁ f₂)⁻¹ =
        eichler q e₁ f₂ * eichler q e₁ e₂ * eichler q f₁ f₂ * (eichler q e₁ f₂)⁻¹ := by
        simp only [mul_assoc]
    _ = eichler q e₁ e₂ * (eichler q e₁ f₂ * eichler q f₁ f₂) * (eichler q e₁ f₂)⁻¹ := by
        rw [← B.comm_ab, mul_assoc (eichler q e₁ e₂)]
    _ = eichler q e₁ e₂ * eichler q f₁ f₂ := by rw [← B.comm_a'b]; group

theorem b'_mem : eichler q f₁ e₂ ∈ invNormalizer (eichler q e₁ e₂ * eichler q f₁ f₂) := by
  refine Or.inl ?_
  calc eichler q f₁ e₂ * (eichler q e₁ e₂ * eichler q f₁ f₂) * (eichler q f₁ e₂)⁻¹ =
        eichler q f₁ e₂ * eichler q e₁ e₂ * eichler q f₁ f₂ * (eichler q f₁ e₂)⁻¹ := by
        simp only [mul_assoc]
    _ = eichler q e₁ e₂ * (eichler q f₁ e₂ * eichler q f₁ f₂) * (eichler q f₁ e₂)⁻¹ := by
        rw [← B.comm_ab', mul_assoc (eichler q e₁ e₂)]
    _ = eichler q e₁ e₂ * eichler q f₁ f₂ := by rw [← B.comm_a'b']; group

omit B in
theorem eichler_smul_mem {H : Subgroup (V ≃ₗ[ZMod 2] V)} {v w : V} (c : ZMod 2)
    (hw : eichler q v w ∈ H) : eichler q v (c • w) ∈ H := by
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, eichler_zero_right]
    exact one_mem H
  · rw [one_smul]
    exact hw

variable [FiniteDimensional (ZMod 2) V]

theorem radFix_e₁_le (hq : q.polarBilin.Nondegenerate) :
    radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) e₁ ≤
      invNormalizer (eichler q e₁ e₂ * eichler q f₁ f₂) := by
  intro t ht
  obtain ⟨u, huF, hpu, rfl⟩ := (mem_radFix_iff hq B.e₁_ne_zero B.qe₁ B.he₁).mp ht
  have hu := B.eq_sum huF
  have hue₁ : polar q u e₁ = 0 := by rw [polar_comm]; exact hpu
  rw [hue₁, zero_smul, add_zero] at hu
  have h1 : polar q e₁ (polar q u f₁ • e₁ + polar q u f₂ • e₂) = 0 := by
    rw [polar_add_right, polar_smul_right, polar_smul_right, polar_self_zmod2, B.e₁e₂,
      smul_zero, smul_zero, add_zero]
  have h2 : polar q e₁ (polar q u e₂ • f₂) = 0 := by
    rw [polar_smul_right, B.e₁f₂, smul_zero]
  have h3 : polar q e₁ (polar q u f₁ • e₁) = 0 := by
    rw [polar_smul_right, polar_self_zmod2, smul_zero]
  have h4 : polar q e₁ (polar q u f₂ • e₂) = 0 := by
    rw [polar_smul_right, B.e₁e₂, smul_zero]
  rw [hu, ← eichler_mul h1 h2, ← eichler_mul h3 h4]
  refine mul_mem (mul_mem ?_ (eichler_smul_mem _ B.a_mem)) (eichler_smul_mem _ B.b_mem)
  refine eichler_smul_mem _ ?_
  rw [eichler_self B.qe₁]
  exact one_mem _

theorem radFix_f₁_le (hq : q.polarBilin.Nondegenerate) :
    radFix q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) f₁ ≤
      invNormalizer (eichler q e₁ e₂ * eichler q f₁ f₂) := by
  intro t ht
  obtain ⟨u, huF, hpu, rfl⟩ := (mem_radFix_iff hq B.f₁_ne_zero B.qf₁ B.hf₁).mp ht
  have hu := B.eq_sum huF
  have huf₁ : polar q u f₁ = 0 := by rw [polar_comm]; exact hpu
  rw [huf₁, zero_smul, zero_add] at hu
  have h1 : polar q f₁ (polar q u e₁ • f₁ + polar q u f₂ • e₂) = 0 := by
    rw [polar_add_right, polar_smul_right, polar_smul_right, polar_self_zmod2, B.f₁e₂,
      smul_zero, smul_zero, add_zero]
  have h2 : polar q f₁ (polar q u e₂ • f₂) = 0 := by
    rw [polar_smul_right, B.f₁f₂, smul_zero]
  have h3 : polar q f₁ (polar q u e₁ • f₁) = 0 := by
    rw [polar_smul_right, polar_self_zmod2, smul_zero]
  have h4 : polar q f₁ (polar q u f₂ • e₂) = 0 := by
    rw [polar_smul_right, B.f₁e₂, smul_zero]
  rw [hu, ← eichler_mul h1 h2, ← eichler_mul h3 h4]
  refine mul_mem (mul_mem ?_ (eichler_smul_mem _ B.b'_mem)) (eichler_smul_mem _ B.a'_mem)
  refine eichler_smul_mem _ ?_
  rw [eichler_self B.qf₁]
  exact one_mem _

theorem omegaFix_le_invNormalizer (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (hpp₁ : polar q p p₁ = 1) :
    omegaFix q hq (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) ≤
      invNormalizer (eichler q e₁ e₂ * eichler q f₁ f₂) := by
  have hmem0 : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hF0 : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hF₁ := sup_span_pair_inf_perp_eq_bot hF0 (hmem0 p) (hmem0 p₁) hpp₁
  have hd₁ : finrank (ZMod 2) (perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) = 2 * 2 := by
    have : finrank (ZMod 2) (perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) + 2 =
        finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) :=
      finrank_perp_sup_span_pair hq hF0 (hmem0 p) (hmem0 p₁) hpp₁
    rw [perp_bot, finrank_top, hV] at this
    omega
  rw [omegaFix_eq_closure_radFix hq hF₁ le_rfl hd₁ B.he₁ B.hf₁ B.e₁_ne_zero B.qe₁ B.qf₁ B.e₁f₁]
  exact (Subgroup.closure_le _).mpr (Set.union_subset (B.radFix_e₁_le hq) (B.radFix_f₁_le hq))

end HypBasis

end CFSG.LargeExtraspecial.S14
