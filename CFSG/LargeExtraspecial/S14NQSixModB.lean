module

public import CFSG.LargeExtraspecial.S14NQSixModA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.S2
open CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

omit [FiniteDimensional (ZMod 2) M] in
theorem mapsTo_fixOf_radFix (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) {p : V} (hp0 : p ≠ 0)
    (hp : q p = 0) (g : omegaGroup q hq) {v : M} (hv : v ∈ A0 ρ p) :
    ρ g v ∈ A0 ρ ((g : V ≃ₗ[ZMod 2] V) p) := by
  rw [mem_fixOf] at hv ⊢
  intro k hk
  have hk' : ((g⁻¹ * k * g : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) ∈ radFix q ⊥ p := by
    have h := (map_conj_radFix hq hp0 hp (by rw [perp_bot]; exact Submodule.mem_top)
      (mem_omegaGroup.mp g.2).1 (by rw [fixGroup_bot]; exact Subgroup.mem_top _)
      (k : V ≃ₗ[ZMod 2] V)).mp hk
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have e : k * g = g * (g⁻¹ * k * g) := by group
  calc ρ k (ρ g v) = ρ (k * g) v := by rw [map_mul, LinearEquiv.mul_apply]
    _ = ρ (g * (g⁻¹ * k * g)) v := by rw [e]
    _ = ρ g (ρ (g⁻¹ * k * g) v) := by rw [map_mul, LinearEquiv.mul_apply]
    _ = ρ g v := by rw [hv _ hk']

noncomputable abbrev Unorm (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) (p e₁ f₁ e₂ f₂ : V) :
    Submodule (ZMod 2) M :=
  A0 ρ p ⊓ normKer (ρ (zElt hq e₁ f₁ e₂ f₂))

noncomputable abbrev Ufix (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) (p e₁ f₁ e₂ f₂ : V) :
    Submodule (ZMod 2) M :=
  A0 ρ p ⊓ fixSpace (ρ (zElt hq e₁ f₁ e₂ f₂))

namespace Plus6

variable {ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)} {p p₁ e₁ f₁ e₂ f₂ : V}
  (P : Plus6 ρ p p₁ e₁ f₁ e₂ f₂)
include P

omit [FiniteDimensional (ZMod 2) M] in
theorem rho_conj {y : omegaGroup q hq}
    (hy : (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) :
    (∀ w, ρ (zElt hq e₁ f₁ e₂ f₂) (ρ y w) = ρ y (ρ (zElt hq e₁ f₁ e₂ f₂) w)) ∨
      ∀ w, ρ (zElt hq e₁ f₁ e₂ f₂) (ρ y w) =
        ρ y (ρ (zElt hq e₁ f₁ e₂ f₂) (ρ (zElt hq e₁ f₁ e₂ f₂) w)) := by
  set z := zElt hq e₁ f₁ e₂ f₂ with hz
  have hyN := P.B.omegaFix_le_invNormalizer hq P.hV P.hpp₁ ⟨y.2, hy⟩
  have hz3 : z * z * z = 1 := by
    have := P.B.z_pow_three
    rw [pow_three] at this
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc]
    exact this
  rcases hyN with h | h
  · left
    have h' : y * z = z * y := by
      have : y * z * y⁻¹ = z := Subtype.ext h
      calc y * z = y * z * y⁻¹ * y := by group
        _ = z * y := by rw [this]
    intro w
    rw [← LinearEquiv.mul_apply, ← map_mul, ← h', map_mul, LinearEquiv.mul_apply]
  · right
    have hzi : z⁻¹ = z * z := by
      rw [inv_eq_of_mul_eq_one_right (show z * (z * z) = 1 by rw [← mul_assoc, hz3])]
    have h' : y * (z * z) = z * y := by
      have h1 : y * z * y⁻¹ = z⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
        exact h)
      have h2 : y * z⁻¹ * y⁻¹ = z := by
        rw [show y * z⁻¹ * y⁻¹ = (y * z * y⁻¹)⁻¹ by group, h1, inv_inv]
      calc y * (z * z) = y * z⁻¹ * y⁻¹ * y := by rw [hzi]; group
        _ = z * y := by rw [h2]
    intro w
    rw [← LinearEquiv.mul_apply, ← map_mul, ← h', map_mul, map_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply]

omit [FiniteDimensional (ZMod 2) M] in
theorem mapsTo_Unorm_of_fix {y : omegaGroup q hq}
    (hy : (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) {v : M}
    (hv : v ∈ Unorm ρ p e₁ f₁ e₂ f₂) : ρ y v ∈ Unorm ρ p e₁ f₁ e₂ f₂ := by
  obtain ⟨hvA, hvN⟩ := Submodule.mem_inf.mp hv
  rw [mem_normKer] at hvN
  refine Submodule.mem_inf.mpr ⟨mapsTo_A0 ρ P.hp0 P.hp y (apply_p_of_mem_fixGroup hy) hvA, ?_⟩
  rw [mem_normKer]
  rcases P.rho_conj hy with h | h
  · rw [h, h, ← map_add, ← map_add, hvN, map_zero]
  · rw [h, h, P.z_cube, ← map_add, ← map_add, add_assoc, add_comm (ρ _ (ρ _ v)), ← add_assoc,
      hvN, map_zero]

omit [FiniteDimensional (ZMod 2) M] in
theorem mapsTo_Ufix_of_fix {y : omegaGroup q hq}
    (hy : (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) {v : M}
    (hv : v ∈ Ufix ρ p e₁ f₁ e₂ f₂) : ρ y v ∈ Ufix ρ p e₁ f₁ e₂ f₂ := by
  obtain ⟨hvA, hvF⟩ := Submodule.mem_inf.mp hv
  rw [mem_fixSpace] at hvF
  refine Submodule.mem_inf.mpr ⟨mapsTo_A0 ρ P.hp0 P.hp y (apply_p_of_mem_fixGroup hy) hvA, ?_⟩
  rw [mem_fixSpace]
  rcases P.rho_conj hy with h | h
  · rw [h, hvF]
  · rw [h, hvF, hvF]

omit [FiniteDimensional (ZMod 2) M] in
theorem mapsTo_of_stab {W : Submodule (ZMod 2) M} (hWA : W ≤ A0 ρ p)
    (hW : ∀ y : omegaGroup q hq,
      (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) →
        ∀ v ∈ W, ρ y v ∈ W)
    (g : omegaGroup q hq) (hgp : (g : V ≃ₗ[ZMod 2] V) p = p) : ∀ v ∈ W, ρ g v ∈ W := by
  intro v hv
  have hmem0 : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hg : (g : V ≃ₗ[ZMod 2] V) ∈ omegaFix q hq ⊥ := by rw [omegaFix_bot]; exact g.2
  obtain ⟨t, ht, hty⟩ := exists_mem_radFix_inv_mul_mem hq (hmem0 p) (hmem0 p₁) P.hp0 P.hp P.hp₁
    P.hpp₁ hg hgp
  set t' : omegaGroup q hq := ⟨t, (radFix_le_omegaFix hq P.hp0 P.hp ht).1⟩ with ht'
  set y : omegaGroup q hq := t'⁻¹ * g with hy
  have hyF : (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) :=
    (mem_omegaFix.mp hty).2
  have hgty : g = t' * y := by rw [hy]; group
  have h1 := hW y hyF v hv
  rw [hgty, map_mul, LinearEquiv.mul_apply]
  have h2 := (mem_fixOf ρ).mp (hWA h1) t' ht
  rw [h2]
  exact h1

theorem mapsTo_sup {U : Submodule (ZMod 2) M} (hUA : U ≤ A0 ρ p)
    (hU : ∀ y : omegaGroup q hq,
      (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) →
        ∀ v ∈ U, ρ y v ∈ U)
    (g : omegaGroup q hq) (hgp : (g : V ≃ₗ[ZMod 2] V) p = p₁) (h : omegaGroup q hq) :
    ∀ v ∈ U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M), ρ h v ∈ U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M) := by
  have hmem0 : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hF0 : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hdim0 : finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) = 2 * 3 := by
    rw [perp_bot, finrank_top, P.hV]
  have htop : OmegaInvariant ρ ⊥ (⊤ : Submodule (ZMod 2) M) := fun _ _ _ _ => Submodule.mem_top
  have hfix : ∀ k : omegaGroup q hq, (k : V ≃ₗ[ZMod 2] V) ∈ fixGroup ⊥ := fun k => by
    rw [fixGroup_bot]; exact Subgroup.mem_top _
  refine timmesfeld_2_1_c ρ hF0 (m := 3) (by norm_num) hdim0 (Or.inl le_rfl) htop (hmem0 p)
    (hmem0 p₁) P.hp0 P.hp P.hp₁ P.hpp₁ P.hD (by rw [top_inf_eq]; exact hUA)
    (fun k _ hkp => P.mapsTo_of_stab hUA hU k hkp) g (hfix g) hgp h (hfix h)

end Plus6

end CFSG.LargeExtraspecial.S14
