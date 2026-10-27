module

public import CFSG.Certificates.Kernel.QTwoD6.Glue5

public section

namespace CFSG.StandardType.QTwoD6.K

open Module CFSG.KC.QTwoD6K CFSG.StandardType.QTwoLin

theorem W6_fixes_e0' {w : V7 ≃ₗ[ZMod 3] V7} (hw : w ∈ W6) : w e0 = e0 := by
  let H : Subgroup (V7 ≃ₗ[ZMod 3] V7) :=
    { carrier := {g | g e0 = e0}
      one_mem' := rfl
      mul_mem' := by
        intro a b ha hb
        change (a * b) e0 = e0
        rw [LinearEquiv.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        change a⁻¹ e0 = e0
        apply a.injective
        change a (a.symm e0) = a e0
        rw [LinearEquiv.apply_symm_apply]
        exact ha.symm }
  have hgen : Set.range simpleD6 ⊆ H := by
    rintro _ ⟨j, rfl⟩
    change simpleD6 j e0 = e0
    rw [simpleD6_apply_eq]
    revert j
    decide +kernel
  exact (Subgroup.closure_le H).mpr hgen hw

theorem exists_refl_moving_e0' {Aℓ : Subgroup (V7 ≃ₗ[ZMod 3] V7)}
    (hgen : Aℓ = Subgroup.closure {g | g ∈ Aℓ ∧ IsReflLin g})
    (hmoves : ∃ φ ∈ Aℓ, φ e0 ≠ e0) :
    ∃ g ∈ Aℓ, IsReflLin g ∧ g e0 ≠ e0 := by
  by_contra h
  push Not at h
  let Fix : Subgroup (V7 ≃ₗ[ZMod 3] V7) :=
    { carrier := {g | g e0 = e0}
      one_mem' := rfl
      mul_mem' := by
        intro a b ha hb
        change (a * b) e0 = e0
        rw [LinearEquiv.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        change a⁻¹ e0 = e0
        apply a.injective
        change a (a.symm e0) = a e0
        rw [LinearEquiv.apply_symm_apply]
        exact ha.symm }
  have hle : Aℓ ≤ Fix := by
    rw [hgen, Subgroup.closure_le]
    intro g hg
    exact h g hg.1 hg.2
  obtain ⟨φ, hφ, hφe⟩ := hmoves
  exact hφe (hle hφ)

theorem ext_e0_hvec {f f' : V7 →ₗ[ZMod 3] V7} (h0 : f e0 = f' e0)
    (hh : ∀ i, f (hvec i) = f' (hvec i)) : f = f' := by
  refine LinearMap.pi_ext fun i x => ?_
  have hx : (Pi.single i x : V7) = x • (Pi.single i 1 : V7) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hx, map_smul, map_smul]
  congr 1
  induction i using Fin.cases with
  | zero => exact h0
  | succ i => exact hh i

theorem wb_mem_span_hvec : wb ∈ Submodule.span (ZMod 3) (Set.range (hvec : Fin 6 → V7)) := by
  have h : wb = ∑ i : Fin 6, wb i.succ • hvec i := by decide +kernel
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem twist_index : ∀ l c : ZMod 3, l ≠ 0 → c ≠ 0 →
    ∃ k : Fin 4, ((twLam k : Nat) : ZMod 3) = l ∧ ((twC k : Nat) : ZMod 3) = c := by
  decide +kernel

theorem linearCell_of_checks (hσ : sigInvK = true)
    {F₀ F₁ F₂ FT : Nat → Nat} {N₀ N₁ N₂ NT : Nat} {S₀ S₁ S₂ ST : List Nat}
    (c₀ : covK 16128 F₀ N₀ = true)
    (r₀ : ∀ i, 0 ≤ i → i < N₀ → ∃ kd g₁ w₁ g₂ w₂, rowK 16128 F₀ S₀ i kd g₁ w₁ g₂ w₂ = true)
    (t₀ : ∀ j, 0 ≤ j → j < 4 * S₀.length →
      ∃ kd g₁ w₁ g₂ w₂, twRowK true F₀ S₀ j kd g₁ w₁ g₂ w₂ = true)
    (c₁ : covK 16129 F₁ N₁ = true)
    (r₁ : ∀ i, 0 ≤ i → i < N₁ → ∃ kd g₁ w₁ g₂ w₂, rowK 16129 F₁ S₁ i kd g₁ w₁ g₂ w₂ = true)
    (t₁ : ∀ j, 0 ≤ j → j < 4 * S₁.length →
      ∃ kd g₁ w₁ g₂ w₂, twRowK false F₁ S₁ j kd g₁ w₁ g₂ w₂ = true)
    (c₂ : covK 127 F₂ N₂ = true)
    (r₂ : ∀ i, 0 ≤ i → i < N₂ → ∃ kd g₁ w₁ g₂ w₂, rowK 127 F₂ S₂ i kd g₁ w₁ g₂ w₂ = true)
    (t₂ : ∀ j, 0 ≤ j → j < 4 * S₂.length →
      ∃ kd g₁ w₁ g₂ w₂, twRowK false F₂ S₂ j kd g₁ w₁ g₂ w₂ = true)
    (cT : covT FT NT = true)
    (rT : ∀ i, 0 ≤ i → i < NT → ∃ kd g₁ w₁ g₂ w₂, rowT FT ST i kd g₁ w₁ g₂ w₂ = true)
    (tT : ∀ j, 0 ≤ j → j < 4 * ST.length →
      ∃ kd g₁ w₁ g₂ w₂, twRowT FT ST j kd g₁ w₁ g₂ w₂ = true) :
    GGQ2D6LinearCell := by
  intro A ℓ Aℓ hTV hW6 hNF hℓD hℓ0 hAℓA hJ hfix hmoves hgen hcard φ hφA hφ0
  obtain ⟨w, hw, c, hc, π, hπ, hφc⟩ := hNF φ hφA hφ0
  let g : V7 ≃ₗ[ZMod 3] V7 := w⁻¹ * φ
  have hg : g ∈ A := A.mul_mem (A.inv_mem (hW6 hw)) hφA
  have hgcor : ∀ i, g (hvec i) = c • hvec (π i) := by
    intro i
    simp only [g, LinearEquiv.mul_apply, hφc i, map_smul]
    simp
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hφ0
  have hge0 : g e0 = lam • e0 := by
    change w⁻¹ (φ e0) = lam • e0
    rw [← hlam, map_smul, W6_fixes_e0' (W6.inv_mem hw)]
  suffices H : ∃ ψ ∈ W6 ⊔ Aℓ, ∀ v ∈ Dplane, ψ (g v) ∈ Dplane by
    obtain ⟨ψ, hψ, hψD⟩ := H
    refine ⟨ψ * w⁻¹, (W6 ⊔ Aℓ).mul_mem hψ ((le_sup_left : W6 ≤ W6 ⊔ Aℓ) (W6.inv_mem hw)),
      fun v hv => ?_⟩
    have h1 : (ψ * w⁻¹) (φ v) = ψ (g v) := by
      simp only [LinearEquiv.mul_apply, g]
    rw [h1]
    exact hψD v hv
  rcases hπ with rfl | rfl
  ·
    have hspan : ∀ x ∈ Submodule.span (ZMod 3) (Set.range (hvec : Fin 6 → V7)), g x = c • x := by
      intro x hx
      exact Submodule.span_induction (p := fun x _ => g x = c • x)
        (fun y hy => by
          obtain ⟨i, rfl⟩ := hy
          rw [hgcor i]
          rfl)
        (by simp)
        (fun y z _ _ ihy ihz => by rw [map_add, ihy, ihz, smul_add])
        (fun a y _ ihy => by rw [map_smul, ihy, smul_comm])
        hx
    have hgwb : g wb = c • wb := hspan wb wb_mem_span_hvec
    refine ⟨1, Subgroup.one_mem _, fun v hv => ?_⟩
    change g v ∈ Dplane
    exact Submodule.span_induction (p := fun x _ => g x ∈ Dplane)
      (fun x hx => by
        rcases hx with rfl | rfl
        · rw [hge0]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
        · rw [hgwb]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y _ _ ihx ihy => by rw [map_add]; exact Submodule.add_mem _ ihx ihy)
      (fun a x _ ihx => by rw [map_smul]; exact Submodule.smul_mem _ _ ihx)
      hv
  ·
    have hlam0 : lam ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hge0
      have : e0 = 0 := g.injective (by rw [hge0, map_zero])
      exact absurd this (by decide)
    obtain ⟨k, hkl, hkc⟩ := twist_index lam c hlam0 hc
    have hG : (g : V7 →ₗ[ZMod 3] V7) = twL k := by
      apply ext_e0_hvec
      · rw [LinearEquiv.coe_coe, hge0, twL_e0, hkl]
      · intro i
        rw [LinearEquiv.coe_coe, hgcor, twL_hvec, hkc]
    have hk : (k : Nat) < 4 := k.isLt
    obtain ⟨y, hy, μ, hμ, hℓy⟩ := eq_smul_decV_line hℓD hℓ0
    have hfixy : ∀ ρ ∈ Aℓ, ρ (decV y) = decV y := by
      intro ρ hρ
      have h := hfix ρ hρ
      rw [hℓy, map_smul] at h
      exact smul_right_injective V7 hμ h
    obtain ⟨r, hrA, ⟨cr, φr, h2, rfl⟩, hre0⟩ := exists_refl_moving_e0' hgen hmoves
    have he0 : φr e0 ≠ 0 := by
      intro h0
      apply hre0
      rw [reflection_apply, h0, zero_smul, sub_zero]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · rcases line_settle hTV hW6 hNF hAℓA hJ hσ hg hk hG c₀ r₀ t₀ hfixy h2 hrA he0 with
        h | ⟨-, T, hTA, hT⟩
      · exact h
      · rw [decV_16128] at hfixy
        exact depth2_settle hTV hW6 hNF hAℓA hJ hσ hg hk hG cT rT tT hfixy hgen hcard hTA hT
    · rcases line_settle hTV hW6 hNF hAℓA hJ hσ hg hk hG c₁ r₁ t₁ hfixy h2 hrA he0 with
        h | ⟨hf, -⟩
      · exact h
      · exact absurd hf (by decide)
    · rcases line_settle hTV hW6 hNF hAℓA hJ hσ hg hk hG c₂ r₂ t₂ hfixy h2 hrA he0 with
        h | ⟨hf, -⟩
      · exact h
      · exact absurd hf (by decide)

end CFSG.StandardType.QTwoD6.K

end
