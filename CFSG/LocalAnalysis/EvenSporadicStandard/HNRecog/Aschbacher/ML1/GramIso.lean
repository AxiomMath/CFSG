module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GramBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V'] [Module (ZMod 2) V']

private noncomputable def Phi (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (v : V) :
    (A5 → ZMod 2) →ₗ[ZMod 2] V :=
  Fintype.linearCombination (ZMod 2) fun g => σ (g, 1) v

private lemma Phi_apply (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (v : V) (c : A5 → ZMod 2) :
    Phi σ v c = ∑ g, c g • σ (g, 1) v :=
  Fintype.linearCombination_apply (ZMod 2) (fun g => σ (g, 1) v) c

private lemma Phi_surjective (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (v : V)
    (hS : Swap.StdHyp σ) (hv : ∀ x : A5, σ (x, x) v = v) (hv0 : v ≠ 0) :
    Function.Surjective (Phi σ v) := by
  rw [← LinearMap.range_eq_top]
  change LinearMap.range (Fintype.linearCombination (ZMod 2) fun g => σ (g, 1) v) = ⊤
  rw [Fintype.range_linearCombination]
  exact span_w (σ := σ) (v := v) hS hv hv0

private lemma B_Phi (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (B : LinearMap.BilinForm (ZMod 2) V)
    (v : V) (c : A5 → ZMod 2) (y : V) :
    B (Phi σ v c) y = ∑ g, c g * B (σ (g, 1) v) y := by
  rw [Phi_apply, map_sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

private lemma Phi_B (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (B : LinearMap.BilinForm (ZMod 2) V)
    (v : V) (x : V) (c : A5 → ZMod 2) :
    B x (Phi σ v c) = ∑ h, c h * B x (σ (h, 1) v) := by
  rw [Phi_apply, map_sum]
  simp only [map_smul, smul_eq_mul]

private lemma B_Phi_Phi (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (B : LinearMap.BilinForm (ZMod 2) V)
    (v : V) (hF : FormHyp σ B) (c c' : A5 → ZMod 2) :
    B (Phi σ v c) (Phi σ v c') = ∑ g, ∑ h, c g * c' h * gramF σ B v (g⁻¹ * h) := by
  calc B (Phi σ v c) (Phi σ v c')
      = ∑ g, c g * B (σ (g, 1) v) (Phi σ v c') := B_Phi σ B v c (Phi σ v c')
    _ = ∑ g, c g * (∑ h, c' h * B (σ (g, 1) v) (σ (h, 1) v)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Phi_B σ B v (σ (g, 1) v) c']
    _ = ∑ g, c g * (∑ h, c' h * gramF σ B v (g⁻¹ * h)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [show (∑ h, c' h * B (σ (g, 1) v) (σ (h, 1) v)) =
                ∑ h, c' h * gramF σ B v (g⁻¹ * h) by
              refine Finset.sum_congr rfl fun h _ => ?_
              rw [B_w (σ := σ) (B := B) (v := v) hF]]
    _ = ∑ g, ∑ h, c g * c' h * gramF σ B v (g⁻¹ * h) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          ring

private lemma Phi_eq_zero_iff (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V))
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V)
    (hS : Swap.StdHyp σ) (hF : FormHyp σ B) (hv : ∀ x : A5, σ (x, x) v = v) (hv0 : v ≠ 0)
    (c : A5 → ZMod 2) :
    Phi σ v c = 0 ↔ ∀ h, ∑ g, c g * gramF σ B v (g⁻¹ * h) = 0 := by
  constructor
  · intro hc h
    calc ∑ g, c g * gramF σ B v (g⁻¹ * h)
        = ∑ g, c g * B (σ (g, 1) v) (σ (h, 1) v) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [B_w (σ := σ) (B := B) (v := v) hF]
      _ = B (Phi σ v c) (σ (h, 1) v) := (B_Phi σ B v c (σ (h, 1) v)).symm
      _ = 0 := by rw [hc]; simp
  · intro hc
    apply hF.nondeg.1
    intro y
    have hspan : Submodule.span (ZMod 2) (Set.range fun g : A5 => σ (g, 1) v) = ⊤ :=
      span_w (σ := σ) (v := v) hS hv hv0
    have hle : Submodule.span (ZMod 2) (Set.range fun g : A5 => σ (g, 1) v) ≤
        LinearMap.ker (B (Phi σ v c)) := by
      rw [Submodule.span_le]
      rintro u ⟨h, rfl⟩
      change B (Phi σ v c) (σ (h, 1) v) = 0
      rw [B_Phi]
      have h1 : (∑ g, c g * B (σ (g, 1) v) (σ (h, 1) v)) =
          ∑ g, c g * gramF σ B v (g⁻¹ * h) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [B_w (σ := σ) (B := B) (v := v) hF]
      rw [h1]
      exact hc h
    exact hle (by rw [hspan]; trivial)

private lemma tau_apply_w (τ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (v : V)
    (hτ : ∀ x : A5, τ (x, x) v = v) (x y h : A5) :
    τ (x, y) (τ (h, 1) v) = τ (x * h * y⁻¹, 1) v := by
  have hmul : τ (x, y) = τ (x, 1) * τ (1, y) := by
    have h : (x, 1) * (1, y) = (x, y) := by ext <;> simp
    rw [← map_mul, h]
  calc τ (x, y) (τ (h, 1) v)
      = (τ (x, 1) * τ (1, y)) (τ (h, 1) v) := by rw [hmul]
    _ = τ (x, 1) (τ (1, y) (τ (h, 1) v)) := LinearEquiv.mul_apply _ _ _
    _ = τ (x, 1) (τ (h * y⁻¹, 1) v) := by rw [σ_inr_w (σ := τ) (v := v) hτ]
    _ = τ (x * (h * y⁻¹), 1) v := σ_inl_w (σ := τ) (v := v) x (h * y⁻¹)
    _ = τ (x * h * y⁻¹, 1) v := by rw [show x * (h * y⁻¹) = x * h * y⁻¹ by group]

private lemma Phi_group (τ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (v : V)
    (hτ : ∀ x : A5, τ (x, x) v = v) (x y : A5) (c : A5 → ZMod 2) :
    τ (x, y) (Phi τ v c) = Phi τ v (fun k => c (x⁻¹ * k * y)) := by
  rw [Phi_apply, Phi_apply, map_sum]
  simp only [map_smul]
  rw [← Equiv.sum_comp ((Equiv.mulLeft x).trans (Equiv.mulRight y⁻¹))
        (fun k => c (x⁻¹ * k * y) • τ (k, 1) v)]
  refine Finset.sum_congr rfl fun h _ => ?_
  change c h • τ (x, y) (τ (h, 1) v)
      = c (x⁻¹ * (x * h * y⁻¹) * y) • τ (x * h * y⁻¹, 1) v
  rw [tau_apply_w τ v hτ x y h]
  rw [show x⁻¹ * (x * h * y⁻¹) * y = h by group]

theorem gram_iso (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V'))
    (B : LinearMap.BilinForm (ZMod 2) V) (B' : LinearMap.BilinForm (ZMod 2) V')
    (hS : Swap.StdHyp σ) (hS' : Swap.StdHyp σ') (hF : FormHyp σ B) (hF' : FormHyp σ' B')
    (v : V) (v' : V') (hv : ∀ x : A5, σ (x, x) v = v) (hv' : ∀ x : A5, σ' (x, x) v' = v')
    (hv0 : v ≠ 0) (hv0' : v' ≠ 0) (hf : gramF σ B v = gramF σ' B' v') :
    ∃ a : V ≃ₗ[ZMod 2] V', (∀ x y, B' (a x) (a y) = B x y) ∧ ∀ g u, a (σ g u) = σ' g (a u) := by
  have hΦ : Function.Surjective (Phi σ v) := Phi_surjective σ v hS hv hv0
  have hΦ' : Function.Surjective (Phi σ' v') := Phi_surjective σ' v' hS' hv' hv0'
  have hker : LinearMap.ker (Phi σ v) = LinearMap.ker (Phi σ' v') := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.mem_ker,
      Phi_eq_zero_iff σ B v hS hF hv hv0 c,
      Phi_eq_zero_iff σ' B' v' hS' hF' hv' hv0' c]
    simp only [hf]
  let a : V ≃ₗ[ZMod 2] V' :=
    ((Phi σ v).quotKerEquivOfSurjective hΦ).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans
        ((Phi σ' v').quotKerEquivOfSurjective hΦ'))
  have ha : ∀ c : A5 → ZMod 2, a (Phi σ v c) = Phi σ' v' c := by
    intro c
    change (Phi σ' v').quotKerEquivOfSurjective hΦ'
        ((Submodule.quotEquivOfEq _ _ hker)
          (((Phi σ v).quotKerEquivOfSurjective hΦ).symm (Phi σ v c))) = Phi σ' v' c
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  refine ⟨a, ?_, ?_⟩
  · intro x y
    obtain ⟨c, rfl⟩ := hΦ x
    obtain ⟨c', rfl⟩ := hΦ y
    rw [ha, ha, B_Phi_Phi σ' B' v' hF' c c', B_Phi_Phi σ B v hF c c']
    simp only [hf]
  · rintro ⟨x, y⟩ u
    obtain ⟨c, rfl⟩ := hΦ u
    rw [show σ (x, y) (Phi σ v c) = Phi σ v (fun k => c (x⁻¹ * k * y)) from
          Phi_group σ v hv x y c,
      ha (fun k => c (x⁻¹ * k * y)), ha c,
      show σ' (x, y) (Phi σ' v' c) = Phi σ' v' (fun k => c (x⁻¹ * k * y)) from
          Phi_group σ' v' hv' x y c]

end CFSG.EvenSporadicStandard.HNRecog.ML1
