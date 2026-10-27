module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LinearAlgebra

open Module Submodule
open CFSG.GroupTheory.GLnTwoSplitting

variable {A V : Type*} [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup V] [Module (ZMod 2) V]

private lemma exists_conj_transvection {φ φ' : Dual (ZMod 2) A} {w w' : A}
    (hφ : φ w = 0) (hφ' : φ' w' = 0) (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hφ0 : φ ≠ 0) (hφ'0 : φ' ≠ 0) :
    ∃ h : A ≃ₗ[ZMod 2] A, h w = w' ∧
      h * LinearEquiv.transvection hφ * h⁻¹ = LinearEquiv.transvection hφ' := by
  classical
  obtain ⟨χ₁, k₁, hχ₁, h₁eq⟩ := exists_transvection_apply_eq hw hw'
  let h1 : A ≃ₗ[ZMod 2] A := LinearEquiv.transvection hχ₁
  have hh1 : h1 w = w' := h₁eq
  let ψ : Dual (ZMod 2) A := φ.comp (h1.symm : A →ₗ[ZMod 2] A)
  have h1symm : h1.symm w' = w := by
    rw [← hh1, LinearEquiv.symm_apply_apply]
  have hψw' : ψ w' = 0 := by
    simp [ψ, h1symm, hφ]
  have hψ0 : ψ ≠ 0 := by
    intro h
    apply hφ0
    ext x
    have := congrArg (fun f : Dual (ZMod 2) A => f (h1 x)) h
    simpa [ψ] using this
  obtain ⟨g, hgw', hgcomp⟩ := exists_comp_eq_of_apply_eq_zero hψ0 hφ'0 hψw' hφ'
  let h : A ≃ₗ[ZMod 2] A := g⁻¹ * h1
  have hgw'inv : g⁻¹ w' = w' := by
    calc
      g⁻¹ w' = g⁻¹ (g w') := by rw [hgw']
      _ = w' := LinearEquiv.symm_apply_apply g w'
  have hhw : h w = w' := by
    simp only [h, LinearEquiv.mul_apply, hh1, hgw'inv]
  refine ⟨h, ?_, ?_⟩
  · exact hhw
  have hhcomp : φ.comp ((h.symm).toLinearMap) = φ' := by
    apply LinearMap.ext
    intro x
    change φ (h1.symm (g x)) = φ' x
    have hh := congrArg (fun f : Dual (ZMod 2) A => f x) hgcomp
    simpa [ψ, LinearMap.comp_apply] using hh
  have h' : (φ.comp ((h.symm).toLinearMap)) (h w) = 0 := by
    rw [hhw, hhcomp]
    exact hφ'
  have hmain := mul_transvection_mul_inv (g := h) (f := φ) (d := w) hφ h'
  rw [hmain]
  apply LinearEquiv.ext
  intro x
  rw [transvection_apply h', transvection_apply hφ', hhcomp, hhw]

private theorem exists_transvection_of_finrank_ker [FiniteDimensional (ZMod 2) A]
    (hA : finrank (ZMod 2) A = 4) (e : A ≃ₗ[ZMod 2] A)
    (he : finrank (ZMod 2) (LinearMap.ker ((e : A →ₗ[ZMod 2] A) - LinearMap.id)) = 3) :
    ∃ (f : Dual (ZMod 2) A) (v : A) (hfv : f v = 0),
      e = LinearEquiv.transvection hfv ∧ f ≠ 0 ∧ v ≠ 0 ∧
      LinearMap.ker ((e : A →ₗ[ZMod 2] A) - LinearMap.id) = LinearMap.ker f ∧
      LinearMap.range ((e : A →ₗ[ZMod 2] A) - LinearMap.id) = Submodule.span (ZMod 2) {v} := by
  classical
  let δ : A →ₗ[ZMod 2] A := (e : A →ₗ[ZMod 2] A)
  have hrank : finrank (ZMod 2) (LinearMap.range (δ - LinearMap.id)) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (δ - LinearMap.id)
    rw [hA, he] at h
    omega
  have hmem : e ∈ LinearEquiv.dilatransvections (ZMod 2) A := by
    rw [LinearEquiv.mem_dilatransvections_iff_finrank]
    exact hrank.le
  obtain ⟨f, v, hev⟩ := hmem
  have hfv : f v = 0 := by
    rcases zmod_two_eq_zero_or_one (f v) with h | h
    · exact h
    · exfalso
      have hv0 : v = 0 := e.injective (by
        change (e : A →ₗ[ZMod 2] A) v = e 0
        rw [hev, LinearMap.transvection.apply, h, one_smul, two_add_self]
        rw [map_zero])
      rw [hv0, map_zero] at h
      exact zero_ne_one h
  let t : A ≃ₗ[ZMod 2] A := LinearEquiv.transvection hfv
  have ht : t = e := by
    apply LinearEquiv.ext
    intro x
    change LinearEquiv.transvection hfv x = e x
    rw [show e x = LinearMap.transvection f v x by
      change (e : A →ₗ[ZMod 2] A) x = LinearMap.transvection f v x
      rw [hev]]
    rfl
  have ht_sq : t * t = 1 := transvection_mul_self hfv
  have hv : v ≠ 0 := by
    intro hv0
    have hδ1 : t = 1 := by
      apply LinearEquiv.ext
      intro y
      change LinearEquiv.transvection hfv y = y
      rw [show LinearEquiv.transvection hfv y = LinearMap.transvection f v y from rfl, hv0]
      simp
    have hfin : finrank (ZMod 2) (LinearMap.ker ((e : A →ₗ[ZMod 2] A) - LinearMap.id)) =
        finrank (ZMod 2) A := by
      rw [show (e : A →ₗ[ZMod 2] A) = (t : A →ₗ[ZMod 2] A) by rw [ht], hδ1]
      have hzero : ((1 : A ≃ₗ[ZMod 2] A) : A →ₗ[ZMod 2] A) - LinearMap.id = 0 := by
        ext y
        simp
      rw [hzero]
      have hker0 : LinearMap.ker (0 : A →ₗ[ZMod 2] A) = ⊤ := by
        ext x
        simp
      rw [hker0]
      exact finrank_top _ _
    rw [hfin, hA] at he
    omega
  have hf : f ≠ 0 := by
    intro hf0
    have hδ1 : t = 1 := by
      apply LinearEquiv.ext
      intro y
      change LinearEquiv.transvection hfv y = y
      rw [show LinearEquiv.transvection hfv y = LinearMap.transvection f v y from rfl, hf0]
      simp
    have hfin : finrank (ZMod 2) (LinearMap.ker ((e : A →ₗ[ZMod 2] A) - LinearMap.id)) =
        finrank (ZMod 2) A := by
      rw [show (e : A →ₗ[ZMod 2] A) = (t : A →ₗ[ZMod 2] A) by rw [ht], hδ1]
      have hzero : ((1 : A ≃ₗ[ZMod 2] A) : A →ₗ[ZMod 2] A) - LinearMap.id = 0 := by
        ext y
        simp
      rw [hzero]
      have hker0 : LinearMap.ker (0 : A →ₗ[ZMod 2] A) = ⊤ := by
        ext x
        simp
      rw [hker0]
      exact finrank_top _ _
    rw [hfin, hA] at he
    omega
  have hker : LinearMap.ker (δ - LinearMap.id) = LinearMap.ker f := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    rw [show δ x = x + f x • v by
      change (e : A →ₗ[ZMod 2] A) x = x + f x • v
      rw [hev]
      rfl]
    constructor
    · intro hx
      have hx' : f x • v = 0 := by simpa using hx
      exact (smul_eq_zero.1 hx').resolve_right hv
    · intro hx
      rw [LinearMap.mem_ker] at hx
      rw [hx, zero_smul, add_zero, sub_self]
  have hrange : LinearMap.range (δ - LinearMap.id) = Submodule.span (ZMod 2) {v} := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [LinearMap.sub_apply, LinearMap.id_apply]
      rw [show δ x = x + f x • v by
        change (e : A →ₗ[ZMod 2] A) x = x + f x • v
        rw [hev]
        rfl]
      rw [add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [Submodule.span_singleton_le_iff_mem]
      obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
        by_contra h
        push Not at h
        exact hf (LinearMap.ext h)
      have hx1 : f x = 1 := zmod_two_eq_one_of_ne_zero hx
      refine ⟨x, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.id_apply]
      rw [show δ x = x + f x • v by
        change (e : A →ₗ[ZMod 2] A) x = x + f x • v
        rw [hev]
        rfl]
      rw [hx1, one_smul, add_sub_cancel_left]
  exact ⟨f, v, hfv, ht.symm, hf, hv, hker, hrange⟩

private noncomputable def linSec (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ) :
    A →ₗ[ZMod 2] V :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective θ (LinearMap.range_eq_top.mpr hθ))

private lemma linSec_theta (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ) (a : A) :
    θ (linSec θ hθ a) = a := by
  have h := Classical.choose_spec
    (LinearMap.exists_rightInverse_of_surjective θ (LinearMap.range_eq_top.mpr hθ))
  have h' := congrArg (fun f : A →ₗ[ZMod 2] A => f a) h
  simpa [linSec] using h'

private lemma theta_iota (ι : A →ₗ[ZMod 2] V) (θ : V →ₗ[ZMod 2] A)
    (hexact : LinearMap.range ι = LinearMap.ker θ) (a : A) : θ (ι a) = 0 := by
  have h : ι a ∈ LinearMap.range ι := LinearMap.mem_range_self ι a
  rw [hexact] at h
  exact h

private noncomputable def iotaProj (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ) : V →ₗ[ZMod 2] A :=
  (LinearEquiv.ofInjective ι hι).symm.toLinearMap.comp
    (LinearMap.codRestrict (LinearMap.range ι)
      (LinearMap.id - (linSec θ hθ).comp θ) (by
        intro v
        change v - linSec θ hθ (θ v) ∈ LinearMap.range ι
        rw [hexact]
        rw [LinearMap.mem_ker]
        rw [map_sub, linSec_theta, sub_self]))

private lemma iotaProj_apply (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ) (v : V) :
    ι (iotaProj ι hι θ hθ hexact v) = v - linSec θ hθ (θ v) := by
  unfold iotaProj
  change ι ((LinearEquiv.ofInjective ι hι).symm
    ⟨v - linSec θ hθ (θ v), _⟩) = v - linSec θ hθ (θ v)
  rw [LinearEquiv.ofInjective_symm_apply]

private noncomputable def cocycle (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (g : Γ) : A →ₗ[ZMod 2] A :=
  (iotaProj ι hι θ hθ hexact).comp
    (((ρ g).toLinearMap.comp (linSec θ hθ)) -
      ((linSec θ hθ).comp ((π g).toLinearMap)))

private lemma iota_cocycle (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v)) (g : Γ) (a : A) :
    ι (cocycle ι hι θ hθ hexact π ρ g a) =
      ρ g (linSec θ hθ a) - linSec θ hθ (π g a) := by
  unfold cocycle
  rw [LinearMap.comp_apply]
  change ι (iotaProj ι hι θ hθ hexact
    (ρ g (linSec θ hθ a) - linSec θ hθ (π g a))) =
      ρ g (linSec θ hθ a) - linSec θ hθ (π g a)
  rw [iotaProj_apply]
  have hθzero : θ (ρ g (linSec θ hθ a) - linSec θ hθ (π g a)) = 0 := by
    rw [map_sub, hρθ, linSec_theta, linSec_theta, sub_self]
  rw [hθzero, map_zero, sub_zero]

private lemma cocycle_mul (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v)) (g h : Γ) :
    cocycle ι hι θ hθ hexact π ρ (g * h) =
      (cocycle ι hι θ hθ hexact π ρ g).comp ((π h).toLinearMap) +
        ((π g).toLinearMap).comp (cocycle ι hι θ hθ hexact π ρ h) := by
  apply LinearMap.ext
  intro a
  apply hι
  rw [iota_cocycle ι hι θ hθ hexact π ρ hρθ]
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [map_add]
  rw [iota_cocycle ι hι θ hθ hexact π ρ hρθ]
  have hh : ι (((π g).toLinearMap) (cocycle ι hι θ hθ hexact π ρ h a)) =
      (ρ g) (ι (cocycle ι hι θ hθ hexact π ρ h a)) := by
    simpa using (hρι g (cocycle ι hι θ hθ hexact π ρ h a)).symm
  rw [hh]
  rw [iota_cocycle ι hι θ hθ hexact π ρ hρθ]
  rw [map_sub]
  rw [map_mul, map_mul]
  simp only [LinearEquiv.mul_apply]
  simp only [two_sub]
  change (ρ g) ((ρ h) (linSec θ hθ a)) + (linSec θ hθ) ((π g) ((π h) a)) =
    (ρ g) ((linSec θ hθ) ((π h) a)) + (linSec θ hθ) ((π g) ((π h) a)) +
      ((ρ g) ((ρ h) (linSec θ hθ a)) + (ρ g) ((linSec θ hθ) ((π h) a)))
  have hYZ : ∀ X Y Z : V, (Y + Z) + (X + Y) = X + Z := by
    intro X Y Z
    rw [add_comm (Y + Z) (X + Y), add_assoc X Y (Y + Z), ← add_assoc Y Y Z,
      two_add_self, zero_add]
  rw [hYZ]

private lemma cocycle_one (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v)) :
    cocycle ι hι θ hθ hexact π ρ (1 : Γ) = 0 := by
  apply LinearMap.ext
  intro a
  apply hι
  rw [iota_cocycle ι hι θ hθ hexact π ρ hρθ]
  simp [map_one]

private lemma cocycle_eq_zero_of_pi_eq_one (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1) {g : Γ} (h : π g = 1) :
    cocycle ι hι θ hθ hexact π ρ g = 0 := by
  apply LinearMap.ext
  intro a
  apply hι
  rw [iota_cocycle ι hι θ hθ hexact π ρ hρθ, h, hker g h]
  simp

private lemma cocycle_eq_of_pi_eq (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1) {g g' : Γ} (h : π g = π g') :
    cocycle ι hι θ hθ hexact π ρ g =
      cocycle ι hι θ hθ hexact π ρ g' := by
  have hρ : ρ g = ρ g' := by
    have h1 : π (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : ρ (g⁻¹ * g') = 1 := hker _ h1
    rw [map_mul, map_inv] at h2
    exact eq_of_inv_mul_eq_one h2
  apply LinearMap.ext
  intro a
  apply hι
  rw [iota_cocycle ι hι θ hθ hexact π ρ hρθ,
    iota_cocycle ι hι θ hθ hexact π ρ hρθ, hρ, h]

private lemma cocycle_commute_of_sq (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1) {g : Γ} (h : π (g * g) = 1) :
    (cocycle ι hι θ hθ hexact π ρ g).comp ((π g).toLinearMap) =
      ((π g).toLinearMap).comp (cocycle ι hι θ hθ hexact π ρ g) := by
  have hz := cocycle_eq_zero_of_pi_eq_one ι hι θ hθ hexact π ρ hρθ hker h
  have hsum : (cocycle ι hι θ hθ hexact π ρ g).comp ((π g).toLinearMap) +
      ((π g).toLinearMap).comp (cocycle ι hι θ hθ hexact π ρ g) = 0 := by
    rw [← cocycle_mul ι hι θ hθ hexact π ρ hρι hρθ g g]
    exact hz
  have hbb : ((π g).toLinearMap).comp (cocycle ι hι θ hθ hexact π ρ g) +
      ((π g).toLinearMap).comp (cocycle ι hι θ hθ hexact π ρ g) = 0 :=
    two_add_self _
  have : (cocycle ι hι θ hθ hexact π ρ g).comp ((π g).toLinearMap) +
      ((π g).toLinearMap).comp (cocycle ι hι θ hθ hexact π ρ g) =
      ((π g).toLinearMap).comp (cocycle ι hι θ hθ hexact π ρ g) +
        ((π g).toLinearMap).comp (cocycle ι hι θ hθ hexact π ρ g) := by
    rw [hsum, hbb]
  exact add_right_cancel this

private lemma cocycle_mul_apply_aux (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v)) (g h : Γ) (x : A) :
    cocycle ι hι θ hθ hexact π ρ (g * h) x =
      cocycle ι hι θ hθ hexact π ρ g (((π h).toLinearMap) x) +
        ((π g).toLinearMap) (cocycle ι hι θ hθ hexact π ρ h x) := by
  have h := congrArg (fun L : A →ₗ[ZMod 2] A => L x)
    (cocycle_mul ι hι θ hθ hexact π ρ hρι hρθ g h)
  simpa only [LinearMap.add_apply, LinearMap.comp_apply] using h

private lemma cocycle_mul_apply (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v)) (g h : Γ) (x : A) :
    cocycle ι hι θ hθ hexact π ρ (g * h) x =
      cocycle ι hι θ hθ hexact π ρ g ((π h) x) +
        (π g) (cocycle ι hι θ hθ hexact π ρ h x) := by
  simpa only [LinearEquiv.coe_toLinearMap] using
    cocycle_mul_apply_aux ι hι θ hθ hexact π ρ hρι hρθ g h x

private lemma cocycle_inv_apply (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1) (g : Γ) (x : A) :
    (π g) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) x)) =
      (cocycle ι hι θ hθ hexact π ρ g x) := by
  have h0 : π (g * g⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
  have hz := cocycle_eq_zero_of_pi_eq_one ι hι θ hθ hexact π ρ hρθ hker h0
  have h := cocycle_mul_apply ι hι θ hθ hexact π ρ hρι hρθ g g⁻¹ ((π g) x)
  rw [mul_inv_cancel] at h
  rw [cocycle_one ι hι θ hθ hexact π ρ hρθ] at h
  simp only [LinearMap.zero_apply] at h
  have hx : ((π g⁻¹) ((π g) x)) = x := by
    rw [map_inv]
    exact LinearEquiv.symm_apply_apply (π g) x
  rw [hx] at h
  have h' : cocycle ι hι θ hθ hexact π ρ g x +
      (π g) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) x)) = 0 := by
    simpa [add_comm] using h.symm
  calc
    (π g) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) x)) =
        ((π g) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) x)) +
          cocycle ι hι θ hθ hexact π ρ g x) + cocycle ι hι θ hθ hexact π ρ g x := by
          rw [add_assoc, two_add_self, add_zero]
    _ = 0 + cocycle ι hι θ hθ hexact π ρ g x := by
      rw [add_comm ((π g) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) x)))
        (cocycle ι hι θ hθ hexact π ρ g x), h']
    _ = cocycle ι hι θ hθ hexact π ρ g x := zero_add _

private lemma cocycle_conj_apply
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1)
    (γ : Γ) {v : A}
    (hrange : LinearMap.range ((π γ).toLinearMap - LinearMap.id) =
      Submodule.span (ZMod 2) {v}) (g : Γ) {a : A}
    (ha : a ∈ LinearMap.ker ((π γ).toLinearMap - LinearMap.id)) :
    ∃ μ : ZMod 2,
      cocycle ι hι θ hθ hexact π ρ (g * γ * g⁻¹) ((π g) a) =
        (π g) (cocycle ι hι θ hθ hexact π ρ γ a) + μ • ((π g) v) := by
  classical
  have ha' : (π γ) a = a := by
    have h := ha
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h
    exact sub_eq_zero.mp h
  have hπgi : ((π g⁻¹) ((π g) a)) = a := by
    rw [map_inv]
    exact LinearEquiv.symm_apply_apply (π g) a
  have h1 : cocycle ι hι θ hθ hexact π ρ (g * γ * g⁻¹) ((π g) a) =
      cocycle ι hι θ hθ hexact π ρ g
          ((π (γ * g⁻¹)) ((π g) a)) +
        (π g) (cocycle ι hι θ hθ hexact π ρ (γ * g⁻¹) ((π g) a)) := by
    rw [show g * γ * g⁻¹ = g * (γ * g⁻¹) by group]
    exact cocycle_mul_apply ι hι θ hθ hexact π ρ hρι hρθ g (γ * g⁻¹) ((π g) a)
  have h2 : cocycle ι hι θ hθ hexact π ρ (γ * g⁻¹) ((π g) a) =
      cocycle ι hι θ hθ hexact π ρ γ ((π g⁻¹) ((π g) a)) +
        (π γ) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) a)) :=
    cocycle_mul_apply ι hι θ hθ hexact π ρ hρι hρθ γ g⁻¹ ((π g) a)
  have hπγg : ((π (γ * g⁻¹)) ((π g) a)) = a := by
    rw [map_mul]
    simp only [LinearEquiv.mul_apply, hπgi, ha']
  have hcgi : (π g) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) a)) =
      cocycle ι hι θ hθ hexact π ρ g a :=
    cocycle_inv_apply ι hι θ hθ hexact π ρ hρι hρθ hker g a
  have hmem : ((π γ) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) a)) -
      cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) a)) ∈
      Submodule.span (ZMod 2) {v} := by
    rw [← hrange]
    exact ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨μ, ?_⟩
  calc
    cocycle ι hι θ hθ hexact π ρ (g * γ * g⁻¹) ((π g) a)
        = cocycle ι hι θ hθ hexact π ρ g a +
            (π g) (cocycle ι hι θ hθ hexact π ρ γ a +
              (π γ) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) a))) := by
          rw [h1, h2, hπγg, hπgi]
    _ = (π g) (cocycle ι hι θ hθ hexact π ρ γ a) +
          (π g) (((π γ) (cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) a)) -
            cocycle ι hι θ hθ hexact π ρ g⁻¹ ((π g) a))) := by
          rw [← hcgi]
          rw [map_add, map_sub]
          rw [two_sub]
          abel
    _ = (π g) (cocycle ι hι θ hθ hexact π ρ γ a) +
          (π g) (μ • v) := by rw [hμ]
    _ = (π g) (cocycle ι hι θ hθ hexact π ρ γ a) + μ • ((π g) v) := by
          rw [map_smul]

private lemma end_eq_zero_or_one_of_preserves_lines
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (hE : finrank (ZMod 2) E = 2) (T : E →ₗ[ZMod 2] E)
    (hT : ∀ x : E, x ≠ 0 → ∃ mu : ZMod 2, T x = mu • x) :
    T = 0 ∨ T = 1 := by
  classical
  let b : Basis (Fin 2) (ZMod 2) E := Module.finBasisOfFinrankEq (ZMod 2) E hE
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  have hb1 : b 1 ≠ 0 := b.ne_zero 1
  have hs01 : b 0 + b 1 ≠ 0 := by
    intro h
    have hli := (Fintype.linearIndependent_iff.1 b.linearIndependent) ![1, 1]
    have hsum : (∑ i, (![1, 1] : Fin 2 → ZMod 2) i • ![b 0, b 1] i) = 0 := by
      rw [Fin.sum_univ_two]
      simpa using h
    have hcoef := hli hsum
    have h0 := hcoef 0
    norm_num at h0
  obtain ⟨l0, h0⟩ := hT (b 0) hb0
  obtain ⟨l1, h1⟩ := hT (b 1) hb1
  obtain ⟨l2, h2⟩ := hT (b 0 + b 1) hs01
  have hsum : l0 • b 0 + l1 • b 1 = l2 • b 0 + l2 • b 1 := by
    calc
      l0 • b 0 + l1 • b 1 = T (b 0) + T (b 1) := by rw [h0, h1]
      _ = T (b 0 + b 1) := (map_add T (b 0) (b 1)).symm
      _ = l2 • (b 0 + b 1) := h2
      _ = l2 • b 0 + l2 • b 1 := smul_add l2 (b 0) (b 1)
  have hc0 := congrArg (fun x => b.repr x 0) hsum
  have hc1 := congrArg (fun x => b.repr x 1) hsum
  simp only [map_add, map_smul, Module.Basis.repr_self_apply, smul_eq_mul] at hc0 hc1
  norm_num at hc0 hc1
  have hl0 : l0 = l2 := hc0
  have hl1 : l1 = l2 := hc1
  have hl2 : l2 = l0 := hl0.symm
  have hT' : T = l0 • (1 : E →ₗ[ZMod 2] E) := by
    ext x
    have hx : x = b.repr x 0 • b 0 + b.repr x 1 • b 1 := by
      conv_lhs => rw [← b.sum_repr x]
      rw [Fin.sum_univ_two]
    calc
      T x = T ((b.repr x 0) • b 0 + (b.repr x 1) • b 1) := congrArg T hx
      _ = (b.repr x 0) • T (b 0) + (b.repr x 1) • T (b 1) := by simp
      _ = (b.repr x 0) • (l0 • b 0) + (b.repr x 1) • (l0 • b 1) := by
        rw [h0, h1, hl1, hl2]
      _ = l0 • ((b.repr x 0) • b 0 + (b.repr x 1) • b 1) := by module
      _ = l0 • x := congrArg (fun y => l0 • y) hx.symm
      _ = (l0 • (1 : E →ₗ[ZMod 2] E)) x := by
        simp
  rcases zmod_two_eq_zero_or_one l0 with rfl | rfl
  · left
    rw [hT']
    simp
  · right
    rw [hT']
    simp

private lemma cocycle_preserves_line
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hπ : Function.Surjective π)
    (γ : Γ) {φ : Dual (ZMod 2) A} {v : A} (hφv : φ v = 0)
    (hπγ : π γ = LinearEquiv.transvection hφv)
    (hconj : ∀ (h : Γ), π h * π γ = π γ * π h → ∀ y ∈ LinearMap.ker
      ((π γ).toLinearMap - LinearMap.id),
      cocycle ι hι θ hθ hexact π ρ γ ((π h) y) -
        (π h) (cocycle ι hι θ hθ hexact π ρ γ y) ∈
        Submodule.span (ZMod 2) {v})
    {a : A} (haK : a ∈ LinearMap.ker φ) (haW : a ∉ Submodule.span (ZMod 2) {v}) :
    cocycle ι hι θ hθ hexact π ρ γ a ∈
      Submodule.span (ZMod 2) ({v, a} : Set A) := by
  by_contra hca
  obtain ⟨ψ, hψS, hψca⟩ := exists_dual_eq_one_of_notMem (S :=
    Submodule.span (ZMod 2) ({v, a} : Set A)) hca
  have hψv : ψ v = 0 := hψS v (Submodule.subset_span (by simp))
  have hψa : ψ a = 0 := hψS a (Submodule.subset_span (by simp))
  have hφa : φ a = 0 := by
    have := haK
    rwa [LinearMap.mem_ker] at this
  let P : A ≃ₗ[ZMod 2] A := LinearEquiv.transvection hψa
  have hPcomm : P * π γ = π γ * P := by
    rw [hπγ]
    exact transvection_commute hψa hφv hψv hφa
  obtain ⟨h, hh⟩ := hπ P
  have hcomm : π h * π γ = π γ * π h := by rw [hh]; exact hPcomm
  have hδa : (π γ) a = a := by
    rw [hπγ]
    change LinearEquiv.transvection hφv a = a
    rw [transvection_apply hφv, hφa, zero_smul, add_zero]
  have hmem : a ∈ LinearMap.ker ((π γ).toLinearMap - LinearMap.id) := by
    rw [LinearMap.mem_ker]
    change (π γ) a - a = 0
    rw [hδa, sub_self]
  have hconj' := hconj h hcomm a hmem
  have hPa : P a = a := by
    change LinearEquiv.transvection hψa a = a
    rw [transvection_apply hψa, hψa, zero_smul, add_zero]
  have hPca : P (cocycle ι hι θ hθ hexact π ρ γ a) =
      cocycle ι hι θ hθ hexact π ρ γ a + a := by
    change LinearEquiv.transvection hψa (cocycle ι hι θ hθ hexact π ρ γ a) = _
    rw [transvection_apply hψa, hψca, one_smul]
  have hconj'' : cocycle ι hι θ hθ hexact π ρ γ a -
      P (cocycle ι hι θ hθ hexact π ρ γ a) ∈ Submodule.span (ZMod 2) {v} := by
    have := hconj'
    rw [hh] at this
    simpa [hPa] using this
  have : a ∈ Submodule.span (ZMod 2) {v} := by
    have h := hconj''
    have hsub : cocycle ι hι θ hθ hexact π ρ γ a -
        P (cocycle ι hι θ hθ hexact π ρ γ a) = a := by
      rw [hPca]
      have h : cocycle ι hι θ hθ hexact π ρ γ a -
          (cocycle ι hι θ hθ hexact π ρ γ a + a) =
          cocycle ι hι θ hθ hexact π ρ γ a -
            cocycle ι hι θ hθ hexact π ρ γ a - a := by abel
      rw [h, sub_self, zero_sub, two_neg]
    rwa [hsub] at h
  exact haW this

private lemma cocycle_dichotomy [FiniteDimensional (ZMod 2) A]
    (c : A →ₗ[ZMod 2] A) {φ : Dual (ZMod 2) A} {v : A} (hφv : φ v = 0) (hv : v ≠ 0)
    (hK : finrank (ZMod 2) (LinearMap.ker φ) = 3)
    (hcK : ∀ x ∈ LinearMap.ker φ, c x ∈ LinearMap.ker φ)
    (hcW : ∀ x ∈ Submodule.span (ZMod 2) {v}, c x ∈ Submodule.span (ZMod 2) {v})
    (hline : ∀ x ∈ LinearMap.ker φ, x ∉ Submodule.span (ZMod 2) {v} →
      c x ∈ Submodule.span (ZMod 2) ({v, x} : Set A)) :
    (∀ x ∈ LinearMap.ker φ, c x ∈ Submodule.span (ZMod 2) {v}) ∨
      (∀ x ∈ LinearMap.ker φ, c x - x ∈ Submodule.span (ZMod 2) {v}) := by
  classical
  let K : Submodule (ZMod 2) A := LinearMap.ker φ
  let W : Submodule (ZMod 2) A := Submodule.span (ZMod 2) {v}
  have hWK : W ≤ K := by
    intro x hx
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_smul, hφv, smul_zero]
  let cK : K →ₗ[ZMod 2] K :=
    LinearMap.codRestrict K (c.comp K.subtype) (by
      intro x
      exact hcK x.1 x.2)
  let WK : Submodule (ZMod 2) K := W.comap K.subtype
  have hcWK : ∀ x ∈ WK, cK x ∈ WK := by
    intro x hx
    change c (x : A) ∈ W
    exact hcW x.1 hx
  let T : K ⧸ WK →ₗ[ZMod 2] K ⧸ WK :=
    Submodule.mapQ WK WK cK (by
      intro x hx
      exact hcWK x hx)
  have hfinW : finrank (ZMod 2) W = 1 := by
    rw [finrank_span_singleton hv]
  have hfinWK : finrank (ZMod 2) WK = 1 := by
    exact (Submodule.comapSubtypeEquivOfLe hWK).finrank_eq.trans hfinW
  haveI : Module.Finite (ZMod 2) K :=
    FiniteDimensional.finiteDimensional_submodule K
  have hdim : finrank (ZMod 2) (K ⧸ WK) = 2 := by
    have h := Submodule.finrank_quotient_add_finrank WK
    rw [hfinWK, hK] at h
    omega
  have hT : ∀ z : K ⧸ WK, z ≠ 0 → ∃ mu : ZMod 2, T z = mu • z := by
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | _ x =>
      by_cases hxW : (x : A) ∈ W
      · have hxWK : x ∈ WK := hxW
        have hzero : Submodule.Quotient.mk x = (0 : K ⧸ WK) :=
          (Submodule.Quotient.mk_eq_zero WK).mpr hxWK
        exact absurd hzero hz
      · have hxK : (x : A) ∈ K := x.2
        have hxW' : (x : A) ∉ Submodule.span (ZMod 2) {v} := hxW
        obtain ⟨α, β, hc⟩ := Submodule.mem_span_pair.1 (hline (x : A) hxK hxW')
        refine ⟨β, ?_⟩
        have hTapply : T (Submodule.Quotient.mk x) =
            Submodule.Quotient.mk (cK x) := by
          rw [show T = Submodule.mapQ WK WK cK _ from rfl]
          exact Submodule.mapQ_apply _ _ _ _
        rw [hTapply]
        have hdiff : cK x - β • x ∈ WK := by
          change c (x : A) - β • (x : A) ∈ W
          rw [← hc]
          rw [add_sub_cancel_right]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        have hzero : Submodule.Quotient.mk (cK x - β • x) = 0 :=
          (Submodule.Quotient.mk_eq_zero WK).mpr hdiff
        rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul] at hzero
        rw [sub_eq_zero] at hzero
        exact hzero
  obtain hT0 | hT1 := end_eq_zero_or_one_of_preserves_lines hdim T hT
  · left
    intro x hx
    have hxK : x ∈ K := hx
    have hTx : T (Submodule.Quotient.mk (⟨x, hxK⟩ : K)) = 0 := by
      rw [hT0]; rfl
    have hTapply : T (Submodule.Quotient.mk (⟨x, hxK⟩ : K)) =
        Submodule.Quotient.mk (cK ⟨x, hxK⟩) := by
      rw [show T = Submodule.mapQ WK WK cK _ from rfl]
      exact Submodule.mapQ_apply _ _ _ _
    rw [hTapply] at hTx
    have : cK ⟨x, hxK⟩ ∈ WK := (Submodule.Quotient.mk_eq_zero WK).mp hTx
    change c x ∈ W
    exact this
  · right
    intro x hx
    have hxK : x ∈ K := hx
    have hTx : T (Submodule.Quotient.mk (⟨x, hxK⟩ : K)) =
        Submodule.Quotient.mk (⟨x, hxK⟩ : K) := by
      rw [hT1]; rfl
    have hTapply : T (Submodule.Quotient.mk (⟨x, hxK⟩ : K)) =
        Submodule.Quotient.mk (cK ⟨x, hxK⟩) := by
      rw [show T = Submodule.mapQ WK WK cK _ from rfl]
      exact Submodule.mapQ_apply _ _ _ _
    rw [hTapply] at hTx
    have : cK ⟨x, hxK⟩ - ⟨x, hxK⟩ ∈ WK := by
      have hzero : Submodule.Quotient.mk (p := WK)
          (cK ⟨x, hxK⟩ - ⟨x, hxK⟩) = 0 := by
        rw [Submodule.Quotient.mk_sub (p := WK), hTx, sub_self]
      exact (Submodule.Quotient.mk_eq_zero WK).mp hzero
    change c x - x ∈ W
    exact this

private lemma cocycle_conj_mod_center
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1)
    (γ h : Γ) {f : Dual (ZMod 2) A} {v : A} (hfv : f v = 0)
    (hπγ : π γ = LinearEquiv.transvection hfv)
    (hrange : LinearMap.range ((π γ).toLinearMap - (1 : A →ₗ[ZMod 2] A)) =
      Submodule.span (ZMod 2) {v})
    (hcomm : π h * π γ = π γ * π h) {y : A}
    (hy : y ∈ LinearMap.ker ((π γ).toLinearMap - (1 : A →ₗ[ZMod 2] A))) :
    cocycle ι hι θ hθ hexact π ρ γ ((π h) y) -
      (π h) (cocycle ι hι θ hθ hexact π ρ γ y) ∈
      Submodule.span (ZMod 2) {v} := by
  classical
  have hpi : π (h * γ * h⁻¹) = π γ := by
    rw [map_mul, map_mul, map_inv, hπγ]
    have hc := hcomm
    rw [hπγ] at hc
    rw [hc]
    group
  obtain ⟨mu, hmu⟩ := cocycle_conj_apply (ι := ι) (hι := hι) (θ := θ) (hθ := hθ)
    (hexact := hexact) (π := π) (ρ := ρ) (hρι := hρι) (hρθ := hρθ) (hker := hker)
    (γ := γ) (hrange := hrange) (g := h) (a := y) (ha := hy)
  rw [cocycle_eq_of_pi_eq ι hι θ hθ hexact π ρ hρθ hker hpi] at hmu
  have hv_mem : v ∈ LinearMap.range ((π γ).toLinearMap - (1 : A →ₗ[ZMod 2] A)) := by
    rw [hrange]
    exact Submodule.subset_span (by simp)
  obtain ⟨z, hz⟩ := hv_mem
  have hPδ : (π h) ((π γ) z) = (π γ) ((π h) z) := by
    rw [← LinearEquiv.mul_apply, hcomm, LinearEquiv.mul_apply]
  have hPv_eq : (π h) v = ((π γ).toLinearMap - (1 : A →ₗ[ZMod 2] A)) ((π h) z) := by
    calc
      (π h) v = (π h) (((π γ).toLinearMap - (1 : A →ₗ[ZMod 2] A)) z) := by rw [hz]
      _ = (π h) ((π γ) z) - (π h) z := by
        simp [LinearMap.sub_apply]
      _ = (π γ) ((π h) z) - (π h) z := by rw [hPδ]
      _ = ((π γ).toLinearMap - (1 : A →ₗ[ZMod 2] A)) ((π h) z) := by
        simp [LinearMap.sub_apply]
  have hPv : (π h) v ∈ Submodule.span (ZMod 2) {v} := by
    rw [← hrange]
    exact ⟨(π h) z, hPv_eq.symm⟩
  rw [hmu]
  rw [add_sub_cancel_left]
  exact Submodule.smul_mem _ _ hPv

private lemma cocycle_alt_one_conj
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1)
    (γ : Γ) {φ : Dual (ZMod 2) A} {v : A}
    (hkerφ : LinearMap.ker ((π γ).toLinearMap - (1 : A →ₗ[ZMod 2] A)) =
      LinearMap.ker φ)
    (hrange : LinearMap.range ((π γ).toLinearMap - (1 : A →ₗ[ZMod 2] A)) =
      Submodule.span (ZMod 2) {v})
    (hone : ∀ x ∈ LinearMap.ker φ,
      cocycle ι hι θ hθ hexact π ρ γ x - x ∈ Submodule.span (ZMod 2) {v})
    (h : Γ) {φ' : Dual (ZMod 2) A} {v' : A} (hφ' : φ' v' = 0)
    (hπh : π (h * γ * h⁻¹) = LinearEquiv.transvection hφ')
    (hPv : (π h) v = v') :
    ∀ x ∈ LinearMap.ker φ',
      cocycle ι hι θ hθ hexact π ρ (h * γ * h⁻¹) x - x ∈
        Submodule.span (ZMod 2) {v'} := by
  classical
  intro x hx
  let P : A ≃ₗ[ZMod 2] A := π h
  let y : A := P.symm x
  have hPy : P y = x := P.apply_symm_apply x
  have hxfix : (LinearEquiv.transvection hφ') x = x := by
    rw [transvection_apply hφ']
    have hx' : φ' x = 0 := hx
    rw [hx', zero_smul, add_zero]
  have hPγ : P * π γ = π (h * γ) := (map_mul π h γ).symm
  have hPform : P * π γ = (π (h * γ * h⁻¹)) * P := by
    calc
      P * π γ = π (h * γ) := hPγ
      _ = π ((h * γ * h⁻¹) * h) := by
        congr 1
        group
      _ = π (h * γ * h⁻¹) * π h := map_mul π _ _
      _ = π (h * γ * h⁻¹) * P := rfl
  have hyfix : (π γ) y = y := by
    apply P.injective
    calc
      P ((π γ) y) = (P * π γ) y := rfl
      _ = ((π (h * γ * h⁻¹)) * P) y := by rw [hPform]
      _ = (LinearEquiv.transvection hφ' * P) y := by rw [hπh]
      _ = (LinearEquiv.transvection hφ') x := by rw [LinearEquiv.mul_apply, hPy]
      _ = x := hxfix
      _ = P y := hPy.symm
  have hy' : y ∈ LinearMap.ker ((π γ).toLinearMap - (1 : A →ₗ[ZMod 2] A)) := by
    rw [LinearMap.mem_ker]
    change (π γ) y - y = 0
    rw [hyfix, sub_self]
  have hyker : y ∈ LinearMap.ker φ := by
    have h := hy'
    rwa [hkerφ] at h
  obtain ⟨μ, hμ⟩ := cocycle_conj_apply (ι := ι) (hι := hι) (θ := θ) (hθ := hθ)
    (hexact := hexact) (π := π) (ρ := ρ) (hρι := hρι) (hρθ := hρθ) (hker := hker)
    (γ := γ) (hrange := hrange) (g := h) (a := y) (ha := hy')
  have hcoe : cocycle ι hι θ hθ hexact π ρ (h * γ * h⁻¹) x =
      P (cocycle ι hι θ hθ hexact π ρ γ y) + μ • v' := by
    rw [hPy, hPv] at hμ
    exact hμ
  have hmem : cocycle ι hι θ hθ hexact π ρ γ y - y ∈ Submodule.span (ZMod 2) {v} :=
    hone y hyker
  have hPmem : P (cocycle ι hι θ hθ hexact π ρ γ y - y) ∈ Submodule.span (ZMod 2) {v'} := by
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨α, hα⟩ := hmem
    rw [← hα, map_smul, hPv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  rw [hcoe]
  rw [show P (cocycle ι hι θ hθ hexact π ρ γ y) + μ • v' - x =
      P (cocycle ι hι θ hθ hexact π ρ γ y - y) + μ • v' by
        rw [← hPy]
        rw [map_sub]
        abel]
  exact Submodule.add_mem _ hPmem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private lemma finrank_ker_eq_three [FiniteDimensional (ZMod 2) A]
    (hA : finrank (ZMod 2) A = 4) {φ : Dual (ZMod 2) A} (hφ : φ ≠ 0) :
    finrank (ZMod 2) (LinearMap.ker φ) = 3 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  rw [hA] at h
  omega

private lemma ker_transvection_sub_id {φ : Dual (ZMod 2) A} {v : A} (hφv : φ v = 0)
    (hv : v ≠ 0) :
    LinearMap.ker ((LinearEquiv.transvection hφv).toLinearMap - LinearMap.id) =
      LinearMap.ker φ := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap, transvection_apply, add_sub_cancel_left]
  constructor
  · intro h
    exact (smul_eq_zero.1 h).resolve_right hv
  · intro h
    rw [h, zero_smul]

private lemma range_transvection_sub_id {φ : Dual (ZMod 2) A} {v : A} (hφv : φ v = 0)
    (hφ : φ ≠ 0) :
    LinearMap.range ((LinearEquiv.transvection hφv).toLinearMap - LinearMap.id) =
      Submodule.span (ZMod 2) {v} := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, transvection_apply,
      add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  · rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    refine ⟨x, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, transvection_apply,
      add_sub_cancel_left, zmod_two_eq_one_of_ne_zero hx, one_smul]

private lemma cocycle_alt_of_transvection [FiniteDimensional (ZMod 2) A]
    (hA : finrank (ZMod 2) A = 4)
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1) (hπ : Function.Surjective π)
    (γ : Γ) {φ : Dual (ZMod 2) A} {v : A} (hφv : φ v = 0) (hφ : φ ≠ 0) (hv : v ≠ 0)
    (hπγ : π γ = LinearEquiv.transvection hφv) :
    (∀ x ∈ LinearMap.ker φ,
        cocycle ι hι θ hθ hexact π ρ γ x ∈ Submodule.span (ZMod 2) {v}) ∨
      (∀ x ∈ LinearMap.ker φ,
        cocycle ι hι θ hθ hexact π ρ γ x - x ∈ Submodule.span (ZMod 2) {v}) := by
  have hrangeγ : LinearMap.range ((π γ).toLinearMap - LinearMap.id) =
      Submodule.span (ZMod 2) {v} := by
    rw [hπγ]
    exact range_transvection_sub_id hφv hφ
  have hsq : π (γ * γ) = 1 := by
    rw [map_mul, hπγ, transvection_mul_self]
  have hcomm := cocycle_commute_of_sq ι hι θ hθ hexact π ρ hρι hρθ hker hsq
  have hcδ : ∀ x, cocycle ι hι θ hθ hexact π ρ γ ((π γ) x) =
      (π γ) (cocycle ι hι θ hθ hexact π ρ γ x) := by
    intro x
    have h := congrArg (fun L : A →ₗ[ZMod 2] A => L x) hcomm
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using h
  have hcK : ∀ x ∈ LinearMap.ker φ,
      cocycle ι hι θ hθ hexact π ρ γ x ∈ LinearMap.ker φ := by
    intro x hx
    have hδx : (π γ) x = x := by
      rw [hπγ, transvection_apply, LinearMap.mem_ker.1 hx, zero_smul, add_zero]
    have hδcx : (π γ) (cocycle ι hι θ hθ hexact π ρ γ x) =
        cocycle ι hι θ hθ hexact π ρ γ x := by
      rw [← hcδ, hδx]
    rw [hπγ, transvection_apply] at hδcx
    have h' : cocycle ι hι θ hθ hexact π ρ γ x +
        φ (cocycle ι hι θ hθ hexact π ρ γ x) • v =
        cocycle ι hι θ hθ hexact π ρ γ x + 0 := by
      rw [add_zero]
      exact hδcx
    exact LinearMap.mem_ker.2 ((smul_eq_zero.1 (add_left_cancel h')).resolve_right hv)
  have hcW : ∀ x ∈ Submodule.span (ZMod 2) {v},
      cocycle ι hι θ hθ hexact π ρ γ x ∈ Submodule.span (ZMod 2) {v} := by
    intro x hx
    rw [← hrangeγ] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    refine ⟨cocycle ι hι θ hθ hexact π ρ γ y, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, map_sub,
      hcδ]
  have hline : ∀ x ∈ LinearMap.ker φ, x ∉ Submodule.span (ZMod 2) {v} →
      cocycle ι hι θ hθ hexact π ρ γ x ∈ Submodule.span (ZMod 2) ({v, x} : Set A) := by
    intro x hxK hxW
    refine cocycle_preserves_line ι hι θ hθ hexact π ρ hπ γ hφv hπγ ?_ hxK hxW
    intro h hcommh y hy
    exact cocycle_conj_mod_center ι hι θ hθ hexact π ρ hρι hρθ hker γ h hφv hπγ hrangeγ
      hcommh hy
  exact cocycle_dichotomy (cocycle ι hι θ hθ hexact π ρ γ) hφv hv (finrank_ker_eq_three hA hφ)
    hcK hcW hline

private lemma cocycle_alt_one_of_transvection
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1) (hπ : Function.Surjective π)
    (γ₀ : Γ) {φ₀ : Dual (ZMod 2) A} {v₀ : A} (hφv₀ : φ₀ v₀ = 0) (hφ₀ : φ₀ ≠ 0) (hv₀ : v₀ ≠ 0)
    (hπγ₀ : π γ₀ = LinearEquiv.transvection hφv₀)
    (hone : ∀ x ∈ LinearMap.ker φ₀,
      cocycle ι hι θ hθ hexact π ρ γ₀ x - x ∈ Submodule.span (ZMod 2) {v₀})
    (γ : Γ) {φ : Dual (ZMod 2) A} {v : A} (hφv : φ v = 0) (hφ : φ ≠ 0) (hv : v ≠ 0)
    (hπγ : π γ = LinearEquiv.transvection hφv) :
    ∀ x ∈ LinearMap.ker φ,
      cocycle ι hι θ hθ hexact π ρ γ x - x ∈ Submodule.span (ZMod 2) {v} := by
  obtain ⟨P, hPv, hPconj⟩ := exists_conj_transvection hφv₀ hφv hv₀ hv hφ₀ hφ
  obtain ⟨h, hh⟩ := hπ P
  have hπconj : π (h * γ₀ * h⁻¹) = LinearEquiv.transvection hφv := by
    rw [map_mul, map_mul, map_inv, hh, hπγ₀, hPconj]
  have hkerφ₀ : LinearMap.ker ((π γ₀).toLinearMap - (1 : A →ₗ[ZMod 2] A)) =
      LinearMap.ker φ₀ := by
    rw [hπγ₀]
    exact ker_transvection_sub_id hφv₀ hv₀
  have hrange₀ : LinearMap.range ((π γ₀).toLinearMap - (1 : A →ₗ[ZMod 2] A)) =
      Submodule.span (ZMod 2) {v₀} := by
    rw [hπγ₀]
    exact range_transvection_sub_id hφv₀ hφ₀
  have hconj := cocycle_alt_one_conj ι hι θ hθ hexact π ρ hρι hρθ hker γ₀
    hkerφ₀ hrange₀ hone h hφv hπconj (by rw [hh]; exact hPv)
  intro x hx
  rw [← cocycle_eq_of_pi_eq ι hι θ hθ hexact π ρ hρθ hker (hπconj.trans hπγ.symm)]
  exact hconj x hx

private lemma cocycle_not_alt_one [FiniteDimensional (ZMod 2) A]
    (hA : finrank (ZMod 2) A = 4)
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (hker : ∀ γ, π γ = 1 → ρ γ = 1) (hπ : Function.Surjective π)
    (γ : Γ) {φ : Dual (ZMod 2) A} {v : A} (hφv : φ v = 0) (hφ : φ ≠ 0) (hv : v ≠ 0)
    (hπγ : π γ = LinearEquiv.transvection hφv) :
    ¬ ∀ x ∈ LinearMap.ker φ,
      cocycle ι hι θ hθ hexact π ρ γ x - x ∈ Submodule.span (ZMod 2) {v} := by
  classical
  intro hone
  have hK3 := finrank_ker_eq_three hA hφ
  obtain ⟨a, haK, haW⟩ : ∃ a ∈ LinearMap.ker φ, a ∉ Submodule.span (ZMod 2) {v} := by
    apply exists_mem_notMem_of_finrank_lt
    rw [finrank_span_singleton hv, hK3]
    norm_num
  obtain ⟨y, hyK, hyW⟩ :
      ∃ y ∈ LinearMap.ker φ, y ∉ Submodule.span (ZMod 2) ({v, a} : Set A) := by
    apply exists_mem_notMem_of_finrank_lt
    have := finrank_span_pair_le v a
    omega
  obtain ⟨ψ, hψS, hψy⟩ := exists_dual_eq_one_of_notMem hyW
  have hψv : ψ v = 0 := hψS v (Submodule.subset_span (by simp))
  have hψa : ψ a = 0 := hψS a (Submodule.subset_span (by simp))
  have hφy : φ y = 0 := LinearMap.mem_ker.1 hyK
  have hφa : φ a = 0 := LinearMap.mem_ker.1 haK
  have hψ0 : ψ ≠ 0 := by
    intro h
    rw [h, LinearMap.zero_apply] at hψy
    exact zero_ne_one hψy
  have hφψv : (φ + ψ) v = 0 := by rw [LinearMap.add_apply, hφv, hψv, add_zero]
  have hφψ0 : φ + ψ ≠ 0 := by
    intro h
    have h' := congrArg (fun χ : Dual (ZMod 2) A => χ y) h
    simp only [LinearMap.add_apply, LinearMap.zero_apply, hφy, hψy, zero_add] at h'
    exact one_ne_zero h'
  obtain ⟨γ₂, hγ₂⟩ := hπ (LinearEquiv.transvection hψv)
  have hπγ₃ : π (γ * γ₂) = LinearEquiv.transvection hφψv := by
    rw [map_mul, hπγ, hγ₂, transvection_mul_transvection_right hφv hψv hφψv]
  have hone₂ := cocycle_alt_one_of_transvection ι hι θ hθ hexact π ρ hρι hρθ hker hπ γ hφv hφ hv
    hπγ hone γ₂ hψv hψ0 hv hγ₂
  have hone₃ := cocycle_alt_one_of_transvection ι hι θ hθ hexact π ρ hρι hρθ hker hπ γ hφv hφ hv
    hπγ hone (γ * γ₂) hφψv hφψ0 hv hπγ₃
  have h₁ := hone a haK
  have h₂ := hone₂ a (LinearMap.mem_ker.2 hψa)
  have h₃ := hone₃ a (LinearMap.mem_ker.2 (by rw [LinearMap.add_apply, hφa, hψa, add_zero]))
  have hmul := cocycle_mul_apply ι hι θ hθ hexact π ρ hρι hρθ γ γ₂ a
  have hγ₂a : (π γ₂) a = a := by rw [hγ₂, transvection_apply, hψa, zero_smul, add_zero]
  rw [hγ₂a, hπγ, transvection_apply] at hmul
  apply haW
  have hsum : a = -((cocycle ι hι θ hθ hexact π ρ γ a - a) +
      (cocycle ι hι θ hθ hexact π ρ γ₂ a - a) +
      φ (cocycle ι hι θ hθ hexact π ρ γ₂ a) • v -
      (cocycle ι hι θ hθ hexact π ρ (γ * γ₂) a - a)) := by
    rw [hmul]
    abel
  rw [hsum]
  exact Submodule.neg_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ h₁ h₂)
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v)))) h₃)

private lemma finrank_fixed_of_alt_zero [FiniteDimensional (ZMod 2) A]
    [FiniteDimensional (ZMod 2) V] (hA : finrank (ZMod 2) A = 4)
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a))
    (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (γ : Γ) {φ : Dual (ZMod 2) A} {v : A} (hφv : φ v = 0) (hφ : φ ≠ 0) (hv : v ≠ 0)
    (hπγ : π γ = LinearEquiv.transvection hφv)
    (hzero : ∀ x ∈ LinearMap.ker φ,
      cocycle ι hι θ hθ hexact π ρ γ x ∈ Submodule.span (ZMod 2) {v}) :
    finrank (ZMod 2) (LinearMap.ker ((ρ γ : V →ₗ[ZMod 2] V) - LinearMap.id)) = 6 := by
  classical
  set Kv := LinearMap.ker ((ρ γ : V →ₗ[ZMod 2] V) - LinearMap.id) with hKv
  have memKv : ∀ w, w ∈ Kv ↔ ρ γ w = w := by
    intro w
    rw [hKv, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_toLinearMap, sub_eq_zero]
  have hδ : ∀ x, (π γ) x = x + φ x • v := by
    intro x
    rw [hπγ, transvection_apply]
  let Θ : Kv →ₗ[ZMod 2] A := θ.domRestrict Kv
  have hrange : LinearMap.range Θ = LinearMap.ker φ := by
    apply le_antisymm
    · rintro x ⟨w, rfl⟩
      have hw : ρ γ w = w := (memKv (w : V)).1 w.2
      have h1 : θ (ρ γ w) = (π γ) (θ w) := hρθ γ w
      rw [hw, hδ] at h1
      have h3 : θ w + φ (θ w) • v = θ w + 0 := by
        rw [add_zero]
        exact h1.symm
      change θ (w : V) ∈ LinearMap.ker φ
      exact LinearMap.mem_ker.2 ((smul_eq_zero.1 (add_left_cancel h3)).resolve_right hv)
    · intro a ha
      have hca := hzero a ha
      rw [← range_transvection_sub_id hφv hφ] at hca
      obtain ⟨a', ha'⟩ := hca
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap] at ha'
      have hδa : (π γ) a = a := by rw [hδ, LinearMap.mem_ker.1 ha, zero_smul, add_zero]
      have hδa' : (π γ) a' = a' + cocycle ι hι θ hθ hexact π ρ γ a := by
        rw [hπγ, ← ha']
        abel
      have hsa : ρ γ (linSec θ hθ a) =
          linSec θ hθ ((π γ) a) + ι (cocycle ι hι θ hθ hexact π ρ γ a) := by
        rw [iota_cocycle ι hι θ hθ hexact π ρ hρθ]
        abel
      refine ⟨⟨ι a' + linSec θ hθ a, ?_⟩, ?_⟩
      · rw [memKv, map_add, hρι, hsa, hδa, hδa', map_add]
        have h2 : ι (cocycle ι hι θ hθ hexact π ρ γ a) +
            ι (cocycle ι hι θ hθ hexact π ρ γ a) = 0 := two_add_self _
        calc ι a' + ι (cocycle ι hι θ hθ hexact π ρ γ a) +
              (linSec θ hθ a + ι (cocycle ι hι θ hθ hexact π ρ γ a))
            = ι a' + linSec θ hθ a + (ι (cocycle ι hι θ hθ hexact π ρ γ a) +
                ι (cocycle ι hι θ hθ hexact π ρ γ a)) := by abel
          _ = ι a' + linSec θ hθ a := by rw [h2, add_zero]
      · change θ (ι a' + linSec θ hθ a) = a
        rw [map_add, theta_iota ι θ hexact, linSec_theta, zero_add]
  have hkerdim : finrank (ZMod 2) (LinearMap.ker Θ) = 3 := by
    let F : LinearMap.ker φ →ₗ[ZMod 2] LinearMap.ker Θ :=
      LinearMap.codRestrict (LinearMap.ker Θ)
        (LinearMap.codRestrict Kv (ι.comp (LinearMap.ker φ).subtype) (by
          intro x
          rw [memKv, LinearMap.comp_apply, Submodule.coe_subtype, hρι, hδ,
            LinearMap.mem_ker.1 x.2, zero_smul, add_zero]))
        (by
          intro x
          rw [LinearMap.mem_ker]
          change θ (ι (x : A)) = 0
          exact theta_iota ι θ hexact x)
    have hF : Function.Bijective F := by
      constructor
      · intro x y hxy
        have h := congrArg (fun z : LinearMap.ker Θ => ((z : Kv) : V)) hxy
        have h' : ι (x : A) = ι (y : A) := h
        exact Subtype.ext (hι h')
      · rintro ⟨⟨w, hwKv⟩, hwΘ⟩
        have hθw : θ w = 0 := LinearMap.mem_ker.1 hwΘ
        have hwι : w ∈ LinearMap.range ι := by
          rw [hexact]
          exact LinearMap.mem_ker.2 hθw
        obtain ⟨a', rfl⟩ := hwι
        have hfix : ρ γ (ι a') = ι a' := (memKv _).1 hwKv
        rw [hρι, hδ] at hfix
        have h3 : a' + φ a' • v = a' + 0 := by
          rw [add_zero]
          exact hι hfix
        have ha'K : a' ∈ LinearMap.ker φ :=
          LinearMap.mem_ker.2 ((smul_eq_zero.1 (add_left_cancel h3)).resolve_right hv)
        exact ⟨⟨a', ha'K⟩, rfl⟩
    rw [← (LinearEquiv.ofBijective F hF).finrank_eq]
    exact finrank_ker_eq_three hA hφ
  have hrn := LinearMap.finrank_range_add_finrank_ker Θ
  rw [hrange, hkerdim, finrank_ker_eq_three hA hφ] at hrn
  omega

theorem finrank_ker_sub_one_of_transvection
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) V]
    (hA : Module.finrank (ZMod 2) A = 4)
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (hπ : Function.Surjective π)
    (ρ : Γ →* (V ≃ₗ[ZMod 2] V)) (hker : ∀ γ, π γ = 1 → ρ γ = 1)
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a)) (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (γ : Γ) (hγ : Module.finrank (ZMod 2)
      (LinearMap.ker ((π γ : A →ₗ[ZMod 2] A) - LinearMap.id)) = 3) :
    Module.finrank (ZMod 2) (LinearMap.ker ((ρ γ : V →ₗ[ZMod 2] V) - LinearMap.id)) = 6 := by
  obtain ⟨φ, v, hφv, hπγ, hφ, hv, -, -⟩ := exists_transvection_of_finrank_ker hA (π γ) hγ
  rcases cocycle_alt_of_transvection hA ι hι θ hθ hexact π ρ hρι hρθ hker hπ γ hφv hφ hv hπγ
    with h0 | h1
  · exact finrank_fixed_of_alt_zero hA ι hι θ hθ hexact π ρ hρι hρθ γ hφv hφ hv hπγ h0
  · exact absurd h1
      (cocycle_not_alt_one hA ι hι θ hθ hexact π ρ hρι hρθ hker hπ γ hφv hφ hv hπγ)

theorem card_fixed_of_transvection
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) V]
    (hA : Module.finrank (ZMod 2) A = 4)
    (ι : A →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (θ : V →ₗ[ZMod 2] A) (hθ : Function.Surjective θ)
    (hexact : LinearMap.range ι = LinearMap.ker θ)
    {Γ : Type*} [Group Γ] (π : Γ →* (A ≃ₗ[ZMod 2] A)) (hπ : Function.Surjective π)
    (ρ : Γ →* (V ≃ₗ[ZMod 2] V)) (hker : ∀ γ, π γ = 1 → ρ γ = 1)
    (hρι : ∀ γ a, ρ γ (ι a) = ι (π γ a)) (hρθ : ∀ γ v, θ (ρ γ v) = π γ (θ v))
    (γ : Γ) (hγ : Module.finrank (ZMod 2)
      (LinearMap.ker ((π γ : A →ₗ[ZMod 2] A) - LinearMap.id)) = 3) :
    Nat.card {v : V // ρ γ v = v} = 2 ^ 6 := by
  have h := finrank_ker_sub_one_of_transvection hA ι hι θ hθ hexact π hπ ρ hker hρι hρθ γ hγ
  have hcard : Nat.card (LinearMap.ker ((ρ γ : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2 ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), h, Nat.card_zmod]
  rw [← hcard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap,
    sub_eq_zero]

end CFSG.LinearAlgebra
