module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K U V : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  {Q₀ : QuadraticForm K U} {Q : QuadraticForm K V}

variable (Q₀ Q) in
structure A2lSummand where
  incl : U →ₗ[K] V
  coords : V →ₗ[K] U
  coords_incl : ∀ d, coords (incl d) = d
  polar_incl : ∀ x d, polar Q x (incl d) = polar Q₀ (coords x) d

namespace A2lSummand

variable (S : A2lSummand Q₀ Q)

theorem Q_incl (h2 : (2 : K) ≠ 0) (d : U) : Q (S.incl d) = Q₀ d := by
  have h := S.polar_incl (S.incl d) d
  rw [S.coords_incl, polar_self_eq_two_mul, polar_self_eq_two_mul] at h
  exact mul_left_cancel₀ h2 h

theorem incl_injective : Function.Injective S.incl := fun a b h => by
  rw [← S.coords_incl a, ← S.coords_incl b, h]

@[expose] def embLin (T : Module.End K U) : V →ₗ[K] V :=
  LinearMap.id + S.incl ∘ₗ (T - 1) ∘ₗ S.coords

theorem embLin_apply (T : Module.End K U) (x : V) :
    S.embLin T x = x + S.incl (T (S.coords x) - S.coords x) := by
  simp [embLin]

theorem embLin_one : S.embLin 1 = 1 := by
  ext x
  simp [embLin_apply]

theorem embLin_mul (T₁ T₂ : Module.End K U) :
    S.embLin (T₁ * T₂) = S.embLin T₁ * S.embLin T₂ := by
  ext x
  simp only [embLin_apply, Module.End.mul_apply, map_add, S.coords_incl, map_sub]
  abel

@[expose] noncomputable def embHom {G : Type*} [Group G] (ρ : G →* Module.End K U) :
    G →* (V ≃ₗ[K] V) where
  toFun g := LinearEquiv.ofLinearMap (S.embLin (ρ g)) (S.embLin (ρ g⁻¹))
    (by
      rw [← Module.End.mul_eq_comp, ← embLin_mul, ← map_mul, mul_inv_cancel, map_one,
        embLin_one]
      rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← embLin_mul, ← map_mul, inv_mul_cancel, map_one,
        embLin_one]
      rfl)
  map_one' := LinearEquiv.ext fun x => by simp [embLin_one]
  map_mul' g h := LinearEquiv.ext fun x => by simp [embLin_mul]

theorem embHom_apply {G : Type*} [Group G] (ρ : G →* Module.End K U) (g : G) (x : V) :
    S.embHom ρ g x = x + S.incl (ρ g (S.coords x) - S.coords x) :=
  S.embLin_apply _ _

theorem embHom_apply_of_coords_eq_zero {G : Type*} [Group G] (ρ : G →* Module.End K U) (g : G)
    {r : V} (hr : S.coords r = 0) : S.embHom ρ g r = r := by
  rw [embHom_apply, hr]
  simp

theorem coords_embHom {G : Type*} [Group G] (ρ : G →* Module.End K U) (g : G) (x : V) :
    S.coords (S.embHom ρ g x) = ρ g (S.coords x) := by
  rw [embHom_apply, map_add, S.coords_incl]
  abel

theorem embHom_injective {G : Type*} [Group G] {ρ : G →* Module.End K U}
    (hρ : Function.Injective ρ) : Function.Injective (S.embHom ρ) := by
  intro g h hgh
  apply hρ
  ext d
  have := congrArg (fun m : V ≃ₗ[K] V => S.coords (m (S.incl d))) hgh
  simpa only [coords_embHom, S.coords_incl] using this

@[expose] noncomputable def Phi : (U ≃ₗ[K] U) →* (V ≃ₗ[K] V) :=
  S.embHom LinearEquiv.automorphismGroup.toLinearMapMonoidHom

theorem Phi_apply (B : U ≃ₗ[K] U) (x : V) :
    S.Phi B x = x + S.incl (B (S.coords x) - S.coords x) :=
  S.embHom_apply _ _ _

theorem Phi_injective : Function.Injective S.Phi :=
  S.embHom_injective fun a b h => LinearEquiv.ext fun d => congrArg (fun m => m d) h

theorem Phi_apply_incl (B : U ≃ₗ[K] U) (d : U) : S.Phi B (S.incl d) = S.incl (B d) := by
  rw [Phi_apply, S.coords_incl, map_sub]
  abel

theorem Phi_neg_apply (x : V) :
    S.Phi (LinearEquiv.neg K) x = x + S.incl (-S.coords x - S.coords x) := by
  rw [Phi_apply]
  rfl

theorem Phi_eichler (h2 : (2 : K) ≠ 0) {u w : U} (hu : Q₀ u = 0) (hw : polar Q₀ u w = 0) :
    S.Phi (eichler Q₀ u w) = eichler Q (S.incl u) (S.incl w) := by
  have hu' : Q (S.incl u) = 0 := by rw [S.Q_incl h2, hu]
  have hw' : polar Q (S.incl u) (S.incl w) = 0 := by rw [S.polar_incl, S.coords_incl, hw]
  have key : ∀ c : U, eichler Q₀ u w c - c =
      polar Q₀ c u • w - (polar Q₀ c w + Q₀ w * polar Q₀ c u) • u := fun c => by
    rw [eichler_apply hu hw]
    abel
  refine LinearEquiv.ext fun x => ?_
  rw [S.Phi_apply, key, eichler_apply hu' hw', map_sub, map_smul, map_smul, ← S.polar_incl,
    ← S.polar_incl, ← S.Q_incl h2 w]
  module

theorem Phi_mem_elementaryGroup (h2 : (2 : K) ≠ 0) {B : U ≃ₗ[K] U}
    (hB : B ∈ elementaryGroup Q₀) : S.Phi B ∈ elementaryGroup Q := by
  induction hB using Subgroup.closure_induction with
  | mem B hB =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hB
    rw [Phi_eichler S h2 hu hw]
    exact eichler_mem_elementaryGroup Q _ _
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

@[expose] def HasKey (g : V ≃ₗ[K] V) : Prop :=
  ∀ x, g (S.incl (S.coords x)) = S.incl (S.coords (g x))

theorem hasKey_of_commute (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hg : g * S.Phi (LinearEquiv.neg K) = S.Phi (LinearEquiv.neg K) * g) : S.HasKey g := by
  intro x
  have h := congrArg (fun m : V ≃ₗ[K] V => m x) hg
  simp only [LinearEquiv.mul_apply, Phi_neg_apply, map_add, map_sub, map_neg] at h
  have h4 := add_left_cancel h
  have h3 : (2 : K) • g (S.incl (S.coords x)) = (2 : K) • S.incl (S.coords (g x)) := by
    rw [two_smul, two_smul]
    simpa [neg_sub, sub_neg_eq_add] using congrArg Neg.neg h4
  exact smul_right_injective V h2 h3

variable {S} in
theorem HasKey.inv {g : V ≃ₗ[K] V} (hg : S.HasKey g) : S.HasKey g⁻¹ := by
  intro x
  apply g.injective
  rw [LinearEquiv.apply_inv_apply', hg (g⁻¹ x), LinearEquiv.apply_inv_apply']

@[expose] noncomputable def act (g : V ≃ₗ[K] V) : U →ₗ[K] U :=
  S.coords ∘ₗ g.toLinearMap ∘ₗ S.incl

theorem act_apply (g : V ≃ₗ[K] V) (d : U) : S.act g d = S.coords (g (S.incl d)) := rfl

variable {S} in
theorem HasKey.apply_incl {g : V ≃ₗ[K] V} (hg : S.HasKey g) (d : U) :
    g (S.incl d) = S.incl (S.act g d) := by
  have := hg (S.incl d)
  rwa [S.coords_incl] at this

variable {S} in
theorem HasKey.coords_apply {g : V ≃ₗ[K] V} (hg : S.HasKey g) (x : V) :
    S.coords (g x) = S.act g (S.coords x) := by
  rw [act_apply, hg x, S.coords_incl]

@[expose] noncomputable def actEquiv {g : V ≃ₗ[K] V} (hg : S.HasKey g) : U ≃ₗ[K] U :=
  LinearEquiv.ofLinear (S.act g) (S.act g⁻¹)
    (LinearMap.ext fun d => by
      rw [LinearMap.comp_apply, LinearMap.id_apply, S.act_apply g, ← hg.inv.apply_incl,
        LinearEquiv.apply_inv_apply', S.coords_incl])
    (LinearMap.ext fun d => by
      rw [LinearMap.comp_apply, LinearMap.id_apply, S.act_apply g⁻¹, ← hg.apply_incl,
        LinearEquiv.inv_apply_apply', S.coords_incl])

theorem actEquiv_apply {g : V ≃ₗ[K] V} (hg : S.HasKey g) (d : U) : S.actEquiv hg d = S.act g d :=
  rfl

theorem actEquiv_mem_orthogonalGroup (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V} (hg : S.HasKey g)
    (hgQ : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    S.actEquiv hg ∈ TauCeti.QuadraticMap.orthogonalGroup Q₀ := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun d => ?_
  rw [← S.Q_incl h2, ← S.Q_incl h2 d, actEquiv_apply, ← hg.apply_incl, map_of_mem hgQ]

theorem conj_Phi {g : V ≃ₗ[K] V} (hg : S.HasKey g) (B : U ≃ₗ[K] U) :
    g * S.Phi B * g⁻¹ = S.Phi (S.actEquiv hg * B * (S.actEquiv hg)⁻¹) := by
  refine LinearEquiv.ext fun x => ?_
  have hc : S.coords (g⁻¹ x) = (S.actEquiv hg)⁻¹ (S.coords x) := by
    apply (S.actEquiv hg).injective
    rw [LinearEquiv.apply_inv_apply', actEquiv_apply, ← hg.coords_apply,
      LinearEquiv.apply_inv_apply']
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Phi_apply, Phi_apply, map_add,
    LinearEquiv.apply_inv_apply', hg.apply_incl, hc]
  congr 2
  rw [← actEquiv_apply S hg, map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    LinearEquiv.apply_inv_apply']

end A2lSummand

end CFSG.OddStandard.SmallF3.HypA2Leaves
