module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Involution

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace Frame

variable (F : Frame Q)

theorem mem_span_iff_inv (h2 : (2 : K) ≠ 0) {x : V} : x ∈ F.span ↔ F.La (-1) x = -x := by
  rw [mem_span_iff, La_neg_one_apply]
  constructor
  · intro h
    rw [← h]
    simp only [two_smul]
    abel
  · intro h
    have h0 : x - (2 : K) • F.incl (F.coords x) + x = 0 := by rw [h]; exact neg_add_cancel x
    have h' : (2 : K) • x = (2 : K) • F.incl (F.coords x) := by
      rw [← sub_eq_zero, ← h0]
      module
    exact smul_right_injective V h2 h'

theorem mem_perp_iff_fix (h2 : (2 : K) ≠ 0) {x : V} : x ∈ F.perp ↔ F.La (-1) x = x := by
  rw [mem_perp_iff, La_neg_one_apply]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    have h0 : (2 : K) • F.incl (F.coords x) = 0 := by
      have : x - (2 : K) • F.incl (F.coords x) = x - 0 := by rw [h, sub_zero]
      exact (sub_right_inj.mp this)
    have h1 : F.incl (F.coords x) = 0 := (smul_eq_zero.mp h0).resolve_left h2
    have h3 := congrArg F.coords h1
    rwa [coords_incl, map_zero] at h3

section Commuting

variable {F}
variable {g : V ≃ₗ[K] V}

theorem map_mem_span (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g) {x : V}
    (hx : x ∈ F.span) : g x ∈ F.span := by
  rw [mem_span_iff_inv F h2] at hx ⊢
  have := LinearEquiv.congr_fun hg x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, map_neg] at this
  exact this.symm

theorem map_mem_perp (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g) {x : V}
    (hx : x ∈ F.perp) : g x ∈ F.perp := by
  rw [mem_perp_iff_fix F h2] at hx ⊢
  have := LinearEquiv.congr_fun hg x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx] at this
  exact this.symm

end Commuting

@[expose] def transport (g : V ≃ₗ[K] V) : Module.End K (Matrix (Fin 2) (Fin 2) K) :=
  F.coords ∘ₗ (g : V →ₗ[K] V) ∘ₗ F.incl

theorem transport_apply (g : V ≃ₗ[K] V) (Y : Matrix (Fin 2) (Fin 2) K) :
    F.transport g Y = F.coords (g (F.incl Y)) :=
  rfl

variable {F}
variable {g h : V ≃ₗ[K] V}

theorem inv_commute_La (hg : g * F.La (-1) = F.La (-1) * g) :
    g⁻¹ * F.La (-1) = F.La (-1) * g⁻¹ := by
  calc g⁻¹ * F.La (-1) = g⁻¹ * (F.La (-1) * g) * g⁻¹ := by group
    _ = g⁻¹ * (g * F.La (-1)) * g⁻¹ := by rw [hg]
    _ = F.La (-1) * g⁻¹ := by group

theorem incl_transport (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g)
    (Y : Matrix (Fin 2) (Fin 2) K) : F.incl (F.transport g Y) = g (F.incl Y) :=
  ((mem_span_iff F).mp (map_mem_span h2 hg ⟨Y, rfl⟩)).symm

theorem coords_map (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g) (x : V) :
    F.coords (g x) = F.transport g (F.coords x) := by
  have hr : x - F.incl (F.coords x) ∈ F.perp := by
    rw [mem_perp_iff, map_sub, coords_incl, sub_self]
  have hgr := map_mem_perp h2 hg hr
  rw [mem_perp_iff, map_sub, map_sub] at hgr
  exact sub_eq_zero.mp hgr

theorem transport_mul (h2 : (2 : K) ≠ 0) (hh : h * F.La (-1) = F.La (-1) * h) :
    F.transport (g * h) = F.transport g * F.transport h := by
  refine LinearMap.ext fun Y => ?_
  rw [Module.End.mul_apply, F.transport_apply g (F.transport h Y), incl_transport h2 hh Y]
  rfl

theorem transport_one : F.transport (1 : V ≃ₗ[K] V) = 1 := by
  refine LinearMap.ext fun Y => ?_
  rw [transport_apply]
  exact F.coords_incl Y

theorem transport_mul_inv (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g) :
    F.transport g * F.transport g⁻¹ = 1 := by
  rw [← transport_mul h2 (inv_commute_La hg), mul_inv_cancel, transport_one]

theorem transport_inv_mul (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g) :
    F.transport g⁻¹ * F.transport g = 1 := by
  rw [← transport_mul h2 hg, inv_mul_cancel, transport_one]

@[expose] def transportEquiv (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g) :
    Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  LinearEquiv.ofLinearMap (F.transport g) (F.transport g⁻¹)
    (by rw [← Module.End.mul_eq_comp]; exact transport_mul_inv h2 hg)
    (by rw [← Module.End.mul_eq_comp]; exact transport_inv_mul h2 hg)

theorem transportEquiv_apply (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g)
    (Y : Matrix (Fin 2) (Fin 2) K) : transportEquiv h2 hg Y = F.transport g Y :=
  rfl

theorem transportEquiv_mem_orthogonalGroup (h2 : (2 : K) ≠ 0)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg : g * F.La (-1) = F.La (-1) * g) :
    transportEquiv h2 hg ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun Y => ?_
  rw [detQ_apply, detQ_apply, ← F.Q_incl, ← F.Q_incl, transportEquiv_apply,
    incl_transport h2 hg, map_of_mem hgO]

theorem conj_embLin (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g)
    (T : Module.End K (Matrix (Fin 2) (Fin 2) K)) (x : V) :
    g (F.embLin T (g⁻¹ x)) = F.embLin (F.transport g ∘ₗ T ∘ₗ F.transport g⁻¹) x := by
  have hg' := inv_commute_La hg
  have hSS : ∀ Z, F.transport g (F.transport g⁻¹ Z) = Z := fun Z => by
    have := LinearMap.congr_fun (transport_mul_inv h2 hg) Z
    simpa using this
  rw [embLin_apply_eq, embLin_apply_eq, map_add, map_sub, ← incl_transport h2 hg,
    ← incl_transport h2 hg, coords_map h2 hg' x]
  simp only [LinearMap.comp_apply, hSS]
  rw [show g (g⁻¹ x) = x from by simp]

variable (F) in
@[expose] noncomputable def embGrp : (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) →*
    (V ≃ₗ[K] V) :=
  F.embHom LinearEquiv.automorphismGroup.toLinearMapMonoidHom

theorem embGrp_apply (T : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) (x : V) :
    F.embGrp T x = F.embLin (T : Module.End K (Matrix (Fin 2) (Fin 2) K)) x :=
  rfl

variable (F) in
theorem embGrp_injective : Function.Injective F.embGrp := by
  intro T T' hT
  refine LinearEquiv.ext fun Y => ?_
  have := congrArg (fun g : V ≃ₗ[K] V => F.coords (g (F.incl Y))) hT
  simpa [embGrp_apply, embLin_apply, coords_incl] using this

theorem embGrp_conj (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g)
    (T : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
    F.embGrp (transportEquiv h2 hg * T * (transportEquiv h2 hg)⁻¹) = g * F.embGrp T * g⁻¹ := by
  refine LinearEquiv.ext fun x => ?_
  have hcoe : ((transportEquiv h2 hg * T * (transportEquiv h2 hg)⁻¹ :
      Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
      Module.End K (Matrix (Fin 2) (Fin 2) K)) =
      F.transport g ∘ₗ (T : Module.End K (Matrix (Fin 2) (Fin 2) K)) ∘ₗ F.transport g⁻¹ :=
    LinearMap.ext fun Y => rfl
  rw [embGrp_apply, hcoe, ← conj_embLin h2 hg, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    embGrp_apply]

theorem conjSubgroup_map_embGrp (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g)
    (N : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)) :
    conjSubgroup g (N.map F.embGrp) = (conjSubgroup (transportEquiv h2 hg) N).map F.embGrp := by
  ext y
  rw [mem_conjSubgroup, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, hy⟩
    refine ⟨transportEquiv h2 hg * n * (transportEquiv h2 hg)⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup]
      simpa [mul_assoc] using hn
    · rw [embGrp_conj h2 hg, hy]
      group
  · rintro ⟨x, hx, rfl⟩
    rw [mem_conjSubgroup] at hx
    refine ⟨_, hx, ?_⟩
    have := embGrp_conj h2 hg ((transportEquiv h2 hg)⁻¹ * x * transportEquiv h2 hg)
    rw [show transportEquiv h2 hg * ((transportEquiv h2 hg)⁻¹ * x * transportEquiv h2 hg) *
      (transportEquiv h2 hg)⁻¹ = x by group] at this
    rw [this]
    group

@[expose] def sigmaSL (A : SL(2, K)) : SL(2, K) :=
  ⟨sigmaLin (A : Matrix (Fin 2) (Fin 2) K), by rw [det_sigmaLin, A.2]⟩

theorem coe_sigmaSL (A : SL(2, K)) :
    ((sigmaSL A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = sigmaLin (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem sigmaSL_sigmaSL (A : SL(2, K)) : sigmaSL (sigmaSL A) = A :=
  Subtype.ext (sigmaLin_sigmaLin _)

theorem La_eq_embGrp (A : SL(2, K)) : F.La A = F.embGrp (lmulEquiv A) :=
  LinearEquiv.ext fun _ => rfl

theorem swap_La_eq_embGrp (A : SL(2, K)) : F.swap.La A = F.embGrp (rmulEquiv (sigmaSL A)) :=
  LinearEquiv.ext fun x => La_swap_apply F A x

theorem La_range_eq_map : F.La.range = leftGrp.map F.embGrp := by
  ext y
  rw [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨lmulEquiv A, lmulEquiv_mem_leftGrp A, (La_eq_embGrp A).symm⟩
  · rintro ⟨x, ⟨A, hA⟩, rfl⟩
    refine ⟨A, ?_⟩
    rw [La_eq_embGrp]
    congr 1
    exact (LinearEquiv.ext fun X => (hA X).symm)

theorem swap_La_range_eq_map : F.swap.La.range = rightGrp.map F.embGrp := by
  ext y
  rw [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨rmulEquiv (sigmaSL A), rmulEquiv_mem_rightGrp _, (swap_La_eq_embGrp A).symm⟩
  · rintro ⟨x, ⟨B, hB⟩, rfl⟩
    refine ⟨sigmaSL B, ?_⟩
    rw [swap_La_eq_embGrp, sigmaSL_sigmaSL]
    congr 1
    exact (LinearEquiv.ext fun X => (hB X).symm)

theorem conjSubgroup_La_range (h2 : (2 : K) ≠ 0) (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g * F.La (-1) = F.La (-1) * g) :
    (LinearEquiv.det (transportEquiv h2 hg) = 1 ∧ conjSubgroup g F.La.range = F.La.range ∧
        conjSubgroup g F.swap.La.range = F.swap.La.range) ∨
      (LinearEquiv.det (transportEquiv h2 hg) = -1 ∧ conjSubgroup g F.La.range = F.swap.La.range ∧
        conjSubgroup g F.swap.La.range = F.La.range) := by
  rcases isometry_trichotomy h2 (transportEquiv_mem_orthogonalGroup h2 hgO hg) with
    ⟨hd, h1, h3⟩ | ⟨hd, h1, h3⟩
  · left
    refine ⟨hd, ?_, ?_⟩
    · rw [La_range_eq_map (F := F), conjSubgroup_map_embGrp h2 hg, h1]
    · rw [swap_La_range_eq_map (F := F), conjSubgroup_map_embGrp h2 hg, h3]
  · right
    refine ⟨hd, ?_, ?_⟩
    · rw [La_range_eq_map (F := F), swap_La_range_eq_map (F := F),
        conjSubgroup_map_embGrp h2 hg, h1]
    · rw [La_range_eq_map (F := F), swap_La_range_eq_map (F := F),
        conjSubgroup_map_embGrp h2 hg, h3]

end Frame

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
