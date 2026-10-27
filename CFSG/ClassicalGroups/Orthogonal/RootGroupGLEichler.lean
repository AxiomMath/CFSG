module

public import CFSG.ClassicalGroups.Orthogonal.LineStabilizer
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusOTwo

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.StandardType.AutOm (eichlerC)
open QuadraticMap Matrix

section Fin

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem eichler_apply_eq_eichlerC {u w : Fin d → K} (hu : Q u = 0) (hw : polar Q u w = 0)
    (y : Fin d → K) : eichler Q u w y = eichlerC Q u w y := by
  rw [eichler_apply hu hw, eichlerC, add_smul]
  abel

theorem polar_eichlerC_left (u w y z : Fin d → K) :
    polar Q (eichlerC Q u w y) z =
      polar Q y z + polar Q y u * polar Q w z - polar Q y w * polar Q u z -
        Q w * polar Q y u * polar Q u z := by
  simp only [eichlerC, polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul]

theorem eichlerC_zero_right (u y : Fin d → K) : eichlerC Q u 0 y = y := by
  simp [eichlerC]

theorem eichlerC_eq_self {u w v : Fin d → K} (hu : polar Q v u = 0)
    (hw : polar Q v w = 0) : eichlerC Q u w v = v := by
  rw [eichlerC, hu, hw]
  simp

theorem eichlerC_eichlerC {u w w' : Fin d → K} (hu : Q u = 0) (hw : polar Q u w = 0)
    (hw' : polar Q u w' = 0) (y : Fin d → K) :
    eichlerC Q u w (eichlerC Q u w' y) = eichlerC Q u (w + w') y := by
  have huu : polar Q u u = 0 := polar_self_eq_zero hu
  have hw'u : polar Q w' u = 0 := by rwa [polar_comm Q w' u]
  have hp1 : polar Q (eichlerC Q u w' y) u = polar Q y u := by
    rw [polar_eichlerC_left]
    simp [huu, hw'u]
  have hp2 : polar Q (eichlerC Q u w' y) w =
      polar Q y w + polar Q y u * polar Q w' w := by
    rw [polar_eichlerC_left]
    simp [hw]
  have hQadd : Q (w + w') = Q w + Q w' + polar Q w w' := QuadraticMap.map_add Q w w'
  have hpadd : polar Q y (w + w') = polar Q y w + polar Q y w' :=
    polar_add_right Q y w w'
  change eichlerC Q u w' y + polar Q (eichlerC Q u w' y) u • w -
      polar Q (eichlerC Q u w' y) w • u -
      (Q w * polar Q (eichlerC Q u w' y) u) • u = eichlerC Q u (w + w') y
  rw [hp1, hp2]
  simp only [eichlerC]
  rw [hQadd, hpadd, polar_comm Q w' w]
  module

theorem eichlerC_add_smul_self {u w : Fin d → K} (hu : Q u = 0)
    (hwu : polar Q w u = 0) (c : K) (y : Fin d → K) :
    eichlerC Q u (w + c • u) y = eichlerC Q u w y := by
  have hpol : polar Q y (w + c • u) = polar Q y w + c * polar Q y u := by
    rw [polar_add_right, polar_smul_right, smul_eq_mul]
  have hQ : Q (w + c • u) = Q w := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hu, smul_zero,
      polar_smul_right, hwu, smul_zero, add_zero, add_zero]
  rw [eichlerC, hpol, hQ, eichlerC, smul_add, smul_smul, add_smul]
  module

theorem eichlerC_smul_right_eq {e u : Fin d → K} (hu : Q u = 0) (he : Q e = 0)
    (hue : polar Q u e = 0) (c : K) (y : Fin d → K) :
    eichlerC Q u (c • e) y = eichlerC Q e ((-c) • u) y := by
  have hQe : Q (c • e) = 0 := by rw [QuadraticMap.map_smul, he, smul_zero]
  have hQu : Q ((-c) • u) = 0 := by rw [QuadraticMap.map_smul, hu, smul_zero]
  rw [eichlerC, eichlerC, polar_smul_right, polar_smul_right, hQe, hQu]
  module

theorem mem_rootGroupGL_of_eichlerC {e w : Fin d → K} {g : GL (Fin d) K}
    (he : Q e = 0) (hw : polar Q e w = 0)
    (hg : ∀ y, (g : Matrix (Fin d) (Fin d) K) *ᵥ y = eichlerC Q e w y) :
    g ∈ rootGroupGL Q e := by
  rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mem_rootGroup]
  refine ⟨w, hw, ?_⟩
  apply LinearEquiv.ext
  intro y
  rw [eichler_apply_eq_eichlerC Q he hw y, toLinEquiv_apply, ← hg y]

theorem mem_rootGroupGL_of_eichlerC_smul_right {e u : Fin d → K} (c : K) {g : GL (Fin d) K}
    (he : Q e = 0) (hu : Q u = 0) (hue : polar Q u e = 0)
    (hg : ∀ y, (g : Matrix (Fin d) (Fin d) K) *ᵥ y = eichlerC Q u (c • e) y) :
    g ∈ rootGroupGL Q e := by
  refine mem_rootGroupGL_of_eichlerC (Q := Q) (e := e) (w := (-c) • u) (g := g) he ?_
    fun y => ?_
  · rw [polar_smul_right, polar_comm Q e u, hue, smul_zero]
  · rw [hg y, eichlerC_smul_right_eq Q hu he hue c y]

theorem exists_eichlerC_of_mem_rootGroupGL {e f : Fin d → K} (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) {g : GL (Fin d) K} (hg : g ∈ rootGroupGL Q f) :
    ∃ w, polar Q w e = 0 ∧ polar Q w f = 0 ∧
      ∀ y, (g : Matrix (Fin d) (Fin d) K) *ᵥ y = eichlerC Q f w y := by
  rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mem_rootGroup] at hg
  obtain ⟨w₀, hw₀f, hw₀⟩ := hg
  set a : K := polar Q w₀ e with ha
  have hgact : ∀ y, (g : Matrix (Fin d) (Fin d) K) *ᵥ y = eichlerC Q f w₀ y := by
    intro y
    rw [← toLinEquiv_apply, ← hw₀, eichler_apply_eq_eichlerC Q hf hw₀f y]
  have hw₀f' : polar Q w₀ f = 0 := by rwa [polar_comm Q w₀ f]
  refine ⟨w₀ + (-a) • f, ?_, ?_, ?_⟩
  · rw [polar_add_left, polar_smul_left, polar_comm Q f e, hef, smul_eq_mul, mul_one,
      ← ha, add_neg_cancel]
  · rw [polar_add_left, polar_smul_left, hw₀f', polar_self_eq_zero hf, smul_zero, add_zero]
  · intro y
    rw [eichlerC_add_smul_self Q hf hw₀f' (-a) y]
    exact hgact y

end Fin

section General

variable {K : Type} [Field K]

theorem conj_mem_rootGroupGL {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K (ι → K)} {e : ι → K} {m g : GL ι K}
    (hm : m ∈ lineStabilizer Q e) (hg : g ∈ rootGroupGL Q e) :
    m * g * m⁻¹ ∈ rootGroupGL Q e := by
  obtain ⟨hmiso, c, hme⟩ := (mem_lineStabilizer_iff Q).mp hm
  have hmO : toLinEquiv ι K m ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [toLinEquiv_apply]
      exact hmiso v
  have hmapply : toLinEquiv ι K m e = c • e := by
    rw [toLinEquiv_apply]
    exact hme
  have hg' : toLinEquiv ι K g ∈ rootGroup Q e := by
    rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hg
    exact hg
  have hconj := conj_mem_rootGroup_of_apply_eq_smul (Q := Q) hmO hmapply hg'
  rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  simpa only [map_mul, map_inv] using hconj

theorem mem_rootGroupGL_of_intertwine {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {Q : QuadraticForm K (ι → K)}
    {Q' : QuadraticForm K (ι' → K)} (φ : (ι → K) ≃ₗ[K] (ι' → K))
    (hφ : ∀ x, Q' (φ x) = Q x) {g : GL ι K} {g' : GL ι' K}
    (hgg' : ∀ x, (g' : Matrix ι' ι' K) *ᵥ φ x = φ ((g : Matrix ι ι K) *ᵥ x))
    {e : ι → K} (hg : g ∈ rootGroupGL Q e) : g' ∈ rootGroupGL Q' (φ e) := by
  rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mem_rootGroup] at hg ⊢
  obtain ⟨w, hw, hgw⟩ := hg
  let φi : Q.IsometryEquiv Q' := { φ with map_app' := hφ }
  refine ⟨φ w, ?_, ?_⟩
  · rw [polar_map_of_linearIsometry Q φ hφ e w]
    exact hw
  · apply LinearEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    calc eichler Q' (φ e) (φ w) (φ x)
        = φ (eichler Q e w x) :=
          (CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.eichler_isometry_apply
            φi e w x).symm
      _ = φ ((g : Matrix ι ι K) *ᵥ x) := by rw [hgw, toLinEquiv_apply]
      _ = (g' : Matrix ι' ι' K) *ᵥ φ x := (hgg' x).symm
      _ = toLinEquiv ι' K g' (φ x) := (toLinEquiv_apply g' (φ x)).symm

end General

end CFSG.ClassicalGroups.Orthogonal
