module

public import CFSG.ClassicalInvolution.Phan.PhanP16Witt

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open QuadraticMap

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def planeMap (R : Submodule F V) (a b : V) : (R × (F × F)) →ₗ[F] V where
  toFun p := (p.1 : V) + p.2.1 • a + p.2.2 • b
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add]

theorem planeMap_apply (R : Submodule F V) (a b : V) (p : R × (F × F)) :
    planeMap R a b p = (p.1 : V) + p.2.1 • a + p.2.2 • b := rfl

@[expose] noncomputable def planeForm (Q : QuadraticForm F V) (R : Submodule F V) (c : F) :
    QuadraticForm F (R × (F × F)) :=
  (Q.restrict R).prod ((c • QuadraticMap.sq).prod (c • QuadraticMap.sq))

theorem planeForm_apply (Q : QuadraticForm F V) (R : Submodule F V) (c : F)
    (p : R × (F × F)) :
    planeForm Q R c p = Q p.1 + (c * (p.2.1 * p.2.1) + c * (p.2.2 * p.2.2)) := by
  simp [planeForm]

theorem planeForm_nondegenerate [Invertible (2 : F)] (Q : QuadraticForm F V)
    {R : Submodule F V} (hR : (Q.restrict R).Nondegenerate) {c : F} (hc : c ≠ 0) :
    (planeForm Q R c).Nondegenerate :=
  hR.prod ((QuadraticMap.nondegenerate_smul_sq hc).prod (QuadraticMap.nondegenerate_smul_sq hc))

theorem quad_add_smul_smul (Q : QuadraticForm F V) {r a b : V} (hra : polar Q r a = 0)
    (hrb : polar Q r b = 0) (hab : polar Q a b = 0) (s t : F) :
    Q (r + s • a + t • b) = Q r + s ^ 2 * Q a + t ^ 2 * Q b := by
  have h1 : polar Q r (s • a + t • b) = 0 := by
    rw [polar_add_right, polar_smul_right, polar_smul_right, hra, hrb]
    simp
  rw [add_assoc, QuadraticMap.map_add (⇑Q), h1,
    CFSG.RankThree.Classical.quad_smul_add_smul Q hab]
  ring

@[expose] noncomputable def planeIsometry (Q : QuadraticForm F V) (R : Submodule F V) {c : F}
    {a b : V} (hra : ∀ r ∈ R, polar Q r a = 0) (hrb : ∀ r ∈ R, polar Q r b = 0)
    (hab : polar Q a b = 0) (ha : Q a = c) (hb : Q b = c) : planeForm Q R c →qᵢ Q where
  toLinearMap := planeMap R a b
  map_app' p := by
    change Q (planeMap R a b p) = planeForm Q R c p
    rw [planeMap_apply, planeForm_apply, quad_add_smul_smul Q (hra _ p.1.2) (hrb _ p.1.2) hab,
      ha, hb]
    ring

theorem planeIsometry_apply (Q : QuadraticForm F V) (R : Submodule F V) {c : F} {a b : V}
    (hra : ∀ r ∈ R, polar Q r a = 0) (hrb : ∀ r ∈ R, polar Q r b = 0)
    (hab : polar Q a b = 0) (ha : Q a = c) (hb : Q b = c) (p : R × (F × F)) :
    planeIsometry Q R hra hrb hab ha hb p = (p.1 : V) + p.2.1 • a + p.2.2 • b := rfl

section Witt

variable [Invertible (2 : F)] [FiniteDimensional F V]

theorem exists_isometry_plane (Q : QuadraticForm F V) {R : Submodule F V}
    (hR : (Q.restrict R).Nondegenerate) {c : F} (hc : c ≠ 0) {a b a' b' : V}
    (hra : ∀ r ∈ R, polar Q r a = 0) (hrb : ∀ r ∈ R, polar Q r b = 0)
    (hab : polar Q a b = 0) (ha : Q a = c) (hb : Q b = c)
    (hra' : ∀ r ∈ R, polar Q r a' = 0) (hrb' : ∀ r ∈ R, polar Q r b' = 0)
    (hab' : polar Q a' b' = 0) (ha' : Q a' = c) (hb' : Q b' = c) :
    ∃ Θ : Q.IsometryEquiv Q, (∀ r ∈ R, Θ r = r) ∧ Θ a = a' ∧ Θ b = b' := by
  set α := planeIsometry Q R hra hrb hab ha hb with hαdef
  set β := planeIsometry Q R hra' hrb' hab' ha' hb' with hβdef
  have hnd := planeForm_nondegenerate Q hR hc
  have hα : Function.Injective α := Isometry.injective_of_radical_eq_bot α hnd.radical_eq_bot
  have hβ : Function.Injective β := Isometry.injective_of_radical_eq_bot β hnd.radical_eq_bot
  have hreg := CFSG.ClassicalInvolution.PhanP.nondegenerate_range α hα hnd
  obtain ⟨Θ, hΘ⟩ := (CFSG.ClassicalInvolution.PhanP.rangeIsometry α β hα hβ).exists_extension hreg
  have key : ∀ p, Θ (α p) = β p := fun p => by
    have := hΘ ⟨α p, p, rfl⟩
    rw [CFSG.ClassicalInvolution.PhanP.rangeIsometry_apply α β hα hβ p] at this
    exact this
  refine ⟨Θ, fun r hr => ?_, ?_, ?_⟩
  · have := key (⟨r, hr⟩, 0, 0)
    simpa [hαdef, hβdef, planeIsometry_apply] using this
  · have := key (0, 1, 0)
    simpa [hαdef, hβdef, planeIsometry_apply] using this
  · have := key (0, 0, 1)
    simpa [hαdef, hβdef, planeIsometry_apply] using this

theorem exists_perp_vector (Q : QuadraticForm F V) (hQ : Q.Nondegenerate) {R : Submodule F V}
    (hR : (Q.restrict R).Nondegenerate) {c : F} (hc : c ≠ 0) {a b : V}
    (hra : ∀ r ∈ R, polar Q r a = 0) (hrb : ∀ r ∈ R, polar Q r b = 0)
    (hab : polar Q a b = 0) (ha : Q a = c) (hb : Q b = c)
    (hdim : Module.finrank F R + 2 < Module.finrank F V) :
    ∃ n : V, Q n ≠ 0 ∧ (∀ r ∈ R, polar Q r n = 0) ∧ polar Q a n = 0 ∧ polar Q b n = 0 := by
  set α := planeIsometry Q R hra hrb hab ha hb with hαdef
  have hnd := planeForm_nondegenerate Q hR hc
  have hα : Function.Injective α := Isometry.injective_of_radical_eq_bot α hnd.radical_eq_bot
  have hW := CFSG.ClassicalInvolution.PhanP.nondegenerate_range α hα hnd
  set W := LinearMap.range α.toLinearMap with hWdef
  have hP := hQ.nondegenerate_restrict_orthogonal hW
  have hcomp := hW.isCompl_orthogonal
  have hfin := Submodule.finrank_add_eq_of_isCompl hcomp
  have hW2 : Module.finrank F W = Module.finrank F R + 2 := by
    rw [hWdef, LinearMap.finrank_range_of_inj hα, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_self]
  have hpos : 0 < Module.finrank F (LinearMap.BilinForm.orthogonal Q.polarBilin W) := by omega
  have := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := hP.exists_isUnit
  have hvW : ∀ w ∈ W, polar Q w (v : V) = 0 := fun w hw => by
    have h1 : Q.polarBilin w (v : V) = 0 := v.2 w hw
    rwa [QuadraticMap.polarBilin_apply_apply] at h1
  refine ⟨v, ?_, fun r hr => ?_, ?_, ?_⟩
  · have := hv.ne_zero
    simpa using this
  · refine hvW r ⟨(⟨r, hr⟩, 0, 0), ?_⟩
    simp [hαdef, planeIsometry_apply]
  · refine hvW a ⟨(0, 1, 0), ?_⟩
    simp [hαdef, planeIsometry_apply]
  · refine hvW b ⟨(0, 0, 1), ?_⟩
    simp [hαdef, planeIsometry_apply]

end Witt

end CFSG.ClassicalInvolution.PhanB3.S
