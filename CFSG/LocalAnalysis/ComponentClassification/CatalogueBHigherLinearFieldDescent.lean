module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearField

noncomputable section

open Matrix

universe u

abbrev fixedField (K : Type u) [Field K] (sigma : K ≃+* K) : Subfield K :=
  CatalogueBLinearTwoDescent.fixedSubfield K sigma

theorem mem_fixedField (K : Type u) [Field K] (sigma : K ≃+* K) (x : K) :
    x ∈ fixedField K sigma ↔ sigma x = x :=
  CatalogueBLinearTwoDescent.mem_fixedSubfield K sigma x

theorem fixedField_coe (K : Type u) [Field K] (sigma : K ≃+* K)
    (x : fixedField K sigma) : sigma (x : K) = (x : K) :=
  (mem_fixedField K sigma x).mp x.property

theorem fixedField_finrank (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    Module.finrank (fixedField K sigma) K = 2 :=
  CatalogueBLinearTwoDescent.fixedSubfield_finrank K sigma hsigma hne

theorem fixedField_card_square (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    Nat.card K = Nat.card (fixedField K sigma) ^ 2 := by
  rw [← fixedField_finrank K sigma hsigma hne]
  exact Module.natCard_eq_pow_finrank

abbrev subfieldGLMap (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] (S : Subfield K) : GL ι S →* GL ι K :=
  GeneralLinearGroup.map S.subtype

theorem subfieldGLMap_injective (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] (S : Subfield K) :
    Function.Injective (subfieldGLMap ι K S) := by
  intro A B h
  apply GeneralLinearGroup.ext
  intro i j
  apply S.subtype.injective
  exact congrArg (fun C : GL ι K => C i j) h

abbrev subfieldPGLMap (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] (S : Subfield K) :
    ProjGenLinGroup ι S →* ProjGenLinGroup ι K :=
  ProjGenLinGroup.map S.subtype

theorem subfieldPGLMap_mk (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] (S : Subfield K) (A : GL ι S) :
    subfieldPGLMap ι K S (ProjGenLinGroup.mk A) =
      ProjGenLinGroup.mk (subfieldGLMap ι K S A) := rfl

theorem subfieldGLMap_scalar_reflect (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K : Type u) [Field K] (S : Subfield K)
    (A : GL ι S) (c : Kˣ)
    (hA : subfieldGLMap ι K S A = GeneralLinearGroup.scalar ι c) :
    ∃ b : Sˣ, A = GeneralLinearGroup.scalar ι b := by
  let i : ι := Classical.choice inferInstance
  have hii : ((A i i : S) : K) = (c : K) := by
    have h := congrArg (fun B : GL ι K => B i i) hA
    simpa only [GeneralLinearGroup.map_apply, Subfield.subtype_apply,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h
  have hne : A i i ≠ 0 := by
    intro hz
    apply c.ne_zero
    rw [← hii, hz]
    rfl
  let b : Sˣ := Units.mk0 (A i i) hne
  have hb : Units.map S.subtype b = c := by
    apply Units.ext
    exact hii
  refine ⟨b, subfieldGLMap_injective ι K S ?_⟩
  rw [show subfieldGLMap ι K S (GeneralLinearGroup.scalar ι b) =
    GeneralLinearGroup.scalar ι (Units.map S.subtype b) from
      GeneralLinearGroup.map_scalar S.subtype b, hb]
  exact hA

theorem subfieldPGLMap_injective (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K : Type u) [Field K] (S : Subfield K) :
    Function.Injective (subfieldPGLMap ι K S) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  change ProjGenLinGroup.mk (subfieldGLMap ι K S A) = 1 at hg
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨c, hc⟩ := hg
  obtain ⟨b, hb⟩ := subfieldGLMap_scalar_reflect ι K S A c hc.symm
  rw [hb]
  exact ProjGenLinGroup.mk_scalar b

theorem gl_exists_nonzero_entry (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (K : Type u) [Field K] (A : GL ι K) :
    ∃ i j : ι, A i j ≠ 0 := by
  by_contra h
  have hz : A.val = 0 := by
    ext i j
    exact not_not.mp (not_exists.mp (not_exists.mp h i) j)
  exact A.det_ne_zero (by rw [hz, Matrix.det_zero])

theorem exists_fixedField_GL (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] (sigma : K ≃+* K)
    (A : GL ι K) (hA : ∀ i j, sigma (A i j) = A i j) :
    ∃ B : GL ι (fixedField K sigma),
      subfieldGLMap ι K (fixedField K sigma) B = A := by
  let M : Matrix ι ι (fixedField K sigma) :=
    fun i j => ⟨A i j, (mem_fixedField K sigma (A i j)).mpr (hA i j)⟩
  have hM : (fixedField K sigma).subtype.mapMatrix M = A.val := rfl
  have hdet : M.det ≠ 0 := by
    intro hz
    apply A.det_ne_zero
    have h := congrArg (fixedField K sigma).subtype hz
    rw [map_zero, RingHom.map_det, hM] at h
    exact h
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hdet, ?_⟩
  apply GeneralLinearGroup.ext
  intro i j
  rfl

theorem normalized_entry_fixed (K : Type u) [Field K] (sigma : K ≃+* K)
    (x y : K) (hx : x ≠ 0) (c : Kˣ)
    (hxc : sigma x * (c : K) = x) (hyc : sigma y * (c : K) = y) :
    sigma (y / x) = y / x := by
  rw [map_div₀]
  apply (div_eq_div_iff (by exact fun h => hx (sigma.injective (h.trans (map_zero sigma).symm)))
    hx).mpr
  apply mul_right_cancel₀ c.ne_zero
  calc
    (sigma y * x) * (c : K) = (sigma y * (c : K)) * x := by ring
    _ = y * x := by rw [hyc]
    _ = y * (sigma x * (c : K)) := by rw [hxc]
    _ = (y * sigma x) * (c : K) := by ring

theorem fixed_projective_exists_subfield_matrix
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Type u) [Field K] (sigma : K ≃+* K) (A : GL ι K)
    (hfixed : pglFieldAut ι K sigma (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk A) :
    ∃ B : GL ι (fixedField K sigma),
      ProjGenLinGroup.mk (subfieldGLMap ι K (fixedField K sigma) B) =
        ProjGenLinGroup.mk A := by
  change ProjGenLinGroup.mk (GeneralLinearGroup.map sigma.toRingHom A) =
    ProjGenLinGroup.mk A at hfixed
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hfixed
  obtain ⟨i, j, hx⟩ := gl_exists_nonzero_entry ι K A
  have hentries (r s : ι) : sigma (A r s) * (c : K) = A r s := by
    have h := congrArg (fun B : GL ι K => B r s) hc
    change ((GeneralLinearGroup.map sigma.toRingHom A : Matrix ι ι K) *
      (Matrix.diagonal (fun _ : ι => (c : K)) : Matrix ι ι K)) r s = A r s at h
    rw [Matrix.mul_diagonal] at h
    exact h
  let b : Kˣ := (Units.mk0 (A i j) hx)⁻¹
  let T : GL ι K := A * GeneralLinearGroup.scalar ι b
  have hT (r s : ι) : T r s = A r s / A i j := by
    change ((A : Matrix ι ι K) *
      (Matrix.diagonal (fun _ : ι => (b : K)) : Matrix ι ι K)) r s = _
    rw [Matrix.mul_diagonal]
    simp [b, div_eq_mul_inv]
  have hTf (r s : ι) : sigma (T r s) = T r s := by
    rw [hT]
    exact normalized_entry_fixed K sigma (A i j) (A r s) hx c
      (hentries i j) (hentries r s)
  obtain ⟨B, hB⟩ := exists_fixedField_GL ι K sigma T hTf
  refine ⟨B, ?_⟩
  rw [hB]
  change ProjGenLinGroup.mk (A * GeneralLinearGroup.scalar ι b) = _
  rw [map_mul, ProjGenLinGroup.mk_scalar, mul_one]

theorem pgl_fixed_iff_mem_subfield_range
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Type u) [Field K] (sigma : K ≃+* K) (g : ProjGenLinGroup ι K) :
    pglFieldAut ι K sigma g = g ↔
      g ∈ (subfieldPGLMap ι K (fixedField K sigma)).range := by
  constructor
  · intro h
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
    obtain ⟨B, hB⟩ := fixed_projective_exists_subfield_matrix ι K sigma A h
    exact ⟨ProjGenLinGroup.mk B, hB⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
    change ProjGenLinGroup.mk (GeneralLinearGroup.map sigma.toRingHom
      (subfieldGLMap ι K (fixedField K sigma) A)) =
        ProjGenLinGroup.mk (subfieldGLMap ι K (fixedField K sigma) A)
    congr 1
    apply GeneralLinearGroup.ext
    intro i j
    exact fixedField_coe K sigma (A i j)

abbrev fixedPGL (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] (sigma : K ≃+* K) : Subgroup (ProjGenLinGroup ι K) :=
  TauCeti.fixedSubgroup (pglFieldAut ι K sigma).toMonoidHom

theorem subfieldPGL_range_eq_fixedPGL
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Type u) [Field K] (sigma : K ≃+* K) :
    (subfieldPGLMap ι K (fixedField K sigma)).range = fixedPGL ι K sigma := by
  ext g
  exact (pgl_fixed_iff_mem_subfield_range ι K sigma g).symm

@[expose] def subfieldPGLEquivFixed
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Type u) [Field K] (sigma : K ≃+* K) :
    ProjGenLinGroup ι (fixedField K sigma) ≃* fixedPGL ι K sigma :=
  (MonoidHom.ofInjective (subfieldPGLMap_injective ι K (fixedField K sigma))).trans
    (MulEquiv.subgroupCongr (subfieldPGL_range_eq_fixedPGL ι K sigma))

theorem subfieldPGLEquivFixed_val
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Type u) [Field K] (sigma : K ≃+* K)
    (g : ProjGenLinGroup ι (fixedField K sigma)) :
    (subfieldPGLEquivFixed ι K sigma g).val =
      subfieldPGLMap ι K (fixedField K sigma) g := rfl

end

end CFSG.ComponentClassification.CatalogueBHigherLinearField
