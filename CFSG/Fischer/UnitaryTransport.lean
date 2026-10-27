module

public import CFSG.Fischer.Unitary
public import CFSG.Blueprint.FischerDefs

public section

namespace CFSG.Fischer

open Matrix Blueprint.Fischer

noncomputable abbrev ψ : F4 ≃+* K := F4.equivGaloisField

@[expose] noncomputable def ψGL : GL (Fin 6) F4 ≃* GL (Fin 6) K :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 6) ψ).toMulEquiv

theorem ψGL_val (g : GL (Fin 6) F4) :
    ((ψGL g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (RingEquiv.mapMatrix (m := Fin 6) ψ) (g : Matrix (Fin 6) (Fin 6) F4) := rfl

@[expose] noncomputable def ψV (x : Fin 6 → F4) : V := fun i => ψ (x i)

theorem ψV_surjective : Function.Surjective ψV := by
  intro y
  exact ⟨fun i => ψ.symm (y i), by funext i; simp [ψV]⟩

theorem ψV_injective : Function.Injective ψV := by
  intro x y h
  funext i
  exact ψ.injective (congrFun h i)

theorem mulVec_ψ (M : Matrix (Fin 6) (Fin 6) F4) (x : Fin 6 → F4) :
    (RingEquiv.mapMatrix (m := Fin 6) ψ M).mulVec (ψV x) = ψV (M.mulVec x) := by
  funext i
  simp only [ψV, mulVec, dotProduct, RingEquiv.mapMatrix_apply, Matrix.map_apply, map_sum,
    map_mul]

theorem hermitian_ψ (x y : Fin 6 → F4) : hermitian 1 (ψV x) (ψV y) = ψ (herm x y) := by
  unfold hermitian herm H0 ψV
  simp only [map_sum, map_mul, map_pow, Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem isNondegenerateHermitian_one : IsNondegenerateHermitian (1 : Matrix (Fin 6) (Fin 6) K) := by
  refine ⟨fun i j => ?_, fun x hx => ?_⟩
  · by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · funext j
    have := hx (Pi.single j 1)
    unfold hermitian at this
    simp only [Matrix.one_apply] at this
    rw [Finset.sum_eq_single j] at this
    · simpa [Pi.single_apply] using this
    · intro i _ hij
      simp [Pi.single_apply, hij]
    · simp

theorem det_ψGL (g : GL (Fin 6) F4) :
    Matrix.GeneralLinearGroup.det (ψGL g) = Units.map ψ.toRingHom.toMonoidHom
      (Matrix.GeneralLinearGroup.det g) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, ψGL_val, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [RingHom.map_det]
  rfl

theorem det_ψGL_eq_one_iff (g : GL (Fin 6) F4) :
    Matrix.GeneralLinearGroup.det (ψGL g) = 1 ↔ Matrix.GeneralLinearGroup.det g = 1 := by
  rw [det_ψGL]
  constructor
  · intro h
    apply Units.ext
    have := congrArg Units.val h
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      Units.val_one] at this
    apply ψ.injective
    rw [Units.val_one, map_one]
    exact this
  · intro h
    rw [h, map_one]

theorem isom_ψGL_iff (g : GL (Fin 6) F4) :
    (∀ x y : V, hermitian 1 ((ψGL g : Matrix (Fin 6) (Fin 6) K).mulVec x)
      ((ψGL g : Matrix (Fin 6) (Fin 6) K).mulVec y) = hermitian 1 x y) ↔
    ∀ x y : Fin 6 → F4, herm ((g : Matrix (Fin 6) (Fin 6) F4).mulVec x)
      ((g : Matrix (Fin 6) (Fin 6) F4).mulVec y) = herm x y := by
  constructor
  · intro h x y
    have := h (ψV x) (ψV y)
    rw [ψGL_val, mulVec_ψ, mulVec_ψ, hermitian_ψ, hermitian_ψ] at this
    exact ψ.injective this
  · intro h x y
    obtain ⟨x0, rfl⟩ := ψV_surjective x
    obtain ⟨y0, rfl⟩ := ψV_surjective y
    rw [ψGL_val, mulVec_ψ, mulVec_ψ, hermitian_ψ, hermitian_ψ, h]

theorem SU_eq_map : SU (1 : Matrix (Fin 6) (Fin 6) K) = SU0.map ψGL.toMonoidHom := by
  unfold SU SU0
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_image, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨hdet, hisom⟩
    refine ⟨ψGL.symm g, ⟨?_, ?_⟩, by simp⟩
    · rw [← det_ψGL_eq_one_iff, MulEquiv.apply_symm_apply]; exact hdet
    · rw [← isom_ψGL_iff, MulEquiv.apply_symm_apply]; exact hisom
  · rintro ⟨g0, ⟨hdet, hisom⟩, rfl⟩
    exact ⟨(det_ψGL_eq_one_iff g0).2 hdet, (isom_ψGL_iff g0).2 hisom⟩

@[expose] noncomputable def suEquiv : SU0 ≃* SU (1 : Matrix (Fin 6) (Fin 6) K) :=
  (SU0.equivMapOfInjective ψGL.toMonoidHom ψGL.injective).trans
    (MulEquiv.subgroupCongr SU_eq_map.symm)

theorem suEquiv_val (s : SU0) : ((suEquiv s : SU (1 : Matrix (Fin 6) (Fin 6) K)) :
    GL (Fin 6) K) = ψGL s := rfl

@[expose] noncomputable def psuEquiv :
    (SU0 ⧸ Subgroup.center SU0) ≃* PSU (1 : Matrix (Fin 6) (Fin 6) K) :=
  QuotientGroup.congr _ _ suEquiv (by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩ w
      obtain ⟨w0, rfl⟩ := suEquiv.surjective w
      show suEquiv w0 * suEquiv y = suEquiv y * suEquiv w0
      rw [← map_mul, ← map_mul, hy]
    · intro hz
      refine ⟨suEquiv.symm z, fun w => ?_, by simp⟩
      apply suEquiv.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz])

theorem psuEquiv_mk (s : SU0) :
    psuEquiv (QuotientGroup.mk s) = QuotientGroup.mk (suEquiv s) := rfl

end CFSG.Fischer
