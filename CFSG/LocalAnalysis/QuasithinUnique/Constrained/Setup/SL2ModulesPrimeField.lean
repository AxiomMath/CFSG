module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups Matrix
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

section Endo

variable {F : Type*} [Field F]

theorem uElt_mulVec (t : F) (v : Fin 2 → F) :
    (uElt t : Matrix (Fin 2) (Fin 2) F) *ᵥ v = ![v 0 + t * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [coe_uElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lElt_mulVec (t : F) (v : Fin 2 → F) :
    (lElt t : Matrix (Fin 2) (Fin 2) F) *ᵥ v = ![v 0, t * v 0 + v 1] := by
  ext i
  fin_cases i <;> simp [lElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem pi_two_split (v : Fin 2 → F) : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
  ext i
  fin_cases i <;> simp

theorem endomorphism_scalar (f : (Fin 2 → F) →+ (Fin 2 → F))
    (hu : ∀ (t : F) (v : Fin 2 → F),
      f ((uElt t : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = (uElt t : Matrix (Fin 2) (Fin 2) F) *ᵥ f v)
    (hl : ∀ v : Fin 2 → F,
      f ((lElt (1 : F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (lElt (1 : F) : Matrix (Fin 2) (Fin 2) F) *ᵥ f v) :
    ∃ c : F, ∀ v, f v = c • v := by
  have hP1 : ∀ x : F, f (Pi.single 0 x) 1 = 0 := by
    intro x
    have h := congrFun (hu 1 (Pi.single 0 x)) 0
    have e : (uElt (1 : F) : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pi.single 0 x : Fin 2 → F) =
        Pi.single 0 x := by
      rw [uElt_mulVec]
      ext i
      fin_cases i <;> simp
    rw [e, uElt_mulVec] at h
    simpa using h
  have hQ0 : ∀ y : F, f (Pi.single 1 y) 0 = 0 := by
    intro y
    have h := congrFun (hl (Pi.single 1 y)) 1
    have e : (lElt (1 : F) : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pi.single 1 y : Fin 2 → F) =
        Pi.single 1 y := by
      rw [lElt_mulVec]
      ext i
      fin_cases i <;> simp
    rw [e, lElt_mulVec] at h
    simpa using h
  have hA : ∀ t y : F, f (Pi.single 0 (t * y)) 0 = t * f (Pi.single 1 y) 1 := by
    intro t y
    have h := congrFun (hu t (Pi.single 1 y)) 0
    have e : (uElt t : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pi.single 1 y : Fin 2 → F) =
        Pi.single 0 (t * y) + Pi.single 1 y := by
      rw [uElt_mulVec]
      ext i
      fin_cases i <;> simp
    rw [e, map_add, uElt_mulVec] at h
    simp only [Pi.add_apply, Matrix.cons_val_zero] at h
    rw [hQ0 y] at h
    simpa using h
  have hAQ : ∀ y : F, f (Pi.single 0 y) 0 = f (Pi.single 1 y) 1 := by
    intro y
    have h := hA 1 y
    rwa [one_mul, one_mul] at h
  have hAc : ∀ t : F, f (Pi.single 0 t) 0 = t * f (Pi.single 0 1) 0 := by
    intro t
    have h := hA t 1
    rw [mul_one, ← hAQ 1] at h
    exact h
  refine ⟨f (Pi.single 0 1) 0, fun v => ?_⟩
  have hv : f v = f (Pi.single 0 (v 0)) + f (Pi.single 1 (v 1)) := by
    conv_lhs => rw [pi_two_split v]
    rw [map_add]
  ext i
  fin_cases i
  · show f v 0 = f (Pi.single 0 1) 0 * v 0
    rw [hv, Pi.add_apply, hQ0, add_zero, hAc, mul_comm]
  · show f v 1 = f (Pi.single 0 1) 0 * v 1
    rw [hv, Pi.add_apply, hP1, zero_add, ← hAQ, hAc, mul_comm]

end Endo

section Semilinear

variable {F : Type*} [Field F]

@[expose] def natEndHom (F : Type*) [Field F] : SL(2, F) →* AddMonoid.End (Fin 2 → F) where
  toFun g := AddMonoidHom.mk' (fun v => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
    (fun v w => Matrix.mulVec_add _ _ _)
  map_one' := AddMonoidHom.ext fun v => by
    show ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  map_mul' g h := AddMonoidHom.ext fun v => by
    show ((g * h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
      (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

theorem natEndHom_apply (g : SL(2, F)) (v : Fin 2 → F) :
    natEndHom F g v = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v := rfl

@[expose] noncomputable def natEnd (F : Type*) [Field F] :
    SL(2, F) →* (AddMonoid.End (Fin 2 → F))ˣ :=
  (natEndHom F).toHomUnits

theorem natEnd_val (g : SL(2, F)) : (natEnd F g).val = natEndHom F g := rfl

@[expose] def semilinEnd (g : Matrix (Fin 2) (Fin 2) F) (σ : RingAut F) :
    AddMonoid.End (Fin 2 → F) :=
  AddMonoidHom.mk' (fun v => g *ᵥ (fun i => σ (v i))) (fun v w => by
    have h : (fun i => σ ((v + w) i)) = (fun i => σ (v i)) + (fun i => σ (w i)) :=
      funext fun i => map_add σ (v i) (w i)
    rw [h, Matrix.mulVec_add])

theorem semilinEnd_apply (g : Matrix (Fin 2) (Fin 2) F) (σ : RingAut F) (v : Fin 2 → F) :
    semilinEnd g σ v = g *ᵥ (fun i => σ (v i)) := rfl

@[expose] def semilinInv (g : Matrix (Fin 2) (Fin 2) F) (σ : RingAut F) :
    AddMonoid.End (Fin 2 → F) :=
  AddMonoidHom.mk' (fun w => fun i => σ.symm ((g *ᵥ w) i)) (fun v w => by
    funext i
    simp [Matrix.mulVec_add])

@[expose] def semilin (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : RingAut F) :
    (AddMonoid.End (Fin 2 → F))ˣ where
  val := semilinEnd (g : Matrix (Fin 2) (Fin 2) F) σ
  inv := semilinInv (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) σ
  val_inv := AddMonoidHom.ext fun w => by
    show (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (σ.symm (((((g⁻¹ :
      Matrix.GeneralLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w) i))) = w
    have h : (fun i => σ (σ.symm (((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) *ᵥ w) i))) = ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) *ᵥ w) := funext fun i => σ.apply_symm_apply _
    rw [h, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  inv_val := AddMonoidHom.ext fun v => by
    show (fun i => σ.symm (((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F) *ᵥ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (v i)))) i)) = v
    funext i
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact σ.symm_apply_apply (v i)

theorem semilin_apply (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : RingAut F) (v : Fin 2 → F) :
    (semilin g σ).val v = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (v i)) := rfl

theorem semilin_inv_apply (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : RingAut F)
    (w : Fin 2 → F) :
    ((semilin g σ)⁻¹).val w = fun i => σ.symm ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) *ᵥ w) i) := rfl

@[expose] def scalEnd (c : F) : AddMonoid.End (Fin 2 → F) :=
  AddMonoidHom.mk' (fun v => c • v) (fun v w => smul_add c v w)

theorem scalEnd_apply (c : F) (v : Fin 2 → F) : scalEnd c v = c • v := rfl

@[expose] def scalMonoidHom (F : Type*) [Field F] : F →* AddMonoid.End (Fin 2 → F) where
  toFun := scalEnd
  map_one' := AddMonoidHom.ext fun v => one_smul F v
  map_mul' c d := AddMonoidHom.ext fun v => mul_smul c d v

@[expose] def scalHom (F : Type*) [Field F] : Fˣ →* (AddMonoid.End (Fin 2 → F))ˣ :=
  Units.map (scalMonoidHom F)

theorem scalHom_apply (c : Fˣ) (v : Fin 2 → F) : (scalHom F c).val v = (c : F) • v := rfl

theorem semilin_conj_natEnd (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : RingAut F)
    (s : SL(2, F)) :
    ∃ s' : SL(2, F), semilin g σ * natEnd F s * (semilin g σ)⁻¹ = natEnd F s' := by
  have hdet : Matrix.det ((g : Matrix (Fin 2) (Fin 2) F) *
      ((s : Matrix (Fin 2) (Fin 2) F).map σ) *
      (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) = 1 := by
    rw [Matrix.det_units_conj]
    have h := RingHom.map_det σ.toRingHom (s : Matrix (Fin 2) (Fin 2) F)
    rw [s.2, map_one] at h
    exact h.symm
  refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) F) * ((s : Matrix (Fin 2) (Fin 2) F).map σ) *
    (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F), hdet⟩, ?_⟩
  apply Units.ext
  refine AddMonoidHom.ext fun w => ?_
  show (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (((s : Matrix (Fin 2) (Fin 2) F) *ᵥ
    (fun i => σ.symm ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) *ᵥ w) i))) i)) =
    ((g : Matrix (Fin 2) (Fin 2) F) * ((s : Matrix (Fin 2) (Fin 2) F).map σ) *
    (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) *ᵥ w
  have key : (fun i => σ (((s : Matrix (Fin 2) (Fin 2) F) *ᵥ
      (fun i => σ.symm ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) *ᵥ w) i))) i)) =
      ((s : Matrix (Fin 2) (Fin 2) F).map σ) *ᵥ ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) *ᵥ w) := by
    funext i
    have h := RingHom.map_mulVec σ.toRingHom (s : Matrix (Fin 2) (Fin 2) F)
      (fun j => σ.symm ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) *ᵥ w) j)) i
    have h2 : (σ.toRingHom ∘ fun j => σ.symm ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) *ᵥ w) j)) = ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) *ᵥ w) := funext fun j => σ.apply_symm_apply _
    rw [h2] at h
    exact h
  rw [key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Semilinear

section Normalizer

variable {F : Type*} [Field F] [Finite F]

theorem finite_units_addEnd : Finite (AddMonoid.End (Fin 2 → F))ˣ := by
  have : Finite (AddMonoid.End (Fin 2 → F)) :=
    Finite.of_injective (fun f : AddMonoid.End (Fin 2 → F) => (f : (Fin 2 → F) → (Fin 2 → F)))
      DFunLike.coe_injective
  infer_instance

theorem semilin_mem_normalizer (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : RingAut F) :
    semilin g σ ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) := by
  have := finite_units_addEnd (F := F)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := semilin_conj_natEnd g σ s
    exact ⟨s', hs'.symm⟩
  · intro hx
    have hmap : ∀ y : (natEnd F).range,
        semilin g σ * (y : (AddMonoid.End (Fin 2 → F))ˣ) * (semilin g σ)⁻¹ ∈ (natEnd F).range := by
      rintro ⟨_, s, rfl⟩
      obtain ⟨s', hs'⟩ := semilin_conj_natEnd g σ s
      exact ⟨s', hs'.symm⟩
    let f : (natEnd F).range → (natEnd F).range := fun y => ⟨_, hmap y⟩
    have hfinj : Function.Injective f := fun a b hab => by
      have h1 : semilin g σ * (a : (AddMonoid.End (Fin 2 → F))ˣ) * (semilin g σ)⁻¹ =
          semilin g σ * (b : (AddMonoid.End (Fin 2 → F))ˣ) * (semilin g σ)⁻¹ :=
        congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hfinj ⟨_, hx⟩
    have h1 : semilin g σ * (y : (AddMonoid.End (Fin 2 → F))ˣ) * (semilin g σ)⁻¹ =
        semilin g σ * x * (semilin g σ)⁻¹ := congrArg Subtype.val hy
    have h2 : (y : (AddMonoid.End (Fin 2 → F))ˣ) = x := mul_left_cancel (mul_right_cancel h1)
    rw [← h2]
    exact y.2

theorem exists_semilin_of_mem_normalizer (h : (AddMonoid.End (Fin 2 → F))ˣ)
    (hN : h ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ)) :
    ∃ (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : RingAut F), h = semilin g σ := by
  classical
  have hh : ∀ v, h.val ((h⁻¹).val v) = v := fun v => by
    have := congrArg (fun u : AddMonoid.End (Fin 2 → F) => u v) (Units.mul_inv h)
    exact this
  have hh' : ∀ v, (h⁻¹).val (h.val v) = v := fun v => by
    have := congrArg (fun u : AddMonoid.End (Fin 2 → F) => u v) (Units.inv_mul h)
    exact this
  have hR : ∀ s : SL(2, F), ∃ s' : SL(2, F), ∀ x,
      natEndHom F s (h.val x) = h.val (natEndHom F s' x) := by
    intro s
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) (natEnd F s)).mp ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := h1
    refine ⟨s', fun x => ?_⟩
    have h2 : h * natEnd F s' = natEnd F s * h := by
      rw [hs', inv_inv]
      group
    have h3 := congrArg (fun u : (AddMonoid.End (Fin 2 → F))ˣ => u.val x) h2
    exact h3.symm
  let T : F → AddMonoid.End (Fin 2 → F) := fun c => h.val.comp ((scalEnd c).comp (h⁻¹).val)
  have hT : ∀ c v, T c v = h.val (c • (h⁻¹).val v) := fun c v => rfl
  have hTcomm : ∀ (c : F) (s : SL(2, F)) (v : Fin 2 → F),
      T c ((s : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = (s : Matrix (Fin 2) (Fin 2) F) *ᵥ T c v := by
    intro c s v
    obtain ⟨s', hs'⟩ := hR s
    have e1 : (h⁻¹).val ((s : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (s' : Matrix (Fin 2) (Fin 2) F) *ᵥ (h⁻¹).val v := by
      have h4 := hs' ((h⁻¹).val v)
      rw [hh] at h4
      have h5 := congrArg (h⁻¹).val h4
      rw [hh'] at h5
      exact h5
    rw [hT, e1, hT]
    have e2 := hs' (c • (h⁻¹).val v)
    rw [← Matrix.mulVec_smul]
    exact e2.symm
  have hex : ∀ c : F, ∃ d : F, ∀ v, T c v = d • v := fun c =>
    endomorphism_scalar (T c) (fun t v => hTcomm c (uElt t) v)
      (fun v => hTcomm c (lElt (1 : F)) v)
  choose σ0 hσ0 using hex
  have hK : ∀ (c : F) (w : Fin 2 → F), h.val (c • w) = σ0 c • h.val w := by
    intro c w
    have h4 := hσ0 c (h.val w)
    rw [hT, hh'] at h4
    exact h4
  let w0 : Fin 2 → F := (h⁻¹).val (Pi.single 0 1)
  have hw0 : h.val w0 = Pi.single 0 1 := hh _
  have hσ : ∀ c, σ0 c = h.val (c • w0) 0 := by
    intro c
    rw [hK, hw0]
    simp
  have hσ_add : ∀ c d, σ0 (c + d) = σ0 c + σ0 d := by
    intro c d
    rw [hσ, hσ, hσ, add_smul, map_add]
    rfl
  have hσ_mul : ∀ c d, σ0 (c * d) = σ0 c * σ0 d := by
    intro c d
    rw [hσ (c * d), mul_smul, hK c (d • w0)]
    show σ0 c * h.val (d • w0) 0 = σ0 c * σ0 d
    rw [hσ d]
  have hσ_one : σ0 1 = 1 := by
    rw [hσ, one_smul, hw0]
    simp
  have hσ_zero : σ0 0 = 0 := by
    rw [hσ, zero_smul, map_zero]
    rfl
  let σr : F →+* F :=
    { toFun := σ0
      map_one' := hσ_one
      map_mul' := hσ_mul
      map_zero' := hσ_zero
      map_add' := hσ_add }
  have hσinj : Function.Injective σr := σr.injective
  let σ : RingAut F := RingEquiv.ofBijective σr ⟨hσinj, Finite.surjective_of_injective hσinj⟩
  have hσapp : ∀ c, σ c = σ0 c := fun c => rfl
  let M : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => h.val (Pi.single j 1) i
  have hS5 : ∀ v : Fin 2 → F, h.val v = M *ᵥ (fun i => σ (v i)) := by
    intro v
    have hv : v = (v 0) • (Pi.single 0 1 : Fin 2 → F) + (v 1) • (Pi.single 1 1 : Fin 2 → F) := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hv]
    rw [map_add, hK, hK]
    ext i
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hσapp, mul_comm]
  have hMinj : Function.Injective (Matrix.mulVec M) := by
    intro x y hxy
    have e : ∀ z : Fin 2 → F, M *ᵥ z = h.val (fun i => σ.symm (z i)) := by
      intro z
      rw [hS5]
      congr 1
      funext i
      exact (σ.apply_symm_apply (z i)).symm
    have h1 : h.val (fun i => σ.symm (x i)) = h.val (fun i => σ.symm (y i)) := by
      rw [← e, ← e]
      exact hxy
    have h2 := congrArg (h⁻¹).val h1
    rw [hh', hh'] at h2
    funext i
    exact σ.symm.injective (congrFun h2 i)
  have hMunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hMinj
  refine ⟨hMunit.unit, σ, ?_⟩
  apply Units.ext
  refine AddMonoidHom.ext fun v => ?_
  show h.val v = M *ᵥ (fun i => σ (v i))
  exact hS5 v

omit [Finite F] in
theorem semilin_unique {g g' : Matrix.GeneralLinearGroup (Fin 2) F} {σ σ' : RingAut F}
    (h : semilin g σ = semilin g' σ') : g = g' ∧ σ = σ' := by
  have hv : ∀ v : Fin 2 → F, (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (v i)) =
      (g' : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ' (v i)) := fun v =>
    congrArg (fun u : (AddMonoid.End (Fin 2 → F))ˣ => u.val v) h
  have hgg : g = g' := by
    apply Units.ext
    ext i j
    have h1 := congrFun (hv (Pi.single j 1)) i
    have e : ∀ τ : RingAut F, (fun k => τ ((Pi.single j 1 : Fin 2 → F) k)) = Pi.single j 1 := by
      intro τ
      ext k
      by_cases hk : k = j <;> simp [hk]
    rw [e σ, e σ', Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h1
    exact h1
  refine ⟨hgg, ?_⟩
  subst hgg
  have hinj : Function.Injective (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) F)) :=
    Matrix.mulVec_injective_iff_isUnit.mpr g.isUnit
  ext c
  have h1 := hinj (hv (Pi.single 0 c))
  have h2 := congrFun h1 0
  simpa using h2

omit [Finite F] in
theorem scalHom_commute_natEnd (c : Fˣ) (s : SL(2, F)) :
    scalHom F c * natEnd F s = natEnd F s * scalHom F c := by
  apply Units.ext
  refine AddMonoidHom.ext fun v => ?_
  show (c : F) • ((s : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = (s : Matrix (Fin 2) (Fin 2) F) *ᵥ ((c : F) • v)
  rw [Matrix.mulVec_smul]

omit [Finite F] in
theorem scalHom_eq_semilin (c : Fˣ) :
    scalHom F c = semilin (Units.map (Matrix.scalar (Fin 2)).toMonoidHom c) 1 := by
  apply Units.ext
  refine AddMonoidHom.ext fun v => ?_
  show (c : F) • v = (Matrix.scalar (Fin 2) (c : F)) *ᵥ (fun i => (1 : RingAut F) (v i))
  ext i
  simp

theorem normalizer_centralizer_root_iff (h : (AddMonoid.End (Fin 2 → F))ˣ) :
    (h ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) ∧
        ∀ t : F, h * natEnd F (uElt t) = natEnd F (uElt t) * h) ↔
      ∃ (c : Fˣ) (t : F), h = scalHom F c * natEnd F (uElt t) := by
  constructor
  · rintro ⟨hN, hcomm⟩
    obtain ⟨g, σ, rfl⟩ := exists_semilin_of_mem_normalizer h hN
    have hv : ∀ (t : F) (v : Fin 2 → F),
        (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (((uElt t : Matrix (Fin 2) (Fin 2) F) *ᵥ v) i)) =
          (uElt t : Matrix (Fin 2) (Fin 2) F) *ᵥ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (v i))) :=
      fun t v => congrArg (fun u : (AddMonoid.End (Fin 2 → F))ˣ => u.val v) (hcomm t)
    have hg0 : ∀ w : Fin 2 → F, ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ w) 0 =
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 * w 0 + (g : Matrix (Fin 2) (Fin 2) F) 0 1 * w 1 := by
      intro w
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hg1 : ∀ w : Fin 2 → F, ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ w) 1 =
        (g : Matrix (Fin 2) (Fin 2) F) 1 0 * w 0 + (g : Matrix (Fin 2) (Fin 2) F) 1 1 * w 1 := by
      intro w
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h0f : ∀ t : F, (g : Matrix (Fin 2) (Fin 2) F) 0 0 * σ t + (g : Matrix (Fin 2) (Fin 2) F) 0 1 =
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 + t * (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
      intro t
      have h := congrFun (hv t (Pi.single 1 1)) 0
      simp only [uElt_mulVec, hg0, hg1] at h
      simpa using h
    have h0 : ∀ t : F, (g : Matrix (Fin 2) (Fin 2) F) 0 0 * σ t =
        t * (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
      intro t
      have h := h0f t
      rw [add_comm ((g : Matrix (Fin 2) (Fin 2) F) 0 1)] at h
      exact add_right_cancel h
    have hcc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have h := congrFun (hv 1 (Pi.single 1 1)) 1
      simp only [uElt_mulVec, hg0, hg1] at h
      simpa using h
    have hda : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      have h := h0 1
      rw [map_one] at h
      simpa using h.symm
    have ha0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro ha
      have hdet := (Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin 2) (Fin 2) F)).mp g.isUnit
      rw [Matrix.det_fin_two, hcc, hda, ha] at hdet
      simp at hdet
    have hσt : ∀ t : F, σ t = t := by
      intro t
      have h := h0 t
      rw [hda] at h
      apply mul_left_cancel₀ ha0
      rw [h, mul_comm]
    refine ⟨Units.mk0 _ ha0, (g : Matrix (Fin 2) (Fin 2) F) 0 1 / (g : Matrix (Fin 2) (Fin 2) F) 0 0,
      ?_⟩
    apply Units.ext
    refine AddMonoidHom.ext fun v => ?_
    show (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (v i)) =
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 • ((uElt ((g : Matrix (Fin 2) (Fin 2) F) 0 1 /
        (g : Matrix (Fin 2) (Fin 2) F) 0 0) : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, hg0, hσt, uElt_mulVec, Pi.smul_apply, smul_eq_mul]
      simp
      field_simp
    · simp only [Fin.mk_one, hg1, hσt, uElt_mulVec, Pi.smul_apply, smul_eq_mul, hcc, hda]
      simp
  · rintro ⟨c, t, rfl⟩
    refine ⟨?_, fun t' => ?_⟩
    · rw [scalHom_eq_semilin]
      exact Subgroup.mul_mem _ (semilin_mem_normalizer _ _) (Subgroup.le_normalizer ⟨_, rfl⟩)
    · have hUU : natEnd F (uElt t) * natEnd F (uElt t') = natEnd F (uElt t') * natEnd F (uElt t) := by
        rw [← map_mul, ← map_mul, ← uElt_add, ← uElt_add, add_comm]
      calc scalHom F c * natEnd F (uElt t) * natEnd F (uElt t')
          = scalHom F c * (natEnd F (uElt t) * natEnd F (uElt t')) := mul_assoc _ _ _
        _ = scalHom F c * (natEnd F (uElt t') * natEnd F (uElt t)) := by rw [hUU]
        _ = (scalHom F c * natEnd F (uElt t')) * natEnd F (uElt t) := (mul_assoc _ _ _).symm
        _ = (natEnd F (uElt t') * scalHom F c) * natEnd F (uElt t) := by
            rw [scalHom_commute_natEnd]
        _ = natEnd F (uElt t') * (scalHom F c * natEnd F (uElt t)) := mul_assoc _ _ _

omit [Finite F] in
theorem natEnd_uElt_apply_e0 (t : F) :
    (natEnd F (uElt t)).val (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1 := by
  show (uElt t : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1
  rw [uElt_mulVec]
  ext i
  fin_cases i <;> simp

omit [Finite F] in
theorem scalHom_natEnd_injective :
    Function.Injective (fun p : Fˣ × F => scalHom F p.1 * natEnd F (uElt p.2)) := by
  rintro ⟨c, t⟩ ⟨c', t'⟩ h
  have h0 := congrArg (fun u : (AddMonoid.End (Fin 2 → F))ˣ => u.val (Pi.single 0 1)) h
  simp only [Units.val_mul] at h0
  have e0 : ∀ (d : Fˣ) (s : F), (scalHom F d * natEnd F (uElt s)).val (Pi.single 0 1) =
      (d : F) • (Pi.single 0 1 : Fin 2 → F) := by
    intro d s
    show (scalHom F d).val ((natEnd F (uElt s)).val (Pi.single 0 1)) = _
    rw [natEnd_uElt_apply_e0]
    rfl
  have hcc : c = c' := by
    have h1 : (c : F) • (Pi.single 0 1 : Fin 2 → F) = (c' : F) • Pi.single 0 1 := by
      rw [← e0 c t, ← e0 c' t']
      exact h0
    have h2 := congrFun h1 0
    simp at h2
    exact Units.ext h2
  subst hcc
  have h3 : natEnd F (uElt t) = natEnd F (uElt t') := mul_left_cancel h
  have h4 := congrArg (fun u : (AddMonoid.End (Fin 2 → F))ˣ => u.val (Pi.single 1 1)) h3
  have h5 := congrFun h4 0
  have h6 : t = t' := by simpa [natEnd_val, natEndHom_apply, coe_uElt] using h5
  rw [h6]

omit [Finite F] in
theorem coprime_card_units {p : ℕ} [hp : Fact p.Prime] [CharP F p] [Fintype F] :
    Nat.Coprime p (Nat.card Fˣ) := by
  classical
  obtain ⟨n, -, hF⟩ := FiniteField.card F p
  rw [Nat.card_eq_fintype_card, Fintype.card_units, hF]
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  have h2 : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.pos.ne'
  have h3 : 1 ≤ p ^ (n : ℕ) := Nat.one_le_pow _ _ hp.out.pos
  have h4 : p ∣ 1 := by
    have := Nat.dvd_sub h2 h
    rwa [Nat.sub_sub_self h3] at this
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp h4)

theorem pSubgroup_centralizer_root {p : ℕ} [hp : Fact p.Prime] [CharP F p] [Fintype F]
    (P : Subgroup (AddMonoid.End (Fin 2 → F))ˣ)
    (hP : ∀ x ∈ P, x ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) ∧
      ∀ t : F, x * natEnd F (uElt t) = natEnd F (uElt t) * x)
    (hpg : IsPGroup p P) (x : (AddMonoid.End (Fin 2 → F))ˣ) (hx : x ∈ P) :
    ∃ t : F, x = natEnd F (uElt t) := by
  obtain ⟨c, t, rfl⟩ := (normalizer_centralizer_root_iff x).mp (hP x hx)
  obtain ⟨k, hk⟩ := hpg ⟨_, hx⟩
  have hk' : (scalHom F c * natEnd F (uElt t)) ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have hcomm : Commute (scalHom F c) (natEnd F (uElt t)) := scalHom_commute_natEnd c (uElt t)
  rw [hcomm.mul_pow, ← map_pow (scalHom F)] at hk'
  have h0 := congrArg (fun u : (AddMonoid.End (Fin 2 → F))ˣ => u.val (Pi.single 0 1)) hk'
  have hfix : ∀ m : ℕ, ((natEnd F (uElt t)) ^ m).val (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ, Units.val_mul]
      show ((natEnd F (uElt t) ^ m).val) ((natEnd F (uElt t)).val (Pi.single 0 1)) = _
      rw [natEnd_uElt_apply_e0, ih]
  have hc : c ^ (p ^ k) = 1 := by
    have h1 : (scalHom F (c ^ (p ^ k)) * (natEnd F (uElt t)) ^ (p ^ k)).val (Pi.single 0 1) =
        ((c ^ (p ^ k) : Fˣ) : F) • (Pi.single 0 1 : Fin 2 → F) := by
      rw [Units.val_mul]
      show (scalHom F (c ^ (p ^ k))).val (((natEnd F (uElt t)) ^ (p ^ k)).val (Pi.single 0 1)) = _
      rw [hfix]
      rfl
    have h2 : ((c ^ (p ^ k) : Fˣ) : F) • (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1 := by
      rw [← h1]
      exact h0
    have h3 := congrFun h2 0
    simp at h3
    exact Units.ext h3
  have hc1 : c = 1 := by
    have hord : orderOf c ∣ p ^ k := orderOf_dvd_of_pow_eq_one hc
    have hord2 : orderOf c ∣ Nat.card Fˣ := orderOf_dvd_natCard c
    have hcop : Nat.Coprime (orderOf c) (Nat.card Fˣ) :=
      Nat.Coprime.coprime_dvd_left hord (Nat.Coprime.pow_left k coprime_card_units)
    have : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd hcop hord2
    exact orderOf_eq_one_iff.mp this
  exact ⟨t, by rw [hc1, map_one, one_mul]⟩

end Normalizer

section Main

variable {F : Type*} [Field F] [Fintype F]

theorem natural_SL2_prime_field_normalizer {p : ℕ} [Fact p.Prime] [CharP F p] :
    (∀ f : AddMonoid.End (Fin 2 → F),
      (∀ s : SL(2, F), f * natEndHom F s = natEndHom F s * f) ↔ ∃ c : F, f = scalEnd c) ∧
    (∀ h : (AddMonoid.End (Fin 2 → F))ˣ,
      h ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) ↔
        ∃ (g : Matrix.GeneralLinearGroup (Fin 2) F) (σ : RingAut F), h = semilin g σ) ∧
    (∀ (g g' : Matrix.GeneralLinearGroup (Fin 2) F) (σ σ' : RingAut F),
      semilin g σ = semilin g' σ' → g = g' ∧ σ = σ') ∧
    (∀ h : (AddMonoid.End (Fin 2 → F))ˣ,
      (h ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) ∧
        ∀ t : F, h * natEnd F (uElt t) = natEnd F (uElt t) * h) ↔
        ∃ (c : Fˣ) (t : F), h = scalHom F c * natEnd F (uElt t)) ∧
    (∀ (c : Fˣ) (t : F), scalHom F c * natEnd F (uElt t) = natEnd F (uElt t) * scalHom F c) ∧
    Function.Injective (fun q : Fˣ × F => scalHom F q.1 * natEnd F (uElt q.2)) ∧
    (∀ P : Subgroup (AddMonoid.End (Fin 2 → F))ˣ,
      (∀ x ∈ P, x ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) ∧
        ∀ t : F, x * natEnd F (uElt t) = natEnd F (uElt t) * x) →
      IsPGroup p P → ∀ x ∈ P, ∃ t : F, x = natEnd F (uElt t)) := by
  refine ⟨?_, fun h => ⟨exists_semilin_of_mem_normalizer h, ?_⟩, fun g g' σ σ' => semilin_unique,
    normalizer_centralizer_root_iff, fun c t => scalHom_commute_natEnd c (uElt t),
    scalHom_natEnd_injective, fun P hP hpg x hx => pSubgroup_centralizer_root P hP hpg x hx⟩
  · intro f
    constructor
    · intro hf
      obtain ⟨c, hc⟩ := endomorphism_scalar f
        (fun t v => congrArg (fun u : AddMonoid.End (Fin 2 → F) => u v) (hf (uElt t)))
        (fun v => congrArg (fun u : AddMonoid.End (Fin 2 → F) => u v) (hf (lElt (1 : F))))
      exact ⟨c, AddMonoidHom.ext hc⟩
    · rintro ⟨c, rfl⟩ s
      refine AddMonoidHom.ext fun v => ?_
      show c • ((s : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = (s : Matrix (Fin 2) (Fin 2) F) *ᵥ (c • v)
      rw [Matrix.mulVec_smul]
  · rintro ⟨g, σ, rfl⟩
    exact semilin_mem_normalizer g σ

end Main

end CFSG.QuasithinUnique.Setup.SL2Modules
