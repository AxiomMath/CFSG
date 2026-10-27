module

public import CFSG.LieType.Chevalley.WeylRoots
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem Matrix

theorem posDef_map_ratCast {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℚ}
    (hM : M.PosDef) : (M.map (Rat.cast : ℚ → ℝ)).PosDef := by
  have hherm : (M.map (Rat.cast : ℚ → ℝ)).IsHermitian :=
    hM.isHermitian.map _ fun x => by simp
  have hpsd : (M.map (Rat.cast : ℚ → ℝ)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
    rw [star_trivial]
    have hdense : DenseRange (Pi.map fun _ : ι => (Rat.cast : ℚ → ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hdense.induction_on (p := fun x : ι → ℝ => 0 ≤ x ⬝ᵥ (M.map (Rat.cast : ℚ → ℝ) *ᵥ x))
      x (isClosed_le continuous_const
        (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))) fun y => ?_
    have hy := hM.posSemidef.dotProduct_mulVec_nonneg y
    rw [star_trivial] at hy
    have h : Pi.map (fun _ : ι => (Rat.cast : ℚ → ℝ)) y ⬝ᵥ
        (M.map (Rat.cast : ℚ → ℝ) *ᵥ Pi.map (fun _ : ι => (Rat.cast : ℚ → ℝ)) y) =
          ((y ⬝ᵥ (M *ᵥ y) : ℚ) : ℝ) := by
      rw [show ((y ⬝ᵥ (M *ᵥ y) : ℚ) : ℝ) = Rat.castHom ℝ (y ⬝ᵥ (M *ᵥ y)) from rfl,
        RingHom.map_dotProduct]
      congr 1
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec]
      rfl
    rw [h]
    exact_mod_cast hy
  rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hdet : (M.map (Rat.cast : ℚ → ℝ)).det = ((M.det : ℚ) : ℝ) := by
    rw [show ((M.det : ℚ) : ℝ) = Rat.castHom ℝ M.det from rfl, RingHom.map_det]
    rfl
  rw [hdet]
  exact_mod_cast hM.det_pos.ne'

@[expose] def formMatrix (τ : Tag) : Matrix (Fin τ.rank) (Fin τ.rank) ℝ :=
  (symmetrized (isFiniteType_cartan τ)).map (Rat.cast : ℚ → ℝ)

theorem posDef_formMatrix (τ : Tag) : (formMatrix τ).PosDef :=
  posDef_map_ratCast (posDef_symmetrized _)

theorem symmetrized_cartan_apply (τ : Tag) (i j : Fin τ.rank) :
    symmetrized (isFiniteType_cartan τ) i j =
      symmetrizer (isFiniteType_cartan τ) i * (τ.cartan i j : ℚ) := by
  have h := form_single_left (isFiniteType_cartan τ) i (Pi.single j 1)
  rw [form_apply, single_dotProduct, one_mul, mulVec_single_one] at h
  simpa [Pi.single_apply] using h

theorem formMatrix_apply (τ : Tag) (i j : Fin τ.rank) :
    formMatrix τ i j = (symmetrizer (isFiniteType_cartan τ) i : ℝ) * (τ.cartan i j : ℝ) := by
  simp [formMatrix, symmetrized_cartan_apply]

theorem symmetrizedCartan_apply (τ : Tag) (i j : Fin τ.rank) :
    τ.symmetrizedCartan i j = τ.symmetrizer i i * τ.cartan i j := by
  cases τ
  case G2 | F4 => fin_cases i <;> fin_cases j <;> rfl
  all_goals simp [Tag.symmetrizedCartan, Tag.symmetrizer]

theorem symmetrizer_mul_cartan (τ : Tag) {i j : Fin τ.rank} {a b : ℤ}
    (hij : τ.cartan i j = a) (hji : τ.cartan j i = b) :
    symmetrizer (isFiniteType_cartan τ) i * a = symmetrizer (isFiniteType_cartan τ) j * b := by
  have h := (posDef_symmetrized (isFiniteType_cartan τ)).isHermitian.apply j i
  rw [symmetrized_cartan_apply, symmetrized_cartan_apply, star_trivial] at h
  rw [← hij, ← hji]
  exact h

theorem symmetrizer_eq_of_cartan {τ : Tag} {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) :
    symmetrizer (isFiniteType_cartan τ) i = symmetrizer (isFiniteType_cartan τ) j := by
  have := symmetrizer_mul_cartan τ hij hji
  push_cast at this
  linarith

theorem exists_symmetrizer_eq (τ : Tag) :
    ∃ c : ℚ, 0 < c ∧ ∀ i, symmetrizer (isFiniteType_cartan τ) i = c * (τ.symmetrizer i i : ℚ) := by
  have hpos := symmetrizer_pos (isFiniteType_cartan τ)
  cases τ with
  | G2 =>
    have h01 := symmetrizer_mul_cartan .G2 (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩)
      (a := -1) (b := -3) rfl rfl
    refine ⟨_, hpos ⟨1, by decide⟩, fun i => ?_⟩
    push_cast at h01
    fin_cases i
    · change _ = _ * ((3 : ℤ) : ℚ)
      push_cast
      linarith
    · change _ = _ * ((1 : ℤ) : ℚ)
      push_cast
      ring
  | F4 =>
    have h01 := symmetrizer_eq_of_cartan (τ := .F4) (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩)
      rfl rfl
    have h12 := symmetrizer_mul_cartan .F4 (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩)
      (a := -1) (b := -2) rfl rfl
    have h23 := symmetrizer_eq_of_cartan (τ := .F4) (i := ⟨2, by decide⟩) (j := ⟨3, by decide⟩)
      rfl rfl
    refine ⟨_, hpos ⟨3, by decide⟩, fun i => ?_⟩
    push_cast at h12
    fin_cases i
    · change _ = _ * ((2 : ℤ) : ℚ)
      push_cast
      linarith
    · change _ = _ * ((2 : ℤ) : ℚ)
      push_cast
      linarith
    · change _ = _ * ((1 : ℤ) : ℚ)
      push_cast
      linarith
    · change _ = _ * ((1 : ℤ) : ℚ)
      push_cast
      linarith
  | D4 =>
    have h02 := symmetrizer_eq_of_cartan (τ := .D4) (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h12 := symmetrizer_eq_of_cartan (τ := .D4) (i := ⟨1, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h23 := symmetrizer_eq_of_cartan (τ := .D4) (i := ⟨2, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    refine ⟨_, hpos ⟨2, by decide⟩, fun i => ?_⟩
    fin_cases i <;> (change _ = _ * ((1 : ℤ) : ℚ); push_cast) <;> linarith
  | E6 =>
    have h02 := symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h13 := symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨1, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h23 := symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨2, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h34 := symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨3, by decide⟩)
      (j := ⟨4, by decide⟩) rfl rfl
    have h45 := symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨4, by decide⟩)
      (j := ⟨5, by decide⟩) rfl rfl
    refine ⟨_, hpos ⟨0, by decide⟩, fun i => ?_⟩
    fin_cases i <;> (change _ = _ * ((1 : ℤ) : ℚ); push_cast) <;> linarith
  | E7 =>
    have h02 := symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h13 := symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨1, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h23 := symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨2, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h34 := symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨3, by decide⟩)
      (j := ⟨4, by decide⟩) rfl rfl
    have h45 := symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨4, by decide⟩)
      (j := ⟨5, by decide⟩) rfl rfl
    have h56 := symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨5, by decide⟩)
      (j := ⟨6, by decide⟩) rfl rfl
    refine ⟨_, hpos ⟨0, by decide⟩, fun i => ?_⟩
    fin_cases i <;> (change _ = _ * ((1 : ℤ) : ℚ); push_cast) <;> linarith
  | E8 =>
    have h02 := symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h13 := symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨1, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h23 := symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨2, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h34 := symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨3, by decide⟩)
      (j := ⟨4, by decide⟩) rfl rfl
    have h45 := symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨4, by decide⟩)
      (j := ⟨5, by decide⟩) rfl rfl
    have h56 := symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨5, by decide⟩)
      (j := ⟨6, by decide⟩) rfl rfl
    have h67 := symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨6, by decide⟩)
      (j := ⟨7, by decide⟩) rfl rfl
    refine ⟨_, hpos ⟨0, by decide⟩, fun i => ?_⟩
    fin_cases i <;> (change _ = _ * ((1 : ℤ) : ℚ); push_cast) <;> linarith

theorem exists_formMatrix_eq_smul (τ : Tag) :
    ∃ c : ℝ, 0 < c ∧ formMatrix τ = c • τ.symmetrizedCartan.map (Int.cast : ℤ → ℝ) := by
  obtain ⟨c, hc, hd⟩ := exists_symmetrizer_eq τ
  refine ⟨c, Rat.cast_pos.2 hc, ?_⟩
  ext i j
  simp only [formMatrix_apply, hd, Matrix.smul_apply, Matrix.map_apply, symmetrizedCartan_apply,
    smul_eq_mul]
  push_cast
  ring

theorem posDef_symmetrizedCartan (τ : Tag) :
    (τ.symmetrizedCartan.map (Int.cast : ℤ → ℝ)).PosDef := by
  obtain ⟨c, hc, h⟩ := exists_formMatrix_eq_smul τ
  have := (posDef_formMatrix τ).smul (inv_pos.2 hc)
  rwa [h, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this

structure RootSpace (τ : Tag) where
  ofPi ::
  toPi : Fin τ.rank → ℝ

namespace RootSpace

variable {τ : Tag}

attribute [coe] toPi

instance instCoeFun : CoeFun (RootSpace τ) (fun _ => Fin τ.rank → ℝ) :=
  ⟨toPi⟩

@[ext] theorem ext {x y : RootSpace τ} (h : ∀ i, x i = y i) : x = y := by
  cases x
  cases y
  congr
  exact funext h

variable (τ) in
@[expose] def equivPi : RootSpace τ ≃ (Fin τ.rank → ℝ) :=
  ⟨toPi, ofPi, fun _ => rfl, fun _ => rfl⟩

instance instAddCommGroup : AddCommGroup (RootSpace τ) :=
  (equivPi τ).addCommGroup

@[simp] theorem toPi_zero : (0 : RootSpace τ).toPi = 0 :=
  rfl

@[simp] theorem toPi_add (x y : RootSpace τ) : (x + y).toPi = x.toPi + y.toPi :=
  rfl

@[simp] theorem toPi_neg (x : RootSpace τ) : (-x).toPi = -x.toPi :=
  rfl

@[simp] theorem toPi_sub (x y : RootSpace τ) : (x - y).toPi = x.toPi - y.toPi :=
  rfl

variable (τ) in
@[expose] def addEquivPi : RootSpace τ ≃+ (Fin τ.rank → ℝ) :=
  { equivPi τ with map_add' := fun _ _ => rfl }

instance instModule : Module ℝ (RootSpace τ) :=
  AddEquiv.module ℝ (addEquivPi τ)

@[simp] theorem toPi_smul (c : ℝ) (x : RootSpace τ) : (c • x).toPi = c • x.toPi :=
  rfl

@[simp] theorem toPi_ofPi (v : Fin τ.rank → ℝ) : (ofPi v : RootSpace τ).toPi = v :=
  rfl

@[simp] theorem ofPi_toPi (x : RootSpace τ) : ofPi x.toPi = x :=
  rfl

variable (τ) in
@[expose] def linearEquivPi : RootSpace τ ≃ₗ[ℝ] (Fin τ.rank → ℝ) where
  toFun := toPi
  invFun := ofPi
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem linearEquivPi_apply (x : RootSpace τ) : linearEquivPi τ x = x.toPi :=
  rfl

@[simp] theorem toPi_sum {ι : Type*} (s : Finset ι) (f : ι → RootSpace τ) :
    (∑ k ∈ s, f k).toPi = ∑ k ∈ s, (f k).toPi :=
  map_sum (linearEquivPi τ) f s

variable (τ) in
@[expose, instance_reducible] def core : InnerProductSpace.Core ℝ (RootSpace τ) where
  inner x y := x.toPi ⬝ᵥ (formMatrix τ *ᵥ y.toPi)
  conj_inner_symm x y := by
    simp only [conj_trivial]
    rw [dotProduct_mulVec, ← mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial,
      (posDef_formMatrix τ).isHermitian.eq, dotProduct_comm]
  re_inner_nonneg x := by
    simpa using (posDef_formMatrix τ).posSemidef.dotProduct_mulVec_nonneg x.toPi
  add_left x y z := add_dotProduct _ _ _
  smul_left x y r := smul_dotProduct r x.toPi _
  definite x hx := by
    by_contra h
    have h' : x.toPi ≠ 0 := fun h0 => h (by ext i; simp [h0])
    have := (posDef_formMatrix τ).dotProduct_mulVec_pos h'
    rw [star_trivial] at this
    exact this.ne' hx

instance instNormedAddCommGroup : NormedAddCommGroup (RootSpace τ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ (core τ)

instance instInnerProductSpace : InnerProductSpace ℝ (RootSpace τ) :=
  InnerProductSpace.ofCore (core τ).toCore

instance instFiniteDimensional : FiniteDimensional ℝ (RootSpace τ) :=
  (linearEquivPi τ).symm.finiteDimensional

theorem inner_def (x y : RootSpace τ) :
    inner ℝ x y = x.toPi ⬝ᵥ (formMatrix τ *ᵥ y.toPi) :=
  rfl

theorem exists_inner_eq_smul (τ : Tag) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : RootSpace τ,
      inner ℝ x y = c * ∑ i, ∑ j, x i * (τ.symmetrizedCartan i j : ℝ) * y j := by
  obtain ⟨c, hc, h⟩ := exists_formMatrix_eq_smul τ
  refine ⟨c, hc, fun x y => ?_⟩
  rw [inner_def, h]
  simp only [dotProduct, mulVec, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

@[coe, expose] def ofLattice (v : Fin τ.rank → ℤ) : RootSpace τ :=
  ofPi fun j => (v j : ℝ)

instance instCoeLattice : Coe (Fin τ.rank → ℤ) (RootSpace τ) :=
  ⟨ofLattice⟩

@[simp] theorem ofLattice_apply (v : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    ofLattice v j = (v j : ℝ) :=
  rfl

@[simp] theorem ofLattice_zero : ofLattice (0 : Fin τ.rank → ℤ) = 0 := by
  ext j
  simp

@[simp] theorem ofLattice_add (u v : Fin τ.rank → ℤ) :
    ofLattice (u + v) = ofLattice u + ofLattice v := by
  ext j
  simp

@[simp] theorem ofLattice_neg (v : Fin τ.rank → ℤ) : ofLattice (-v) = -ofLattice v := by
  ext j
  simp

@[simp] theorem ofLattice_sub (u v : Fin τ.rank → ℤ) :
    ofLattice (u - v) = ofLattice u - ofLattice v := by
  ext j
  simp

@[simp] theorem ofLattice_smul (n : ℤ) (v : Fin τ.rank → ℤ) :
    ofLattice (n • v) = (n : ℝ) • ofLattice v := by
  ext j
  simp

theorem ofLattice_injective :
    Function.Injective (ofLattice : (Fin τ.rank → ℤ) → RootSpace τ) :=
  fun _ _ h => funext fun j => Int.cast_injective (congrArg (fun x : RootSpace τ => x j) h)

@[expose] def ofLatticeHom : (Fin τ.rank → ℤ) →+ RootSpace τ where
  toFun := ofLattice
  map_zero' := ofLattice_zero
  map_add' := ofLattice_add

@[simp] theorem ofLatticeHom_apply (v : Fin τ.rank → ℤ) : ofLatticeHom v = ofLattice v :=
  rfl

theorem ofLattice_sum {ι : Type*} (s : Finset ι) (f : ι → Fin τ.rank → ℤ) :
    ofLattice (∑ k ∈ s, f k) = ∑ k ∈ s, ofLattice (f k) :=
  map_sum ofLatticeHom f s

theorem ofLattice_single_ne_zero (i : Fin τ.rank) :
    ofLattice (Pi.single i 1 : Fin τ.rank → ℤ) ≠ 0 := fun h => by
  simpa using congrArg (fun x : RootSpace τ => x i) h

theorem toPi_ofLattice_single (i : Fin τ.rank) :
    (ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)).toPi = Pi.single i 1 := by
  funext j
  simp only [ofLattice, toPi_ofPi, Pi.single_apply]
  split_ifs <;> simp

variable (τ) in
@[expose] def basis : Module.Basis (Fin τ.rank) ℝ (RootSpace τ) :=
  (Pi.basisFun ℝ (Fin τ.rank)).map (linearEquivPi τ).symm

theorem basis_apply (i : Fin τ.rank) : basis τ i = ofLattice (Pi.single i 1) := by
  rw [basis, Module.Basis.map_apply, Pi.basisFun_apply, ← toPi_ofLattice_single]
  rfl

theorem sum_smul_ofLattice_single (x : RootSpace τ) :
    ∑ i, x i • ofLattice (Pi.single i 1 : Fin τ.rank → ℤ) = x := by
  ext j
  simp [toPi_ofLattice_single, Pi.single_apply]

theorem ofLattice_eq_sum (v : Fin τ.rank → ℤ) :
    ofLattice v = ∑ j, (v j : ℝ) • ofLattice (Pi.single j 1 : Fin τ.rank → ℤ) :=
  (sum_smul_ofLattice_single (ofLattice v)).symm

theorem inner_ofLattice_single_left (i : Fin τ.rank) (y : RootSpace τ) :
    inner ℝ (ofLattice (Pi.single i 1)) y =
      (symmetrizer (isFiniteType_cartan τ) i : ℝ) * ∑ j, (τ.cartan i j : ℝ) * y j := by
  rw [inner_def, toPi_ofLattice_single, single_dotProduct, one_mul]
  simp [mulVec, dotProduct, formMatrix_apply, Finset.mul_sum, mul_assoc]

theorem inner_ofLattice (u v : Fin τ.rank → ℤ) :
    inner ℝ (ofLattice u) (ofLattice v) =
      (form (isFiniteType_cartan τ) (toRat u) (toRat v) : ℝ) := by
  have hu : (ofLattice u).toPi = Rat.castHom ℝ ∘ toRat u := by
    funext j
    simp [ofLattice]
  have hv : (ofLattice v).toPi = Rat.castHom ℝ ∘ toRat v := by
    funext j
    simp [ofLattice]
  rw [inner_def, form_apply, show ((toRat u ⬝ᵥ (symmetrized (isFiniteType_cartan τ) *ᵥ toRat v) :
    ℚ) : ℝ) = Rat.castHom ℝ (toRat u ⬝ᵥ (symmetrized (isFiniteType_cartan τ) *ᵥ toRat v)) from rfl,
    RingHom.map_dotProduct, hu, hv]
  congr 1
  funext i
  rw [Function.comp_apply, RingHom.map_mulVec]
  rfl

theorem inner_ofLattice_eq_sum (v : Fin τ.rank → ℤ) (x : RootSpace τ) :
    inner ℝ (ofLattice v) x = ∑ j, (v j : ℝ) * inner ℝ (ofLattice (Pi.single j 1)) x := by
  rw [ofLattice_eq_sum, sum_inner]
  simp only [real_inner_smul_left]

end RootSpace

open RootSpace

@[expose] def realExtend {τ : Tag} (f : Module.End ℤ (Fin τ.rank → ℤ)) :
    Module.End ℝ (RootSpace τ) where
  toFun x := ∑ k, x k • ofLattice (f (Pi.single k 1))
  map_add' x y := by simp only [toPi_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [toPi_smul, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

variable {τ : Tag}

theorem realExtend_apply (f : Module.End ℤ (Fin τ.rank → ℤ)) (x : RootSpace τ) :
    realExtend f x = ∑ k, x k • ofLattice (f (Pi.single k 1)) :=
  rfl

theorem realExtend_ofLattice (f : Module.End ℤ (Fin τ.rank → ℤ)) (v : Fin τ.rank → ℤ) :
    realExtend f (ofLattice v) = ofLattice (f v) := by
  conv_rhs => rw [← sum_smul_single v]
  rw [map_sum, ofLattice_sum, realExtend_apply]
  simp only [ofLattice_apply, map_zsmul, ofLattice_smul]

theorem realExtend_mul (f g : Module.End ℤ (Fin τ.rank → ℤ)) :
    realExtend (f * g) = realExtend f * realExtend g :=
  (basis τ).ext fun k => by
    rw [basis_apply, Module.End.mul_apply, realExtend_ofLattice, realExtend_ofLattice,
      realExtend_ofLattice, Module.End.mul_apply]

theorem realExtend_one : realExtend (1 : Module.End ℤ (Fin τ.rank → ℤ)) = 1 :=
  (basis τ).ext fun k => by
    rw [basis_apply, realExtend_ofLattice, Module.End.one_apply, Module.End.one_apply]

variable (τ) in
@[expose] def weylLinear : WeylGroup τ →* Module.End ℝ (RootSpace τ) where
  toFun w := realExtend (weylAction (isFiniteType_cartan τ) w)
  map_one' := by rw [map_one, realExtend_one]
  map_mul' w w' := by rw [map_mul, realExtend_mul]

theorem weylLinear_apply (w : WeylGroup τ) (x : RootSpace τ) :
    weylLinear τ w x = ∑ k, x k • ofLattice (w • (Pi.single k 1 : Fin τ.rank → ℤ)) :=
  rfl

theorem weylLinear_ofLattice (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    weylLinear τ w (ofLattice v) = ofLattice (w • v) :=
  realExtend_ofLattice _ v

theorem inner_weylLinear (w : WeylGroup τ) (x y : RootSpace τ) :
    inner ℝ (weylLinear τ w x) (weylLinear τ w y) = inner ℝ x y := by
  have h : (innerₗ (RootSpace τ)).compl₁₂ (weylLinear τ w) (weylLinear τ w) =
      innerₗ (RootSpace τ) := by
    refine LinearMap.BilinForm.ext_basis (basis τ) fun k l => ?_
    simp only [LinearMap.compl₁₂_apply, innerₗ_apply_apply, basis_apply, weylLinear_ofLattice,
      inner_ofLattice, smul_def, form_weylAction]
  have := congrArg (fun B : LinearMap.BilinForm ℝ (RootSpace τ) => B x y) h
  simpa only [LinearMap.compl₁₂_apply, innerₗ_apply_apply] using this

variable (τ) in
@[expose] def weylAct : WeylGroup τ →* (RootSpace τ ≃ₗᵢ[ℝ] RootSpace τ) where
  toFun w := LinearEquiv.isometryOfInner
    (LinearEquiv.ofLinearMap (weylLinear τ w) (weylLinear τ w⁻¹)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id]))
    (inner_weylLinear w)
  map_one' := LinearIsometryEquiv.ext fun x => by
    change weylLinear τ 1 x = x
    rw [map_one, Module.End.one_apply]
  map_mul' w w' := LinearIsometryEquiv.ext fun x => by
    change weylLinear τ (w * w') x = weylLinear τ w (weylLinear τ w' x)
    rw [map_mul, Module.End.mul_apply]

theorem weylAct_apply (w : WeylGroup τ) (x : RootSpace τ) : weylAct τ w x = weylLinear τ w x :=
  rfl

theorem weylAct_mul_apply (w w' : WeylGroup τ) (x : RootSpace τ) :
    weylAct τ (w * w') x = weylAct τ w (weylAct τ w' x) := by
  rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]

theorem weylAct_ofLattice (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    weylAct τ w (ofLattice v) = ofLattice (w • v) :=
  weylLinear_ofLattice w v

theorem reflect_single (i k : Fin τ.rank) :
    reflect τ i (Pi.single k 1) = Pi.single k 1 - τ.cartan i k • Pi.single i 1 := by
  simp [reflect, Pi.single_apply]

theorem weylAct_simple (i : Fin τ.rank) (x : RootSpace τ) :
    weylAct τ (simple τ i) x =
      x - (∑ j, (τ.cartan i j : ℝ) * x j) • ofLattice (Pi.single i 1) := by
  rw [weylAct_apply, weylLinear_apply]
  simp only [simple_smul, reflect_single, ofLattice_sub, ofLattice_smul, smul_sub, smul_smul,
    Finset.sum_sub_distrib, sum_smul_ofLattice_single, ← Finset.sum_smul, mul_comm (x _)]

theorem weylAct_simple_eq (i : Fin τ.rank) (x : RootSpace τ) :
    weylAct τ (simple τ i) x = x - (2 * inner ℝ (ofLattice (Pi.single i 1)) x /
      inner ℝ (ofLattice (Pi.single i 1)) (ofLattice (Pi.single i 1))) •
        ofLattice (Pi.single i 1) := by
  rw [weylAct_simple, inner_ofLattice_single_left, inner_ofLattice_single_left]
  have hd : (0 : ℝ) < symmetrizer (isFiniteType_cartan τ) i :=
    Rat.cast_pos.2 (symmetrizer_pos _ i)
  have h2 : ∑ j, (τ.cartan i j : ℝ) * ofLattice (Pi.single i 1 : Fin τ.rank → ℤ) j = 2 := by
    simp [Pi.single_apply, Tag.cartan_self]
  rw [h2]
  congr 2
  field_simp

theorem eq_zero_of_forall_weylAct_eq {v : RootSpace τ} (h : ∀ w, weylAct τ w v = v) : v = 0 := by
  have hi : ∀ i, inner ℝ (ofLattice (Pi.single i 1)) v = 0 := by
    intro i
    have hs := h (simple τ i)
    rw [weylAct_simple, sub_eq_self, smul_eq_zero] at hs
    rw [inner_ofLattice_single_left]
    rcases hs with hs | hs
    · rw [hs, mul_zero]
    · exact absurd hs (ofLattice_single_ne_zero i)
  have hvv : inner ℝ v v = 0 := calc
    inner ℝ v v = inner ℝ (∑ i, v i • ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)) v := by
      rw [sum_smul_ofLattice_single]
    _ = 0 := by
      rw [sum_inner]
      exact Finset.sum_eq_zero fun i _ => by rw [real_inner_smul_left, hi, mul_zero]
  exact inner_self_eq_zero.1 hvv

variable (τ) in
@[expose] def dominantCone : Set (RootSpace τ) :=
  {v | ∀ i, 0 ≤ inner ℝ (ofLattice (Pi.single i 1)) v}

variable (τ) in
@[expose] def openDominantCone : Set (RootSpace τ) :=
  {v | ∀ i, 0 < inner ℝ (ofLattice (Pi.single i 1)) v}

theorem mem_dominantCone {v : RootSpace τ} :
    v ∈ dominantCone τ ↔ ∀ i, 0 ≤ inner ℝ (ofLattice (Pi.single i 1)) v :=
  Iff.rfl

theorem mem_openDominantCone {v : RootSpace τ} :
    v ∈ openDominantCone τ ↔ ∀ i, 0 < inner ℝ (ofLattice (Pi.single i 1)) v :=
  Iff.rfl

theorem openDominantCone_subset_dominantCone : openDominantCone τ ⊆ dominantCone τ :=
  fun _ hv i => (hv i).le

variable (τ) in
@[expose] def heightVector : RootSpace τ :=
  ofPi ((formMatrix τ)⁻¹ *ᵥ 1)

theorem inner_heightVector (x : RootSpace τ) : inner ℝ x (heightVector τ) = ∑ i, x i := by
  have hdet : IsUnit (formMatrix τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (posDef_formMatrix τ).isUnit
  rw [inner_def, heightVector, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  exact dotProduct_one _

theorem inner_ofLattice_heightVector (v : Fin τ.rank → ℤ) :
    inner ℝ (ofLattice v) (heightVector τ) = (height v : ℝ) := by
  simp [inner_heightVector, height]

theorem heightVector_mem_openDominantCone : heightVector τ ∈ openDominantCone τ := fun i => by
  rw [inner_ofLattice_heightVector, height_single, Int.cast_one]
  exact one_pos

theorem exists_weylAct_mem_dominantCone (x : RootSpace τ) :
    ∃ w : WeylGroup τ, ∃ y ∈ dominantCone τ, x = weylAct τ w y := by
  obtain ⟨u, hu⟩ := Finite.exists_max fun u : WeylGroup τ =>
    inner ℝ (weylAct τ u x) (heightVector τ)
  refine ⟨u⁻¹, weylAct τ u x, fun i => ?_, ?_⟩
  · by_contra hneg
    rw [not_le, inner_ofLattice_single_left] at hneg
    have h := hu (simple τ i * u)
    rw [weylAct_mul_apply, weylAct_simple, inner_sub_left, real_inner_smul_left,
      inner_ofLattice_heightVector, height_single, Int.cast_one, mul_one, sub_le_self_iff] at h
    have hd : (0 : ℝ) < symmetrizer (isFiniteType_cartan τ) i :=
      Rat.cast_pos.2 (symmetrizer_pos _ i)
    nlinarith
  · rw [← weylAct_mul_apply, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]

theorem inner_ofLattice_nonneg {α : Fin τ.rank → ℤ} (hα : ∀ j, 0 ≤ α j) {v : RootSpace τ}
    (hv : v ∈ dominantCone τ) : 0 ≤ inner ℝ (ofLattice α) v := by
  rw [inner_ofLattice_eq_sum]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (by exact_mod_cast hα j) (hv j)

theorem inner_ofLattice_pos {α : Fin τ.rank → ℤ} (hα : ∀ j, 0 ≤ α j) (hne : α ≠ 0)
    {v : RootSpace τ} (hv : v ∈ openDominantCone τ) : 0 < inner ℝ (ofLattice α) v := by
  obtain ⟨k, hk⟩ : ∃ k, α k ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  rw [inner_ofLattice_eq_sum]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (by exact_mod_cast hα j) (hv j).le)
    ⟨k, Finset.mem_univ k,
      mul_pos (by exact_mod_cast lt_of_le_of_ne (hα k) (Ne.symm hk)) (hv k)⟩

theorem IsRoot.inner_nonneg_of_mem_dominantCone {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : 0 < height α) {v : RootSpace τ} (hv : v ∈ dominantCone τ) :
    0 ≤ inner ℝ (ofLattice α) v :=
  inner_ofLattice_nonneg ((IsRoot.height_pos_iff hα).1 hpos) hv

theorem IsRoot.inner_pos_of_mem_openDominantCone {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : 0 < height α) {v : RootSpace τ} (hv : v ∈ openDominantCone τ) :
    0 < inner ℝ (ofLattice α) v :=
  inner_ofLattice_pos ((IsRoot.height_pos_iff hα).1 hpos) hα.ne_zero hv

theorem IsRoot.inner_heightVector_pos {α : Fin τ.rank → ℤ} (hpos : 0 < height α) :
    0 < inner ℝ (ofLattice α) (heightVector τ) := by
  rw [inner_ofLattice_heightVector]
  exact_mod_cast hpos

theorem eq_one_of_weylAct_mem_openDominantCone {w : WeylGroup τ} {v : RootSpace τ}
    (hv : v ∈ openDominantCone τ) (hwv : weylAct τ w v ∈ openDominantCone τ) : w = 1 := by
  refine eq_one_of_forall_height_pos fun i => ?_
  rcases height_smul_single_pos_or_neg w i with h | h
  · exact h
  · exfalso
    have hroot := IsRoot.smul (isRoot_single τ i) w
    have hneg := IsRoot.inner_pos_of_mem_openDominantCone (IsRoot.neg hroot)
      (by rw [height_neg]; omega) hwv
    rw [ofLattice_neg, inner_neg_left, ← weylAct_ofLattice,
      LinearIsometryEquiv.inner_map_map] at hneg
    have := hv i
    linarith

theorem span_ofLattice_isRoot :
    Submodule.span ℝ (Set.range fun α : {v : Fin τ.rank → ℤ // IsRoot τ v} => ofLattice α.1) =
      ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← (basis τ).span_eq]
  exact Submodule.span_mono (Set.range_subset_iff.2 fun i =>
    ⟨⟨_, isRoot_single τ i⟩, (basis_apply i).symm⟩)

@[expose] def labelWeight : Label τ → RootSpace τ
  | .inl _ => 0
  | .inr α => ofLattice α.1

@[simp] theorem labelWeight_inl (i : Fin τ.rank) : labelWeight (.inl i : Label τ) = 0 :=
  rfl

@[simp] theorem labelWeight_inr (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    labelWeight (.inr α : Label τ) = ofLattice α.1 :=
  rfl

theorem weylAct_labelWeight_inr (w : WeylGroup τ) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    weylAct τ w (labelWeight (.inr α : Label τ)) = labelWeight (.inr (w • α) : Label τ) :=
  weylAct_ofLattice w α.1

end CFSG.LieType.Chevalley
