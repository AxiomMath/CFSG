module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsInvol

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
open scoped MatrixGroups

section Fixed

variable {M : Type*} [Group M]

@[expose] def fixSub (β : MulAut M) : Subgroup M where
  carrier := {x | β x = x}
  mul_mem' {x y} hx hy := by
    change β (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := map_one β
  inv_mem' {x} hx := by
    change β x⁻¹ = x⁻¹
    rw [map_inv, hx]

theorem mem_fixSub {β : MulAut M} {x : M} : x ∈ fixSub β ↔ β x = x :=
  Iff.rfl

theorem fixSub_conj (a γ : MulAut M) :
    fixSub (a * γ * a⁻¹) = (fixSub γ).map a.toMonoidHom := by
  ext x
  rw [mem_fixSub, MulAut.mul_apply, MulAut.mul_apply]
  constructor
  · intro hx
    refine ⟨a⁻¹ x, ?_, by simp⟩
    change γ (a⁻¹ x) = a⁻¹ x
    apply a.injective
    rw [hx, MulAut.apply_inv_self]
  · rintro ⟨y, hy, rfl⟩
    change a (γ (a⁻¹ (a y))) = a y
    rw [MulAut.inv_apply_self, mem_fixSub.mp hy]

end Fixed

section Centralizer

variable {n : ℕ} {F : Type} [Field F] {G : Type*} [Group G] {K : Subgroup G}

theorem centralizer_eq_map_fixSub (ψ : SL(n, F) →* K) (hψ : Function.Surjective ψ) {t : G}
    {β : MulAut SL(n, F)} (hβ : ∀ x, t * (ψ x : G) * t⁻¹ = ψ (β x))
    (hfix : ∀ x z, z ∈ ψ.ker → β x = x * z → ∃ w ∈ ψ.ker, β (x * w) = x * w) :
    K ⊓ centralizer ({t} : Set G) = (fixSub β).map (K.subtype.comp ψ) := by
  apply le_antisymm
  · rintro k ⟨hkK, hkt⟩
    obtain ⟨x, hx⟩ := hψ ⟨k, hkK⟩
    have hk : (ψ x : G) = k := congrArg Subtype.val hx
    have h1 : ψ (β x) = ψ x := by
      apply Subtype.ext
      rw [← hβ, hk, mul_inv_eq_iff_eq_mul]
      exact (mem_centralizer_singleton_iff.mp hkt).symm
    have h2 : x⁻¹ * β x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    obtain ⟨w, hw, hxw⟩ := hfix x _ h2 (by rw [mul_inv_cancel_left])
    refine ⟨x * w, hxw, ?_⟩
    change (ψ (x * w) : G) = k
    rw [map_mul, (MonoidHom.mem_ker.mp hw), mul_one, hk]
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨(ψ x).2, mem_centralizer_singleton_iff.mpr ?_⟩
    change (ψ x : G) * t = t * ψ x
    have := hβ x
    rw [mem_fixSub.mp hx] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm

end Centralizer

section Scalars

variable {n : ℕ} {F : Type} [Field F]

theorem exists_scalar_of_mem_center {z : SL(n, F)} (hz : z ∈ center SL(n, F)) :
    ∃ c : Fˣ, c ^ n = 1 ∧ (z : Matrix (Fin n) (Fin n) F) = scalar (Fin n) (c : F) := by
  rw [← scalars_eq_center] at hz
  exact hz

theorem stdSL_conj_center (H : GL (Fin n) F) {z : SL(n, F)} (hz : z ∈ center SL(n, F)) :
    stdSL n F H 1 0 z = z := by
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_center hz
  rw [stdSL_one_zero]
  apply Subtype.ext
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, hc,
    (scalar_commute (c : F) (fun _ => Commute.all _ _) (H : Matrix (Fin n) (Fin n) F)).symm.eq,
    Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem coe_stdSL_one_field (σ : F ≃+* F) (x : SL(n, F)) :
    (stdSL n F 1 σ 0 x : Matrix (Fin n) (Fin n) F) = (x : Matrix (Fin n) (Fin n) F).map σ := by
  rw [stdSL, map_one, one_mul, pow_zero, mul_one]
  rfl

end Scalars

section Field

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

variable (n F) in
@[expose] noncomputable def binSL : SL(n, ZMod 2) →* SL(n, F) :=
  Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F)

theorem coe_binSL (y : SL(n, ZMod 2)) :
    (binSL n F y : Matrix (Fin n) (Fin n) F) =
      (y : Matrix (Fin n) (Fin n) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) F) :=
  rfl

theorem binSL_injective : Function.Injective (binSL n F) := by
  intro y y' h
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun (congrArg Subtype.val h) i) j
  exact (ZMod.castHom (dvd_refl 2) F).injective this

theorem sq_eq_self_of_charTwo_zmod : ∀ a : ZMod 2, a ^ 2 = a := by
  decide

theorem exists_zmod_eq_of_sq_eq_self {x : F} (hx : x ^ 2 = x) :
    ∃ a : ZMod 2, ZMod.castHom (dvd_refl 2) F a = x := by
  have h : x * (x - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hx, sub_self]
  rcases mul_eq_zero.mp h with h0 | h1
  · exact ⟨0, by rw [map_zero, h0]⟩
  · exact ⟨1, by rw [map_one, (sub_eq_zero.mp h1)]⟩

theorem fixSub_field_eq_range {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 2) :
    fixSub (stdSL n F 1 σ 0) = (binSL n F).range := by
  ext x
  rw [mem_fixSub]
  constructor
  · intro hx
    have hfix : ∀ i j, (x : Matrix (Fin n) (Fin n) F) i j ^ 2 =
        (x : Matrix (Fin n) (Fin n) F) i j := fun i j => by
      have := congrFun (congrFun (congrArg Subtype.val hx) i) j
      rw [coe_stdSL_one_field, Matrix.map_apply, hσ] at this
      exact this
    choose y hy using fun i j => exists_zmod_eq_of_sq_eq_self (hfix i j)
    have hmap : (Matrix.of y).map (ZMod.castHom (dvd_refl 2) F) = x := by
      ext i j
      exact hy i j
    have hdet : (Matrix.of y).det = 1 := by
      apply (ZMod.castHom (dvd_refl 2) F).injective
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, x.2, map_one]
    exact ⟨⟨Matrix.of y, hdet⟩, Subtype.ext hmap⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    rw [coe_stdSL_one_field, coe_binSL, Matrix.map_map]
    ext i j
    simp only [Matrix.map_apply, Function.comp_apply]
    rw [hσ, ← map_pow, sq_eq_self_of_charTwo_zmod]

omit [CharP F 2] in
theorem stdSL_field_center {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 2) {z : SL(n, F)}
    (hz : z ∈ center SL(n, F)) : stdSL n F 1 σ 0 z = z * z := by
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_center hz
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_stdSL_one_field, Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.map_apply,
    scalar_apply, diagonal_mul_diagonal, diagonal_apply, diagonal_apply, hσ]
  split_ifs <;> simp [sq]

omit [CharP F 2] in
theorem eq_one_of_mem_center_of_field (hn : 1 ≤ n) {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 2)
    {z : SL(n, F)} (hz : z ∈ center SL(n, F)) (hfix : stdSL n F 1 σ 0 z = z) : z = 1 := by
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_center hz
  have h1 := congrFun (congrFun (congrArg Subtype.val hfix) ⟨0, hn⟩) ⟨0, hn⟩
  rw [coe_stdSL_one_field, Matrix.map_apply, hc, scalar_apply, diagonal_apply_eq, hσ] at h1
  have hc1 : (c : F) = 1 := by
    have h2 : (c : F) * ((c : F) - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h c.ne_zero
    · exact sub_eq_zero.mp h
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [hc, hc1, Matrix.SpecialLinearGroup.coe_one, map_one]

variable {G : Type*} [Group G] {K : Subgroup G}

theorem exists_field_centralizer (hn : 1 ≤ n) (ψ : SL(n, F) →* K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center SL(n, F)) {t : G} {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 2) {H : GL (Fin n) F}
    (hH : ∀ x, t * (ψ x : G) * t⁻¹ =
      ψ ((stdSL n F H 1 0 * stdSL n F 1 σ 0 * (stdSL n F H 1 0)⁻¹) x)) :
    ∃ θ : SL(n, ZMod 2) →* G, Function.Injective θ ∧
      θ.range = K ⊓ centralizer ({t} : Set G) := by
  set c := stdSL n F H 1 0 with hcdef
  have hcz : ∀ z : SL(n, F), z ∈ center SL(n, F) → c⁻¹ z = z := fun z hz => by
    calc c⁻¹ z = c⁻¹ (c z) := by rw [stdSL_conj_center H hz]
      _ = z := MulAut.inv_apply_self _ c z
  have hβz : ∀ z : SL(n, F), z ∈ center SL(n, F) →
      (c * stdSL n F 1 σ 0 * c⁻¹) z = z * z := fun z hz => by
    rw [MulAut.mul_apply, MulAut.mul_apply, hcz z hz, stdSL_field_center hσ hz]
    exact stdSL_conj_center H (mul_mem hz hz)
  have hcent := centralizer_eq_map_fixSub ψ hψ hH fun x z hz hxz => ⟨z⁻¹, inv_mem hz, by
    rw [map_mul, hxz, map_inv, hβz z (hker hz)]
    have hzc := mem_center_iff.mp (hker hz)
    group⟩
  rw [fixSub_conj, fixSub_field_eq_range hσ] at hcent
  refine ⟨(K.subtype.comp ψ).comp (c.toMonoidHom.comp (binSL n F)), ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro y hy
    have hy' : c (binSL n F y) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext hy
    have hzc := hker hy'
    have hb : binSL n F y = c (binSL n F y) := by
      calc binSL n F y = c⁻¹ (c (binSL n F y)) := (MulAut.inv_apply_self _ c _).symm
        _ = c (binSL n F y) := hcz _ hzc
    have hbz : binSL n F y ∈ center SL(n, F) := hb ▸ hzc
    have hfix : stdSL n F 1 σ 0 (binSL n F y) = binSL n F y := by
      have : binSL n F y ∈ fixSub (stdSL n F 1 σ 0) := by
        rw [fixSub_field_eq_range hσ]
        exact ⟨y, rfl⟩
      exact this
    apply binSL_injective (n := n) (F := F)
    rw [eq_one_of_mem_center_of_field hn hσ hbz hfix, map_one]
  · rw [hcent, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.map_map]

end Field

section Unitary

variable {n : ℕ} {F : Type} [Field F]

theorem map_inv_mul_map (σ : F →+* F) (x : SL(n, F)) :
    ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F).map σ * (x : Matrix (Fin n) (Fin n) F).map σ =
      1 := by
  rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero σ) (map_one σ)]

theorem map_mul_map_inv (σ : F →+* F) (x : SL(n, F)) :
    (x : Matrix (Fin n) (Fin n) F).map σ * ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F).map σ =
      1 := by
  rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero σ) (map_one σ)]

theorem isUnitary_mul {σ : F →+* F} {J : Matrix (Fin n) (Fin n) F} {x y : SL(n, F)}
    (hx : ((x : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J * x = J)
    (hy : ((y : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J * y = J) :
    (((x * y : SL(n, F)) : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J * (x * y : SL(n, F)) = J := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul, transpose_mul]
  calc ((y : Matrix (Fin n) (Fin n) F).map σ)ᵀ * ((x : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J *
        ((x : Matrix (Fin n) (Fin n) F) * y) =
      ((y : Matrix (Fin n) (Fin n) F).map σ)ᵀ *
        (((x : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J * x) * y := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hx, hy]

theorem isUnitary_inv {σ : F →+* F} {J : Matrix (Fin n) (Fin n) F} {x : SL(n, F)}
    (hx : ((x : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J * x = J) :
    (((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J *
      ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) = J := by
  set M := (x : Matrix (Fin n) (Fin n) F)
  set M' := ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)
  have hMM' : M * M' = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc (M'.map σ)ᵀ * J * M' = (M'.map σ)ᵀ * ((M.map σ)ᵀ * J * M) * M' := by rw [hx]
    _ = (M.map σ * M'.map σ)ᵀ * J * (M * M') := by
        rw [transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = J := by
        rw [map_mul_map_inv, hMM', transpose_one, Matrix.one_mul, Matrix.mul_one]

@[expose] def slUnitary (σ : F →+* F) (J : Matrix (Fin n) (Fin n) F) : Subgroup SL(n, F) where
  carrier := {x | ((x : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J * x = J}
  mul_mem' hx hy := isUnitary_mul hx hy
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' hx := isUnitary_inv hx

theorem mem_slUnitary {σ : F →+* F} {J : Matrix (Fin n) (Fin n) F} {x : SL(n, F)} :
    x ∈ slUnitary σ J ↔ ((x : Matrix (Fin n) (Fin n) F).map σ)ᵀ * J * x = J :=
  Iff.rfl

theorem coe_stdSL_graphField (J₀ : GL (Fin n) F) (σ : F ≃+* F) (x : SL(n, F)) :
    (stdSL n F J₀ σ 1 x : Matrix (Fin n) (Fin n) F) =
      (J₀ : Matrix (Fin n) (Fin n) F) * (((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F).map σ)ᵀ *
        ((J₀⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [stdSL, pow_one, MulAut.mul_apply, MulAut.mul_apply,
    CatalogueBHigherLinearAction.slConjugation_matrix]
  rfl

theorem inv_eq_self_of_mul_self {J₀ : GL (Fin n) F}
    (hJ : (J₀ : Matrix (Fin n) (Fin n) F) * J₀ = 1) : J₀⁻¹ = J₀ :=
  inv_eq_of_mul_eq_one_right (Units.ext hJ)

theorem fixSub_stdSL_graphField {J₀ : GL (Fin n) F} (hJ : (J₀ : Matrix (Fin n) (Fin n) F) * J₀ = 1)
    (σ : F ≃+* F) : fixSub (stdSL n F J₀ σ 1) = slUnitary (σ : F →+* F) J₀ := by
  ext x
  rw [mem_fixSub, mem_slUnitary, RingEquiv.coe_toRingHom]
  set J := (J₀ : Matrix (Fin n) (Fin n) F)
  set M := (x : Matrix (Fin n) (Fin n) F)
  set M' := ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)
  have h1 : M'.map σ * M.map σ = 1 := map_inv_mul_map (σ : F →+* F) x
  have h2 : M.map σ * M'.map σ = 1 := map_mul_map_inv (σ : F →+* F) x
  have hcoe : (stdSL n F J₀ σ 1 x : Matrix (Fin n) (Fin n) F) = J * (M'.map σ)ᵀ * J := by
    rw [coe_stdSL_graphField, inv_eq_self_of_mul_self hJ]
  constructor
  · intro hx
    have hx' : J * (M'.map σ)ᵀ * J = M := by
      rw [← hcoe, hx]
    calc (M.map σ)ᵀ * J * M = (M.map σ)ᵀ * J * (J * (M'.map σ)ᵀ * J) := by rw [hx']
      _ = (M'.map σ * M.map σ)ᵀ * J := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc J J, hJ, Matrix.one_mul]
      _ = J := by rw [h1, transpose_one, Matrix.one_mul]
  · intro hx
    have key : J * (M'.map σ)ᵀ * J = M := by
      calc J * (M'.map σ)ᵀ * J = J * (M'.map σ)ᵀ * ((M.map σ)ᵀ * J * M) := by rw [hx]
        _ = J * (M.map σ * M'.map σ)ᵀ * J * M := by
            rw [transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = M := by rw [h2, transpose_one, Matrix.mul_one, hJ, Matrix.one_mul]
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [hcoe, key]

theorem coe_stdSL_conj (Q : GL (Fin n) F) (x : SL(n, F)) :
    (stdSL n F Q 1 0 x : Matrix (Fin n) (Fin n) F) =
      (Q : Matrix (Fin n) (Fin n) F) * x * ((Q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [stdSL_one_zero, CatalogueBHigherLinearAction.slConjugation_matrix]

theorem stdSL_graphField_eq_conj (σ : F ≃+* F) {Q J₀ : GL (Fin n) F}
    (hJ : (J₀ : Matrix (Fin n) (Fin n) F) * J₀ = 1)
    (hQ : ((Q : Matrix (Fin n) (Fin n) F).map σ)ᵀ * Q = J₀) :
    stdSL n F 1 σ 1 = stdSL n F Q 1 0 * stdSL n F J₀ σ 1 * (stdSL n F Q 1 0)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  set A := (Q : Matrix (Fin n) (Fin n) F)
  set A' := ((Q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set J := (J₀ : Matrix (Fin n) (Fin n) F)
  have hAA' : A * A' = 1 := Units.mul_inv Q
  have hA'A : A' * A = 1 := Units.inv_mul Q
  have hQ1 : (A.map σ)ᵀ = J * A' := by
    calc (A.map σ)ᵀ = (A.map σ)ᵀ * (A * A') := by rw [hAA', Matrix.mul_one]
      _ = J * A' := by rw [← Matrix.mul_assoc, hQ]
  have hQ2 : (A'.map σ)ᵀ = A * J := by
    have h3 : (A'.map σ)ᵀ * J = A := by
      calc (A'.map σ)ᵀ * J = (A'.map σ)ᵀ * ((A.map σ)ᵀ * A) := by rw [hQ]
        _ = (A.map σ * A'.map σ)ᵀ * A := by rw [transpose_mul, Matrix.mul_assoc]
        _ = A := by
            rw [← Matrix.map_mul, hAA', Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one,
              Matrix.one_mul]
    calc (A'.map σ)ᵀ = (A'.map σ)ᵀ * (J * J) := by rw [hJ, Matrix.mul_one]
      _ = A * J := by rw [← Matrix.mul_assoc, h3]
  refine MulEquiv.ext fun x => Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, coe_stdSL_graphField, coe_stdSL_conj,
    coe_stdSL_graphField, ← map_inv, coe_stdSL_conj, inv_eq_self_of_mul_self hJ, inv_one,
    Units.val_one, Matrix.one_mul, Matrix.mul_one, Matrix.map_mul, Matrix.map_mul,
    transpose_mul, transpose_mul, hQ1, hQ2]
  simp only [Matrix.mul_assoc]
  rfl

theorem stdSL_mul_one_zero (H Q : GL (Fin n) F) :
    stdSL n F (H * Q) 1 0 = stdSL n F H 1 0 * stdSL n F Q 1 0 := by
  rw [stdSL_one_zero, stdSL_one_zero, stdSL_one_zero, map_mul]

theorem conj_graphField_eq (σ : F ≃+* F) (H : GL (Fin n) F) {Q J₀ : GL (Fin n) F}
    (hJ : (J₀ : Matrix (Fin n) (Fin n) F) * J₀ = 1)
    (hQ : ((Q : Matrix (Fin n) (Fin n) F).map σ)ᵀ * Q = J₀) :
    stdSL n F H 1 0 * stdSL n F 1 σ 1 * (stdSL n F H 1 0)⁻¹ =
      stdSL n F (H * Q) 1 0 * stdSL n F J₀ σ 1 * (stdSL n F (H * Q) 1 0)⁻¹ := by
  rw [stdSL_graphField_eq_conj σ hJ hQ, stdSL_mul_one_zero]
  group

theorem eq_one_of_graphField_eq_mul (hF : Nat.card F = 4) {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 2) (hn : 1 ≤ n) {J₀ : GL (Fin n) F}
    (hJ : (J₀ : Matrix (Fin n) (Fin n) F) * J₀ = 1)
    (hJt : (J₀ : Matrix (Fin n) (Fin n) F)ᵀ = J₀) (hJσ : (J₀ : Matrix (Fin n) (Fin n) F).map σ = J₀)
    {y z : SL(n, F)} (hz : z ∈ center SL(n, F)) (hyz : stdSL n F J₀ σ 1 y = y * z) : z = 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have := Fintype.ofFinite F
  have h4 : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ, ← pow_mul, show 2 * 2 = Fintype.card F by rw [h4], FiniteField.pow_card]
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_center hz
  set J := (J₀ : Matrix (Fin n) (Fin n) F)
  set M := (y : Matrix (Fin n) (Fin n) F)
  set M' := ((y⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)
  have h1 : M'.map σ * M.map σ = 1 := map_inv_mul_map (σ : F →+* F) y
  have hcoe : J * (M'.map σ)ᵀ * J = (c : F) • M := by
    have := congrArg (fun x : SL(n, F) => (x : Matrix (Fin n) (Fin n) F)) hyz
    rw [coe_stdSL_graphField, inv_eq_self_of_mul_self hJ, Matrix.SpecialLinearGroup.coe_mul,
      hc, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one] at this
    exact this
  set N := (M.map σ)ᵀ * J * M with hN
  have hcN : (c : F) • N = J := by
    calc (c : F) • N = (M.map σ)ᵀ * J * ((c : F) • M) := by rw [hN, Matrix.mul_smul]
      _ = (M.map σ)ᵀ * J * (J * (M'.map σ)ᵀ * J) := by rw [hcoe]
      _ = (M'.map σ * M.map σ)ᵀ * J := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc J J, hJ, Matrix.one_mul]
      _ = J := by rw [h1, transpose_one, Matrix.one_mul]
  have hMσσ : (M.map σ).map σ = M := by
    rw [Matrix.map_map]
    ext i j
    exact hσσ _
  have hNσ : (N.map σ)ᵀ = N := by
    rw [hN, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hMσσ, hJσ, transpose_mul,
      transpose_mul, transpose_transpose, hJt, Matrix.mul_assoc]
  have hσc : σ (c : F) • N = J := by
    have := congrArg (fun A => (A.map σ)ᵀ) hcN
    rwa [Matrix.map_smul' (f := σ) (c : F) N (map_mul σ), Matrix.transpose_smul, hNσ,
      hJσ, hJt] at this
  have hsub : (σ (c : F) - c) • J = 0 := by
    have : (σ (c : F) - c) • N = 0 := by rw [sub_smul, hσc, hcN, sub_self]
    have hNJ : N = (c : F)⁻¹ • J := by
      rw [← hcN, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]
    rw [hNJ, smul_smul] at this
    have h2 : ((σ (c : F) - c) * (c : F)⁻¹) • J = 0 := this
    have h3 := congrArg (· * J) h2
    simp only [Matrix.smul_mul, hJ, Matrix.zero_mul] at h3
    have h4 := congrFun (congrFun h3 ⟨0, hn⟩) ⟨0, hn⟩
    simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h4
    rw [mul_eq_zero] at h4
    rcases h4 with h4 | h4
    · rw [h4, zero_smul]
    · exact absurd (inv_eq_zero.mp h4) c.ne_zero
  have hσc' : σ (c : F) = c := by
    have h3 := congrArg (· * J) hsub
    simp only [Matrix.smul_mul, hJ, Matrix.zero_mul] at h3
    have h4 := congrFun (congrFun h3 ⟨0, hn⟩) ⟨0, hn⟩
    simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h4
    exact sub_eq_zero.mp h4
  have hc1 : (c : F) = 1 := by
    rw [hσ] at hσc'
    have h2 : (c : F) * ((c : F) - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hσc', sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h c.ne_zero
    · exact sub_eq_zero.mp h
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [hc, hc1, Matrix.SpecialLinearGroup.coe_one, map_one]

variable {G : Type*} [Group G] {K : Subgroup G}

theorem commutator_map_eq_of_perfect {A B : Type*} [Group A] [Group B] (f : A →* B)
    {S : Subgroup A} (hS : ⁅S, S⁆ = S) : ⁅S.map f, S.map f⁆ = S.map f := by
  rw [← Subgroup.map_commutator, hS]

end Unitary

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
