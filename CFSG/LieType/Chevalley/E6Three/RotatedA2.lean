module

public import CFSG.RankThree.PartOne.TCX.E.E6A2Sigma
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.LieType.Chevalley.E6Three.ModelKernel

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E6Three.RotatedA2

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.E6Three.ModelKernel
open CFSG.RankThree.PartOne.TCX.E (e6rhoA2₂ e6rhoA2₂_injective e6rhoA2₂_range
  e6rhoA2₂_transvection e6rhoA2₂_diagonal a2Std₂ chainRoot_eq_weight_sub)

open CFSG.RankThree.E6 (chain56 support56 chainRoot chainRoot_swap)

open scoped MatrixGroups Pointwise

section Cycle

variable {L : Type} [Field L]

@[expose] def cycleMat (p q r : L) : Matrix (Fin 3) (Fin 3) L := !![0, p, 0; 0, 0, q; r, 0, 0]

section Entries

variable (p q r : L)

@[simp] theorem cycleMat_00 : cycleMat p q r 0 0 = 0 := rfl
@[simp] theorem cycleMat_01 : cycleMat p q r 0 1 = p := rfl
@[simp] theorem cycleMat_02 : cycleMat p q r 0 2 = 0 := rfl
@[simp] theorem cycleMat_10 : cycleMat p q r 1 0 = 0 := rfl
@[simp] theorem cycleMat_11 : cycleMat p q r 1 1 = 0 := rfl
@[simp] theorem cycleMat_12 : cycleMat p q r 1 2 = q := rfl
@[simp] theorem cycleMat_20 : cycleMat p q r 2 0 = r := rfl
@[simp] theorem cycleMat_21 : cycleMat p q r 2 1 = 0 := rfl
@[simp] theorem cycleMat_22 : cycleMat p q r 2 2 = 0 := rfl

end Entries

theorem exists_aeval_of_commute_cycleMat {p q r : L} (hp : p ≠ 0) (hq : q ≠ 0)
    {X : Matrix (Fin 3) (Fin 3) L} (hX : Commute X (cycleMat p q r)) :
    ∃ f : Polynomial L, X = Polynomial.aeval (cycleMat p q r) f := by
  have e : ∀ i j, (X * cycleMat p q r) i j = (cycleMat p q r * X) i j := fun i j => by
    rw [hX.eq]
  have e00 : X 0 2 * r = p * X 1 0 := by
    have h := e 0 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three,
      cycleMat_00, cycleMat_01, cycleMat_02, cycleMat_10, cycleMat_20] at h
    linear_combination h
  have e01 : X 0 0 * p = p * X 1 1 := by
    have h := e 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three,
      cycleMat_00, cycleMat_01, cycleMat_02, cycleMat_11, cycleMat_21] at h
    linear_combination h
  have e02 : X 0 1 * q = p * X 1 2 := by
    have h := e 0 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three,
      cycleMat_00, cycleMat_01, cycleMat_02, cycleMat_12, cycleMat_22] at h
    linear_combination h
  have e12 : X 1 1 * q = q * X 2 2 := by
    have h := e 1 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three,
      cycleMat_02, cycleMat_10, cycleMat_11, cycleMat_12, cycleMat_22] at h
    linear_combination h
  have e21 : X 2 0 * p = r * X 0 1 := by
    have h := e 2 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three,
      cycleMat_01, cycleMat_11, cycleMat_20, cycleMat_21, cycleMat_22] at h
    linear_combination h
  have e22 : X 2 1 * q = r * X 0 2 := by
    have h := e 2 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three,
      cycleMat_02, cycleMat_12, cycleMat_20, cycleMat_21, cycleMat_22] at h
    linear_combination h
  have h11 : X 1 1 = X 0 0 :=
    mul_left_cancel₀ hp (by linear_combination -e01)
  have h22 : X 2 2 = X 0 0 :=
    (mul_left_cancel₀ hq (by linear_combination -e12)).trans h11
  have h10 : X 1 0 = X 0 2 * r / p := by
    rw [eq_div_iff hp]
    linear_combination -e00
  have h12 : X 1 2 = X 0 1 * q / p := by
    rw [eq_div_iff hp]
    linear_combination -e02
  have h20 : X 2 0 = X 0 1 * r / p := by
    rw [eq_div_iff hp]
    linear_combination e21
  have h21 : X 2 1 = X 0 2 * r / q := by
    rw [eq_div_iff hq]
    linear_combination e22
  refine ⟨Polynomial.C (X 0 0) + Polynomial.C (X 0 1 / p) * Polynomial.X +
    Polynomial.C (X 0 2 / (p * q)) * Polynomial.X ^ 2, ?_⟩
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, sq,
    Algebra.algebraMap_eq_smul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> (try field_simp)
  all_goals first
    | exact h11
    | exact h22
    | linear_combination -e00
    | linear_combination -e02
    | linear_combination e21
    | linear_combination e22

theorem commute_of_commute_cycleMat {p q r : L} (hp : p ≠ 0) (hq : q ≠ 0)
    {X Y : Matrix (Fin 3) (Fin 3) L} (hX : Commute X (cycleMat p q r))
    (hY : Commute Y (cycleMat p q r)) : Commute X Y := by
  obtain ⟨f, rfl⟩ := exists_aeval_of_commute_cycleMat hp hq hX
  obtain ⟨g, rfl⟩ := exists_aeval_of_commute_cycleMat hp hq hY
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, mul_comm]

end Cycle

section Conj

variable {L : Type} [Field L]

@[expose] def conjSLAut : GL (Fin 3) L →* MulAut SL(3, L) where
  toFun M :=
    { toFun := conjSLn M
      invFun := conjSLn M⁻¹
      left_inv := fun A => Subtype.ext (by
        simp only [coe_conjSLn, inv_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one])
      right_inv := fun A => Subtype.ext (by
        simp only [coe_conjSLn, inv_inv, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one])
      map_mul' := (conjSLn M).map_mul }
  map_one' := MulEquiv.ext fun A => Subtype.ext (by
    change ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * A *
      (↑(1 : GL (Fin 3) L)⁻¹ : Matrix (Fin 3) (Fin 3) L) = A
    simp)
  map_mul' M N := MulEquiv.ext fun A => Subtype.ext (by
    change ((M * N : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * A *
        (↑(M * N)⁻¹ : Matrix (Fin 3) (Fin 3) L) =
      (M : Matrix (Fin 3) (Fin 3) L) * ((N : Matrix (Fin 3) (Fin 3) L) * A *
        (↑N⁻¹ : Matrix (Fin 3) (Fin 3) L)) * (↑M⁻¹ : Matrix (Fin 3) (Fin 3) L)
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc])

theorem conjSLAut_apply (M : GL (Fin 3) L) (A : SL(3, L)) : conjSLAut M A = conjSLn M A :=
  rfl

theorem conjSLn_conjSLn_inv (M : GL (Fin 3) L) (A : SL(3, L)) :
    conjSLn M (conjSLn M⁻¹ A) = A :=
  (conjSLAut M).apply_symm_apply A

theorem exists_scalar_of_conjSLAut_eq_one {Z : GL (Fin 3) L} (h : conjSLAut Z = 1) :
    ∃ c : L, Matrix.scalar (Fin 3) c = (Z : Matrix (Fin 3) (Fin 3) L) := by
  have hsc : (Z : Matrix (Fin 3) (Fin 3) L) ∈ Set.range (Matrix.scalar (Fin 3)) := by
    refine Matrix.mem_range_scalar_of_commute_single fun i j hij => ?_
    have h1 := congrArg (fun φ : MulAut SL(3, L) =>
      ((φ (Matrix.SpecialLinearGroup.transvection hij 1) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L)) h
    simp only [MulAut.one_apply, conjSLAut_apply, coe_conjSLn,
      Matrix.SpecialLinearGroup.transvection_coe] at h1
    have h2 : (Z : Matrix (Fin 3) (Fin 3) L) * (1 + single i j 1) =
        (1 + single i j 1) * (Z : Matrix (Fin 3) (Fin 3) L) := by
      calc (Z : Matrix (Fin 3) (Fin 3) L) * (1 + single i j 1) =
            (Z : Matrix (Fin 3) (Fin 3) L) * (1 + single i j 1) *
              (↑Z⁻¹ : Matrix (Fin 3) (Fin 3) L) * (Z : Matrix (Fin 3) (Fin 3) L) := by
            rw [Matrix.mul_assoc _ (↑Z⁻¹ : Matrix (Fin 3) (Fin 3) L), Units.inv_mul,
              Matrix.mul_one]
        _ = (1 + single i j 1) * (Z : Matrix (Fin 3) (Fin 3) L) := by rw [h1]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h2
    exact (add_left_cancel h2).symm
  exact hsc

theorem mem_center_of_conjSLAut_eq_one {Z : GL (Fin 3) L} (h : conjSLAut Z = 1) :
    Z ∈ Subgroup.center (GL (Fin 3) L) := by
  obtain ⟨c, hc⟩ := exists_scalar_of_conjSLAut_eq_one h
  refine Subgroup.mem_center_iff.2 fun W => Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ← hc]
  exact (Matrix.scalar_commute c (fun _ => Commute.all _ _) (W : Matrix (Fin 3) (Fin 3) L)).eq.symm

@[expose] def cycCent (A : GL (Fin 3) L) : Subgroup (GL (Fin 3) L) where
  carrier := {X | A * X * A⁻¹ * X⁻¹ ∈ Subgroup.center (GL (Fin 3) L)}
  one_mem' := by
    change A * 1 * A⁻¹ * 1⁻¹ ∈ Subgroup.center (GL (Fin 3) L)
    simp only [mul_one, inv_one, mul_inv_cancel]
    exact one_mem _
  mul_mem' {X Y} hX hY := by
    change A * (X * Y) * A⁻¹ * (X * Y)⁻¹ ∈ Subgroup.center (GL (Fin 3) L)
    have hc := Subgroup.mem_center_iff.1 hY (A * X * A⁻¹)
    have e : A * (X * Y) * A⁻¹ * (X * Y)⁻¹ =
        (A * Y * A⁻¹ * Y⁻¹) * (A * X * A⁻¹ * X⁻¹) := by
      calc A * (X * Y) * A⁻¹ * (X * Y)⁻¹ =
            (A * X * A⁻¹) * (A * Y * A⁻¹ * Y⁻¹) * X⁻¹ := by group
        _ = (A * Y * A⁻¹ * Y⁻¹) * (A * X * A⁻¹) * X⁻¹ := by rw [hc]
        _ = (A * Y * A⁻¹ * Y⁻¹) * (A * X * A⁻¹ * X⁻¹) := by group
    rw [e]
    exact mul_mem hY hX
  inv_mem' {X} hX := by
    change A * X⁻¹ * A⁻¹ * X⁻¹⁻¹ ∈ Subgroup.center (GL (Fin 3) L)
    have hc := Subgroup.mem_center_iff.1 hX X
    have e : A * X⁻¹ * A⁻¹ * X⁻¹⁻¹ = (A * X * A⁻¹ * X⁻¹)⁻¹ := by
      calc A * X⁻¹ * A⁻¹ * X⁻¹⁻¹ = X⁻¹ * (X * (A * X⁻¹ * A⁻¹ * X)) := by group
        _ = X⁻¹ * ((A * X * A⁻¹ * X⁻¹)⁻¹ * X) := by group
        _ = X⁻¹ * (X * (A * X * A⁻¹ * X⁻¹)⁻¹) := by
          rw [(Subgroup.mem_center_iff.1 (inv_mem hX) X).symm]
        _ = (A * X * A⁻¹ * X⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hX

theorem isSolvable_cycCent {A : GL (Fin 3) L}
    (hA : ∀ X Y : Matrix (Fin 3) (Fin 3) L, Commute X A → Commute Y A → Commute X Y) :
    Group.IsSolvable (cycCent A) := by
  let g : cycCent A →* Subgroup.center (GL (Fin 3) L) :=
    { toFun := fun X => ⟨A * X * A⁻¹ * (X : GL (Fin 3) L)⁻¹, X.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun X Y => Subtype.ext (by
        have hc := Subgroup.mem_center_iff.1 Y.2 (A * X * A⁻¹)
        have hc' := Subgroup.mem_center_iff.1 X.2 (A * Y * A⁻¹ * (Y : GL (Fin 3) L)⁻¹)
        change A * ((X : GL (Fin 3) L) * Y) * A⁻¹ * ((X : GL (Fin 3) L) * Y)⁻¹ =
          (A * X * A⁻¹ * (X : GL (Fin 3) L)⁻¹) * (A * Y * A⁻¹ * (Y : GL (Fin 3) L)⁻¹)
        calc A * ((X : GL (Fin 3) L) * Y) * A⁻¹ * ((X : GL (Fin 3) L) * Y)⁻¹ =
              (A * X * A⁻¹) * (A * Y * A⁻¹ * (Y : GL (Fin 3) L)⁻¹) * (X : GL (Fin 3) L)⁻¹ := by
              group
          _ = (A * Y * A⁻¹ * (Y : GL (Fin 3) L)⁻¹) * (A * X * A⁻¹) * (X : GL (Fin 3) L)⁻¹ := by
              rw [hc]
          _ = (A * Y * A⁻¹ * (Y : GL (Fin 3) L)⁻¹) * (A * X * A⁻¹ * (X : GL (Fin 3) L)⁻¹) := by
              group
          _ = (A * X * A⁻¹ * (X : GL (Fin 3) L)⁻¹) * (A * Y * A⁻¹ * (Y : GL (Fin 3) L)⁻¹) :=
              hc') }
  have hcomm : ∀ x y : g.ker, x * y = y * x := by
    have hcA : ∀ X : g.ker, Commute ((X : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) A := by
      intro X
      have h1 : A * (X : GL (Fin 3) L) * A⁻¹ * ((X : GL (Fin 3) L))⁻¹ = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.1 X.2)
      have h2 : A * (X : GL (Fin 3) L) = (X : GL (Fin 3) L) * A := by
        calc A * (X : GL (Fin 3) L) =
              A * (X : GL (Fin 3) L) * A⁻¹ * ((X : GL (Fin 3) L))⁻¹ * ((X : GL (Fin 3) L) * A) := by
              group
          _ = (X : GL (Fin 3) L) * A := by rw [h1, one_mul]
      exact (congrArg Units.val h2).symm
    intro x y
    exact Subtype.ext (Subtype.ext (Units.ext (hA _ _ (hcA x) (hcA y)).eq))
  have : Group.IsSolvable g.ker := isSolvable_of_comm hcomm
  have : Group.IsSolvable (Subgroup.center (GL (Fin 3) L)) :=
    isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.1 y.2 x)
  exact solvable_of_ker_le_range g.ker.subtype g fun x hx => ⟨⟨x, hx⟩, rfl⟩

end Conj

section Frame

variable {L : Type} [Field L]

theorem isSLFrame_e6rhoA2₂ : IsSLFrame (e6rhoA2₂ L) (chainRoot chain56) where
  isRoot i j hij := ((a2Std₂.roots _).2 ⟨i, j, hij, rfl⟩).1
  neg i j := chainRoot_swap chain56 i j
  add i j k := by
    rw [chainRoot_eq_weight_sub, chainRoot_eq_weight_sub, chainRoot_eq_weight_sub]
    abel
  transv i j hij := e6rhoA2₂_transvection hij
  range := by
    rw [e6rhoA2₂_range, subsystemGroup_eq_rootSpan]
    congr 1
    ext α
    exact a2Std₂.roots α

variable (L) in
@[expose] noncomputable def frameEquiv : SL(3, L) ≃* (e6rhoA2₂ L).range :=
  MonoidHom.ofInjective e6rhoA2₂_injective

theorem frameEquiv_apply (X : SL(3, L)) :
    ((frameEquiv L X : (e6rhoA2₂ L).range) : ModGL .E6 L) = e6rhoA2₂ L X :=
  rfl

variable (L) in
@[expose] noncomputable def frameAut :
    Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)) →* MulAut SL(3, L) :=
  (MulAut.congr (frameEquiv L)).symm.toMonoidHom.comp
    (e6rhoA2₂ L).range.normalizerMonoidHom

theorem e6rhoA2₂_frameAut (g : Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)))
    (X : SL(3, L)) :
    e6rhoA2₂ L (frameAut L g X) = (g : ModGL .E6 L) * e6rhoA2₂ L X * (g : ModGL .E6 L)⁻¹ := by
  change e6rhoA2₂ L ((frameEquiv L).symm
    (((e6rhoA2₂ L).range.normalizerMonoidHom g) (frameEquiv L X))) = _
  rw [← frameEquiv_apply, MulEquiv.apply_symm_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    frameEquiv_apply]

theorem exists_frameAut_of_conj {g : ModGL .E6 L} {M : GL (Fin 3) L}
    (h : ∀ X : SL(3, L), g * e6rhoA2₂ L X * g⁻¹ = e6rhoA2₂ L (conjSLn M X)) :
    ∃ hg : g ∈ Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)),
      frameAut L ⟨g, hg⟩ = conjSLAut M := by
  have hg : g ∈ Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨conjSLn M X, (h X).symm⟩
    · rintro ⟨Y, hY⟩
      refine ⟨conjSLn M⁻¹ Y, ?_⟩
      have h1 := h (conjSLn M⁻¹ Y)
      rw [conjSLn_conjSLn_inv, hY] at h1
      exact mul_right_cancel (mul_left_cancel h1)
  exact ⟨hg, MulEquiv.ext fun X => e6rhoA2₂_injective (by rw [e6rhoA2₂_frameAut]; exact h X)⟩

theorem exists_frameAut_torus {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L) :
    ∃ ht' : t ∈ Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)),
      ∃ d : Fin 3 → Lˣ, frameAut L ⟨t, ht'⟩ = conjSLAut (diagGLn d) := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨hN, hM⟩ := exists_frameAut_of_conj (g := rootDiagUnit .E6 b)
    (M := diagGLn fun i => rootChar b (chainRoot chain56 i 0)) fun X => by
      rw [isSLFrame_e6rhoA2₂.torus 0 b X]
      rfl
  exact ⟨hN, _, hM⟩

theorem exists_frameAut_range (Y : SL(3, L)) :
    ∃ hY : e6rhoA2₂ L Y ∈ Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)),
      frameAut L ⟨e6rhoA2₂ L Y, hY⟩ = conjSLAut (Matrix.SpecialLinearGroup.toGL Y) :=
  exists_frameAut_of_conj fun X => by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1

theorem sup_le_frameGL : torusGroup .E6 L ⊔ (e6rhoA2₂ L).range ≤
    ((conjSLAut (L := L)).range.comap (frameAut L)).map
      (Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L))).subtype := by
  refine sup_le (fun t ht => ?_) ?_
  · obtain ⟨hN, d, hd⟩ := exists_frameAut_torus ht
    exact ⟨⟨t, hN⟩, ⟨diagGLn d, hd.symm⟩, rfl⟩
  · rintro _ ⟨Y, rfl⟩
    obtain ⟨hN, hY⟩ := exists_frameAut_range Y
    exact ⟨⟨_, hN⟩, ⟨_, hY.symm⟩, rfl⟩

theorem mem_torusGroup_of_frameAut_eq_one {g : ModGL .E6 L}
    (hg : g ∈ torusGroup .E6 L ⊔ (e6rhoA2₂ L).range)
    (hN : g ∈ Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)))
    (h1 : frameAut L ⟨g, hN⟩ = 1) : g ∈ torusGroup .E6 L := by
  have hTN : torusGroup .E6 L ≤ Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)) :=
    fun t ht => (exists_frameAut_torus ht).1
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup .E6 L)
    (e6rhoA2₂ L).range hTN
  have hg' : g ∈ ((torusGroup .E6 L : Set (ModGL .E6 L)) *
      ((e6rhoA2₂ L).range : Set (ModGL .E6 L))) := by
    rw [← hmul]
    exact hg
  obtain ⟨t, ht, s, ⟨Y, rfl⟩, rfl⟩ := Set.mem_mul.1 hg'
  obtain ⟨htN, d, hd⟩ := exists_frameAut_torus ht
  obtain ⟨hYN, hY⟩ := exists_frameAut_range Y
  have e : (⟨t * e6rhoA2₂ L Y, hN⟩ : Subgroup.normalizer ((e6rhoA2₂ L).range : Set _)) =
      ⟨t, htN⟩ * ⟨e6rhoA2₂ L Y, hYN⟩ := rfl
  rw [e, map_mul, hd, hY, ← map_mul] at h1
  obtain ⟨c, hc⟩ := exists_scalar_of_conjSLAut_eq_one h1
  have hdiag : ∀ i j : Fin 3, i ≠ j → (Y : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
    intro i j hij
    have h2 := congrFun (congrFun hc i) j
    rw [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h2
    simp only [diagGLn, Matrix.diagonal_mul, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ hij] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (d i).ne_zero
  have hρT := e6rhoA2₂_diagonal Y hdiag
  exact mul_mem ht hρT

end Frame

section Monomial

variable {L : Type} [Field L]

@[expose] def piThree : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

theorem positionWord_three_chainRoot : ∀ i j : Fin 3,
    CFSG.StandardType.TableBExc.wordAct .E6 (positionWord 3) (chainRoot chain56 i j) =
      chainRoot chain56 (piThree i) (piThree j) := by
  decide +kernel

theorem exists_frameAut_monomial {n : ModGL .E6 L} (hnN : n ∈ monomialSubgroup .E6 L)
    (hw : weylQuotientHom .E6 L ⟨n, hnN⟩ = (coxeterSystem .E6).wordProd (positionWord 3)) :
    ∃ p q r : L, p ≠ 0 ∧ q ≠ 0 ∧ ∃ A : GL (Fin 3) L,
      (A : Matrix (Fin 3) (Fin 3) L) = cycleMat p q r ∧
      ∃ hn : n ∈ Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)),
        frameAut L ⟨n, hn⟩ = conjSLAut A := by
  classical
  have hΨ : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      (MulAut.conj n).toMonoidHom (pinnedX .E6 L (chainRoot chain56 i j) c) =
        pinnedX .E6 L (chainRoot chain56 ((fun i j => (piThree i, piThree j)) i j).1
          ((fun i j => (piThree i, piThree j)) i j).2) ((b : L) * RingHom.id L c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnN ((isSLFrame_e6rhoA2₂ (L := L)).isRoot i j hij)
    refine ⟨μ, fun c => ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hμ, hw,
      CFSG.StandardType.TableBExc.wordProd_smul, positionWord_three_chainRoot]
    rfl
  obtain ⟨Φ', hΦ', b, hshape⟩ := (isSLFrame_e6rhoA2₂ (L := L)).exists_aut e6rhoA2₂_injective
    (RingHom.id L) ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩ (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective (fun i j => (piThree i, piThree j))
    (fun i j hij => piThree.injective.ne hij)
    (fun i j hij => ⟨piThree.symm i, piThree.symm j, piThree.symm.injective.ne hij, by simp⟩) hΨ
  obtain ⟨A, hA⟩ := exists_conj_map_of_root_permuting (le_refl 3) (RingHom.id L) piThree
    Φ'.toMonoidHom b fun i j hij t => hshape i j hij t
  have hΦA : ∀ X : SL(3, L), Φ' X = conjSLn A X := fun X => Subtype.ext (by
    rw [coe_conjSLn]
    have h := hA X
    simpa using h)
  set M : Matrix (Fin 3) (Fin 3) L := (A : Matrix (Fin 3) (Fin 3) L) with hMdef
  have hrel : ∀ (i j : Fin 3) (hij : i ≠ j), M * (1 + single i j 1) =
      (1 + single (piThree i) (piThree j) (b i j : L)) * M := by
    intro i j hij
    have h1 := hshape i j hij 1
    rw [hΦA, coe_conjSLn, Matrix.SpecialLinearGroup.transvection_coe] at h1
    simp only [RingHom.id_apply, mul_one] at h1
    calc M * (1 + single i j 1) =
          M * (1 + single i j 1) * (↑A⁻¹ : Matrix (Fin 3) (Fin 3) L) * M := by
          rw [Matrix.mul_assoc _ (↑A⁻¹ : Matrix (Fin 3) (Fin 3) L), hMdef, Units.inv_mul,
            Matrix.mul_one]
      _ = (1 + single (piThree i) (piThree j) (b i j : L)) * M := by rw [h1]
  have r01 := hrel 0 1 (by decide)
  have r10 := hrel 1 0 (by decide)
  have r20 := hrel 2 0 (by decide)
  have z00 := congrFun (congrFun r01 0) 1
  have z10 := congrFun (congrFun r01 1) 1
  have z11 := congrFun (congrFun r10 1) 0
  have z21 := congrFun (congrFun r10 2) 0
  have z02 := congrFun (congrFun r20 0) 0
  have z22 := congrFun (congrFun r20 2) 0
  simp [piThree, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply] at z00 z10 z11 z21 z02 z22
  have hAeq : M = cycleMat (M 0 1) (M 1 2) (M 2 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycleMat, z00, z10, z11, z21, z02, z22]
  have hdet : M 0 1 * M 1 2 * M 2 0 ≠ 0 := by
    have h := ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
    rw [← hMdef, hAeq, Matrix.det_fin_three] at h
    simpa [cycleMat] using h
  obtain ⟨hn, hnA⟩ := exists_frameAut_of_conj (g := n) (M := A) fun X => by
    rw [← hΦA]
    exact hΦ' X
  exact ⟨M 0 1, M 1 2, M 2 0, left_ne_zero_of_mul (left_ne_zero_of_mul hdet),
    right_ne_zero_of_mul (left_ne_zero_of_mul hdet), A, hAeq, hn, hnA⟩

theorem isSolvable_of_le_of_commute {n : ModGL .E6 L} (hnN : n ∈ monomialSubgroup .E6 L)
    (hw : weylQuotientHom .E6 L ⟨n, hnN⟩ = (coxeterSystem .E6).wordProd (positionWord 3))
    {H : Subgroup (ModGL .E6 L)} (hH : H ≤ torusGroup .E6 L ⊔ (e6rhoA2₂ L).range)
    (hHn : ∀ h ∈ H, h * n = n * h) : Group.IsSolvable H := by
  obtain ⟨p, q, r, hp, hq, A, hA, hn, hnA⟩ := exists_frameAut_monomial hnN hw
  have hK := sup_le_frameGL (L := L)
  have hHN : H ≤ Subgroup.normalizer ((e6rhoA2₂ L).range : Set (ModGL .E6 L)) := fun h hh => by
    obtain ⟨x, -, rfl⟩ := hK (hH hh)
    exact x.2
  let φ : H →* MulAut SL(3, L) := (frameAut L).comp (Subgroup.inclusion hHN)
  have hrange : φ.range ≤ ((conjSLAut (L := L)).comp (cycCent A).subtype).range := by
    rintro _ ⟨h, rfl⟩
    obtain ⟨x, ⟨X, hX⟩, hxh⟩ := hK (hH h.2)
    have hφ : frameAut L (Subgroup.inclusion hHN h) = conjSLAut X := by
      rw [hX]
      congr 1
      exact Subtype.ext hxh.symm
    have hc : frameAut L (Subgroup.inclusion hHN h) * frameAut L ⟨n, hn⟩ =
        frameAut L ⟨n, hn⟩ * frameAut L (Subgroup.inclusion hHN h) := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hHn h h.2)
    rw [hφ, hnA] at hc
    have hZ : conjSLAut (A * X * A⁻¹ * X⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group
    exact ⟨⟨X, mem_center_of_conjSLAut_eq_one hZ⟩, hφ.symm⟩
  have hker : ∀ h : H, φ h = 1 → (h : ModGL .E6 L) ∈ torusGroup .E6 L := fun h h1 =>
    mem_torusGroup_of_frameAut_eq_one (hH h.2) (hHN h.2) h1
  have : Group.IsSolvable (cycCent A) := isSolvable_cycCent fun X Y hX hY => by
    rw [hA] at hX hY
    exact commute_of_commute_cycleMat hp hq hX hY
  have : Group.IsSolvable ((conjSLAut (L := L)).comp (cycCent A).subtype).range :=
    solvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
  have : Group.IsSolvable φ.range :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hrange)
  have hcomm : ∀ x y : φ.ker, x * y = y * x := by
    intro x y
    have hxT := hker x.1 (MonoidHom.mem_ker.1 x.2)
    have hyT := hker y.1 (MonoidHom.mem_ker.1 y.2)
    obtain ⟨bx, hbx⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
    apply Subtype.ext
    apply Subtype.ext
    change (x : ModGL .E6 L) * (y : ModGL .E6 L) = (y : ModGL .E6 L) * (x : ModGL .E6 L)
    rw [hbx]
    exact rootDiagUnit_mul_comm_of_mem_torusGroup bx hyT
  have : Group.IsSolvable φ.ker := isSolvable_of_comm hcomm
  exact solvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict fun x hx =>
    ⟨⟨x, MonoidHom.mem_ker.2 (congrArg Subtype.val (MonoidHom.mem_ker.1 hx))⟩, rfl⟩

end Monomial

end CFSG.LieType.Chevalley.E6Three.RotatedA2
