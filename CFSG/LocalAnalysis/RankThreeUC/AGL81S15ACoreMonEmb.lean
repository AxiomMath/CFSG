module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreDefs
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open Matrix Equiv CFSG.SectionRank.OddCover CFSG.Quasithin

variable {F : Type} [Field F]

@[expose] noncomputable def monPermGL (m : ℕ) : Perm (Fin m) →* GL (Fin m) F :=
  (Matrix.permMatrixHom (n := Fin m) (R := F)).toHomUnits

theorem coe_monPermGL {m : ℕ} (σ : Perm (Fin m)) :
    ((monPermGL m σ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = σ⁻¹.permMatrix F :=
  rfl

theorem permMatrix_apply_eq_ite {m : ℕ} (σ : Perm (Fin m)) (i j : Fin m) :
    σ.permMatrix F i j = if σ i = j then 1 else 0 := by
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem monPermGL_conj_diagHom {m : ℕ} (σ : Perm (Fin m)) (d : Fin m → Fˣ) :
    monPermGL m σ * diagHom m d * (monPermGL m σ)⁻¹ = diagHom m (d ∘ σ.symm) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, coe_monPermGL, coe_monPermGL, inv_inv, coe_diagHom,
    coe_diagHom]
  have h1 : (σ⁻¹.permMatrix F) * diagonal (fun i => (d i : F)) =
      (diagonal fun i => (d i : F)).submatrix (σ⁻¹ : Perm (Fin m)) id :=
    PEquiv.toMatrix_toPEquiv_mul _ _
  have h2 : ((diagonal fun i => (d i : F)).submatrix (σ⁻¹ : Perm (Fin m)) id) * σ.permMatrix F =
      ((diagonal fun i => (d i : F)).submatrix (σ⁻¹ : Perm (Fin m)) id).submatrix id σ.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ _
  rw [h1, h2]
  ext k l
  simp only [submatrix_apply, id_eq, diagonal_apply, Function.comp_apply]
  by_cases hkl : k = l
  · subst hkl
    simp [Equiv.Perm.inv_def]
  · have : σ⁻¹ k ≠ σ.symm l := fun h' =>
      hkl (σ.symm.injective (by rw [← Equiv.Perm.inv_def]; exact h'))
    simp [hkl]

variable {C : Type} [CommGroup C]

@[expose] noncomputable def monEmb {C : Type} [CommGroup C] {F : Type} [Field F] (e : C →* Fˣ)
    (m : ℕ) : Mon C m →* GL (Fin m) F :=
  SemidirectProduct.lift ((diagHom m).comp (MonoidHom.compLeft e (Fin m))) (monPermGL m)
    fun σ => MonoidHom.ext fun t => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [monPermGL_conj_diagHom]
      rfl

theorem monEmb_apply (e : C →* Fˣ) {m : ℕ} (x : Mon C m) :
    monEmb (F := F) e m x = diagHom m (fun i => e (x.left i)) * monPermGL m x.right :=
  rfl

theorem monEmb_monT {C : Type} [CommGroup C] {F : Type} [Field F] (e : C →* Fˣ) {m : ℕ}
    (t : Fin m → C) : monEmb (F := F) e m (monT t) = diagHom m (fun i => e (t i)) := by
  rw [monEmb_apply]
  simp [monT]

theorem monEmb_monS (e : C →* Fˣ) {m : ℕ} (σ : Perm (Fin m)) :
    monEmb (F := F) e m (monS σ) = monPermGL m σ := by
  have h : (fun i => e ((monS (C := C) σ).left i)) = 1 := funext fun i => by simp [monS]
  rw [monEmb_apply, h, map_one, one_mul]
  rfl

theorem monEmb_monScalar {C : Type} [CommGroup C] {F : Type} [Field F] (e : C →* Fˣ) {m : ℕ}
    (z : C) : monEmb (F := F) e m (monScalar C m z) =
      Matrix.GeneralLinearGroup.scalar (Fin m) (e z) := by
  rw [monScalar_apply, monEmb_monT]
  apply Units.ext
  rw [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem coe_monEmb_apply (e : C →* Fˣ) {m : ℕ} (x : Mon C m) (i j : Fin m) :
    ((monEmb (F := F) e m x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j =
      if x.right⁻¹ i = j then (e (x.left i) : F) else 0 := by
  rw [monEmb_apply, Units.val_mul, coe_diagHom, coe_monPermGL, diagonal_mul,
    permMatrix_apply_eq_ite]
  split_ifs <;> simp

theorem monEmb_injective {C : Type} [CommGroup C] {F : Type} [Field F] {e : C →* Fˣ}
    (he : Function.Injective e) (m : ℕ) : Function.Injective (monEmb (F := F) e m) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hent : ∀ i j, (if x.right⁻¹ i = j then (e (x.left i) : F) else 0) =
      if i = j then 1 else 0 := fun i j => by
    rw [← coe_monEmb_apply, hx, Units.val_one, Matrix.one_apply]
  have hσ : ∀ i, x.right⁻¹ i = i := fun i => by
    have h := hent i (x.right⁻¹ i)
    rw [if_pos rfl] at h
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h
    exact (e (x.left i)).ne_zero h
  have hr : x.right = 1 := inv_eq_one.mp (Equiv.ext hσ)
  refine SemidirectProduct.ext (funext fun i => he ?_) hr
  have h := hent i i
  rw [if_pos (hσ i), if_pos rfl] at h
  rw [SemidirectProduct.one_left, Pi.one_apply, map_one]
  exact Units.ext h

theorem det_coe_monEmb (e : C →* Fˣ) {m : ℕ} (x : Mon C m) :
    ((monEmb (F := F) e m x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det =
      (e (monDet x) : F) * ((Perm.sign (monPerm x) : ℤ) : F) := by
  have hdet : monDet x = ∏ i, x.left i := by
    conv_lhs => rw [mon_eq_monT_mul_monS x]
    rw [map_mul, monDet_monT, monDet_monS, mul_one]
  rw [monEmb_apply, Units.val_mul, det_mul, det_diagHom, coe_monPermGL, det_permutation,
    Perm.sign_inv, hdet, map_prod, Units.coe_prod]
  rfl

theorem sign_eq_one_of_odd_orderOf {m : ℕ} {σ : Perm (Fin m)} (h : Odd (orderOf σ)) :
    Perm.sign σ = 1 := by
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
  · exact hs
  · have h1 : Perm.sign σ ^ orderOf σ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [hs, h.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem monEmb_det_of_odd {C : Type} [CommGroup C] {F : Type} [Field F] (e : C →* Fˣ) {m : ℕ}
    (x : Mon C m) (hx : Odd (orderOf x)) :
    Matrix.GeneralLinearGroup.det (monEmb (F := F) e m x) = e (monDet x) := by
  have hs : Perm.sign (monPerm x) = 1 :=
    sign_eq_one_of_odd_orderOf (Odd.of_dvd_nat hx (orderOf_map_dvd monPerm x))
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_coe_monEmb, hs]
  simp

theorem diagHom_mem_statedGU {q m : ℕ} (hq : q ≠ 0) {d : Fin m → Fˣ}
    (hd : ∀ i, (d i : F) ^ (q + 1) = 1) : diagHom m d ∈ StatedGU m q F := by
  apply Subgroup.subset_closure
  change (((diagHom m d : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map (· ^ q))ᵀ *
    ((diagHom m d : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1
  rw [coe_diagHom, Matrix.diagonal_map (by simp [zero_pow hq]), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← pow_succ, hd i]

theorem monPermGL_mem_statedGU {q m : ℕ} (hq : q ≠ 0) (σ : Perm (Fin m)) :
    monPermGL m σ ∈ StatedGU m q F := by
  apply Subgroup.subset_closure
  change (((monPermGL m σ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).map (· ^ q))ᵀ *
    ((monPermGL m σ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1
  have hmap : (σ⁻¹.permMatrix F).map (· ^ q) = σ⁻¹.permMatrix F := by
    ext i j
    rw [Matrix.map_apply, permMatrix_apply_eq_ite]
    split_ifs <;> simp [zero_pow hq]
  rw [coe_monPermGL, hmap, transpose_permMatrix, ← permMatrix_mul, inv_inv, inv_mul_cancel,
    permMatrix_one]

theorem monEmb_mem_statedGU {C : Type} [CommGroup C] {F : Type} [Field F] (e : C →* Fˣ)
    {q m : ℕ} (hq : q ≠ 0) (heU : ∀ z : C, ((e z : Fˣ) : F) ^ (q + 1) = 1) (x : Mon C m) :
    monEmb (F := F) e m x ∈ StatedGU m q F := by
  rw [monEmb_apply]
  exact mul_mem (diagHom_mem_statedGU hq fun i => heU _) (monPermGL_mem_statedGU hq _)

theorem card_mon {m : ℕ} : Nat.card (Mon C m) = Nat.card C ^ m * m.factorial := by
  rw [SemidirectProduct.card, Nat.card_fun, Nat.card_perm, Nat.card_fin]

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
