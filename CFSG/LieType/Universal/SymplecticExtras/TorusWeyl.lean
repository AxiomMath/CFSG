module

public import CFSG.LieType.Universal.SymplecticExtras.Matrices
import CFSG.LieType.Universal.SymplecticRoots.Weyl
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Weyl

public section

namespace CFSG.LieType.Universal.Symplectic.SpExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  TauCeti.GLSymplecticFin

variable {n : ℕ} {F : Type} [Field F]

theorem stdVec_apply_positiveLong (i j : Fin n) :
    stdVec (.positiveLong i : RootSubgroupIndex n) j = if j = i then 2 else 0 := by
  by_cases h : j = i <;> simp [stdVec, h]

theorem stdVec_apply_negativeLong (i j : Fin n) :
    stdVec (.negativeLong i : RootSubgroupIndex n) j = if j = i then -2 else 0 := by
  by_cases h : j = i <;> simp [stdVec, h]

theorem stdVec_apply_difference {i j : Fin n} (hij : i ≠ j) (b : Fin n) :
    stdVec (.difference i j hij : RootSubgroupIndex n) b =
      if b = i then 1 else if b = j then -1 else 0 := by
  by_cases hbi : b = i
  · subst hbi
    simp [stdVec, Ne.symm hij]
  · by_cases hbj : b = j
    · subst hbj
      simp [stdVec, hbi]
    · simp [stdVec, hbi, hbj]

theorem stdVec_apply_positiveSum {i j : Fin n} (hij : i < j) (b : Fin n) :
    stdVec (.positiveSum i j hij : RootSubgroupIndex n) b =
      if b = i then 1 else if b = j then 1 else 0 := by
  by_cases hbi : b = i
  · subst hbi
    simp [stdVec, hij.ne']
  · by_cases hbj : b = j
    · subst hbj
      simp [stdVec, hbi]
    · simp [stdVec, hbi, hbj]

theorem stdVec_apply_negativeSum {i j : Fin n} (hij : i < j) (b : Fin n) :
    stdVec (.negativeSum i j hij : RootSubgroupIndex n) b =
      if b = i then -1 else if b = j then -1 else 0 := by
  by_cases hbi : b = i
  · subst hbi
    simp [stdVec, hij.ne']
  · by_cases hbj : b = j
    · subst hbj
      simp [stdVec, hbi]
    · simp [stdVec, hbi, hbj]

@[expose] noncomputable def diagHom (n : ℕ) (F : Type) [Field F] :
    (Fin n → Fˣ) →* StatedSp n F :=
  (equivStatedSp n F).toMonoidHom.comp TauCeti.GLSymplecticFin.diagonal

theorem character_eq_prod (r : RootSubgroupIndex n) (t : Fin n → Fˣ) :
    RootSubgroupIndex.character r t = ∏ i, t i ^ stdVec r i := by
  cases r with
  | positiveLong i =>
    rw [RootSubgroupIndex.character_positiveLong,
      Finset.prod_eq_single_of_mem (s := Finset.univ) i (Finset.mem_univ i)]
    · rw [stdVec_apply_positiveLong i i, if_pos rfl]
      exact (zpow_two (t i)).symm
    · intro b _ hb
      rw [stdVec_apply_positiveLong i b, if_neg hb]
      simp
  | negativeLong i =>
    rw [RootSubgroupIndex.character_negativeLong,
      Finset.prod_eq_single_of_mem (s := Finset.univ) i (Finset.mem_univ i)]
    · rw [stdVec_apply_negativeLong i i, if_pos rfl,
        show (-2 : ℤ) = -(2 : ℤ) by norm_num, _root_.zpow_neg, zpow_two, _root_.mul_inv_rev]
    · intro b _ hb
      rw [stdVec_apply_negativeLong i b, if_neg hb]
      simp
  | difference i j hij =>
    rw [RootSubgroupIndex.character_difference,
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (s := Finset.univ) (Finset.mem_univ i),
      Finset.prod_eq_single_of_mem (s := Finset.univ \ {i}) j (by simp [hij.symm])]
    · rw [stdVec_apply_difference hij i, stdVec_apply_difference hij j]
      simp [hij.symm]
    · intro b hb hbj
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hb
      rw [stdVec_apply_difference hij b, if_neg hb.2, if_neg hbj]
      simp
  | positiveSum i j hij =>
    rw [RootSubgroupIndex.character_positiveSum,
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (s := Finset.univ) (Finset.mem_univ i),
      Finset.prod_eq_single_of_mem (s := Finset.univ \ {i}) j (by simp [hij.ne'])]
    · rw [stdVec_apply_positiveSum hij i, stdVec_apply_positiveSum hij j]
      simp [hij.ne']
    · intro b hb hbj
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hb
      rw [stdVec_apply_positiveSum hij b, if_neg hb.2, if_neg hbj]
      simp
  | negativeSum i j hij =>
    rw [RootSubgroupIndex.character_negativeSum,
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (s := Finset.univ) (Finset.mem_univ i),
      Finset.prod_eq_single_of_mem (s := Finset.univ \ {i}) j (by simp [hij.ne'])]
    · rw [stdVec_apply_negativeSum hij i, stdVec_apply_negativeSum hij j]
      simp [hij.ne', mul_comm]
    · intro b hb hbj
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hb
      rw [stdVec_apply_negativeSum hij b, if_neg hb.2, if_neg hbj]
      simp

theorem diagHom_conj_elt (t : Fin n → Fˣ) (r : RootSubgroupIndex n) (c : F) :
    diagHom n F t * elt r c * (diagHom n F t)⁻¹ =
      elt r (((∏ i, t i ^ stdVec r i : Fˣ) : F) * c) := by
  have h := TauCeti.GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv (R := F) r t
    (Multiplicative.ofAdd c)
  simp only [diagHom, elt, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← map_inv, ← map_mul, ← map_mul, ← character_eq_prod r t]
  simpa only [toAdd_ofAdd] using congrArg (equivStatedSp n F) h

@[expose] noncomputable def sw {i j : Fin n} (hij : i ≠ j) : StatedSp n F :=
  equivStatedSp n F (TauCeti.GLSymplecticFin.differenceShortRootWeylElement hij)

@[expose] noncomputable def lw (k : Fin n) : StatedSp n F :=
  equivStatedSp n F (TauCeti.GLSymplecticFin.positiveLongRootWeylElement k)

theorem sw_conj_diagHom {i j : Fin n} (hij : i ≠ j) (t : Fin n → Fˣ) :
    sw hij * diagHom n F t * (sw hij)⁻¹ = diagHom n F (t ∘ Equiv.swap i j) := by
  simp only [sw, diagHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← map_inv, ← map_mul, ← map_mul,
    TauCeti.GLSymplecticFin.differenceShortRootWeylElement_inv,
    TauCeti.GLSymplecticFin.differenceShortRootWeylElement_mul_diagonal_mul_inv]

theorem sw_inv_conj_diagHom {i j : Fin n} (hij : i ≠ j) (t : Fin n → Fˣ) :
    (sw hij)⁻¹ * diagHom n F t * sw hij = diagHom n F (t ∘ Equiv.swap i j) := by
  have h := sw_conj_diagHom hij (t ∘ Equiv.swap i j)
  rw [show (t ∘ Equiv.swap i j) ∘ Equiv.swap i j = t from funext fun a => by simp] at h
  calc (sw hij)⁻¹ * diagHom n F t * sw hij
      = (sw hij)⁻¹ * (sw hij * diagHom n F (t ∘ Equiv.swap i j) * (sw hij)⁻¹) * sw hij := by
        rw [h]
    _ = diagHom n F (t ∘ Equiv.swap i j) := by group

theorem lw_conj_diagHom (k : Fin n) (t : Fin n → Fˣ) :
    lw k * diagHom n F t * (lw k)⁻¹ = diagHom n F (Function.update t k (t k)⁻¹) := by
  simp only [lw, diagHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← map_inv, ← map_mul, ← map_mul,
    TauCeti.GLSymplecticFin.positiveLongRootWeylElement_inv,
    TauCeti.GLSymplecticFin.positiveLongRootWeylElement_mul_diagonal_mul_inv]

theorem lw_inv_conj_diagHom (k : Fin n) (t : Fin n → Fˣ) :
    (lw k)⁻¹ * diagHom n F t * lw k = diagHom n F (Function.update t k (t k)⁻¹) := by
  have h := lw_conj_diagHom k (Function.update t k (t k)⁻¹)
  rw [show Function.update (Function.update t k (t k)⁻¹) k
      ((Function.update t k (t k)⁻¹) k)⁻¹ = t from funext fun a => by
    by_cases ha : a = k <;> simp [Function.update, ha]] at h
  calc (lw k)⁻¹ * diagHom n F t * lw k
      = (lw k)⁻¹ * (lw k * diagHom n F (Function.update t k (t k)⁻¹) * (lw k)⁻¹) * lw k := by
        rw [h]
    _ = diagHom n F (Function.update t k (t k)⁻¹) := by group

theorem sw_eq {i j : Fin n} (hij : i ≠ j) : sw (F := F) hij =
    elt (F := F) (.difference i j hij) 1 * elt (F := F) (.difference j i hij.symm) (-1) *
      elt (F := F) (.difference i j hij) 1 := by
  have h : TauCeti.GLSymplecticFin.differenceShortRootWeylElement (R := F) hij =
      TauCeti.GLSymplecticFin.differenceShortRootUnit hij 1 *
        TauCeti.GLSymplecticFin.differenceShortRootUnit hij.symm (-1) *
        TauCeti.GLSymplecticFin.differenceShortRootUnit hij 1 := rfl
  simp only [sw, elt, h, RootSubgroupIndex.hom_difference,
    differenceShortRootHom_apply, toAdd_ofAdd, map_mul]

theorem sw_conj_elt_positiveLong {i j : Fin n} (hij : i ≠ j) (a : Fin n) (c : F) :
    sw hij * elt (.positiveLong a) c * (sw hij)⁻¹ =
      elt (.positiveLong (Equiv.swap i j a)) c := by
  simp only [sw, elt]
  rw [← map_inv, ← map_mul, ← map_mul]
  simpa only [RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
      toAdd_ofAdd] using
    congrArg (equivStatedSp n F) (shortWeyl_conj_positiveLong hij a c)

theorem lw_conj_elt_positiveLong_of_ne {k a : Fin n} (ha : a ≠ k) (c : F) :
    lw k * elt (.positiveLong a) c * (lw k)⁻¹ = elt (.positiveLong a) c := by
  simp only [lw, elt]
  rw [← map_inv, ← map_mul, ← map_mul]
  simpa only [RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
      toAdd_ofAdd] using
    congrArg (equivStatedSp n F) (longWeyl_conj_positiveLong_of_ne ha c)

end CFSG.LieType.Universal.Symplectic.SpExtras
