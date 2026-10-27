module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LieType.Universal.SpecialLinearRoots.SignedPerm
public import Mathlib.FieldTheory.Finite.Basic

public section

open Matrix
open scoped commutatorElement

namespace CFSG.LinearAlgebra.SLThreeRootGeneration

variable {K : Type*} [Field K]

theorem closure_transvections_eq_top {n : ℕ}
    (H : Subgroup (SpecialLinearGroup (Fin n) K))
    (hT : ∀ (i j : Fin n) (hij : i ≠ j) (t : K),
      SpecialLinearGroup.transvection hij t ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  rw [← CFSG.LinearGroups.special_linear_elementary_generation (n := n) (K := K)]
  refine (Subgroup.closure_le (K := H)).2 ?_
  rintro A ⟨i, j, hij, t, rfl⟩
  exact hT i j hij t

private lemma mul_mem_closure_range_pow {r : K} {x y : K}
    (hx : x ∈ AddSubgroup.closure (Set.range fun k : ℕ => r ^ k))
    (hy : y ∈ AddSubgroup.closure (Set.range fun k : ℕ => r ^ k)) :
    x * y ∈ AddSubgroup.closure (Set.range fun k : ℕ => r ^ k) := by
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨l, rfl⟩ := hy
      rw [← pow_add]
      exact AddSubgroup.subset_closure ⟨k + l, rfl⟩
  | zero_left x hx => simpa using hx
  | zero_right x hx => simpa using hx
  | add_left x y z hx hy hz ihx ihy =>
      simpa [add_mul] using AddSubgroup.add_mem _ ihx ihy
  | add_right x y z hx hy hz ihx ihy =>
      simpa [mul_add] using AddSubgroup.add_mem _ ihx ihy
  | neg_left x y hx hy ih =>
      simpa [neg_mul] using AddSubgroup.neg_mem _ ih
  | neg_right x y hx hy ih =>
      simpa [mul_neg] using AddSubgroup.neg_mem _ ih

theorem addSubgroup_closure_pow_eq_top [Fintype K] {r : K}
    (hr : Subfield.closure ({r} : Set K) = ⊤) :
    AddSubgroup.closure (Set.range fun k : ℕ => r ^ k) = ⊤ := by
  let A : AddSubgroup K := AddSubgroup.closure (Set.range fun k : ℕ => r ^ k)
  have hA_mul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A := fun x hx y hy =>
    mul_mem_closure_range_pow hx hy
  have hA_one : (1 : K) ∈ A := by
    simpa using AddSubgroup.subset_closure
      (Set.mem_range_self (f := fun k : ℕ => r ^ k) 0)
  have hpow : ∀ (m : ℕ) {x : K}, x ∈ A → x ^ m ∈ A := by
    intro m
    induction m with
    | zero => intro x _; simpa using hA_one
    | succ m ih => intro x hx; rw [pow_succ]; exact hA_mul (x ^ m) (ih hx) x hx
  have hA_inv : ∀ x ∈ A, x⁻¹ ∈ A := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hq : x ^ (Fintype.card K - 1) = 1 :=
        FiniteField.pow_card_sub_one_eq_one x hx0
      have hcard : 1 < Fintype.card K := Fintype.one_lt_card
      have hxinv : x⁻¹ = x ^ (Fintype.card K - 2) := by
        rw [eq_comm]
        apply eq_inv_of_mul_eq_one_right
        rw [← hq, mul_comm, ← pow_succ]
        congr 1
        omega
      rw [hxinv]
      exact hpow _ hx
  let F : Subfield K :=
    { carrier := A
      zero_mem' := zero_mem A
      add_mem' := fun hx hy => add_mem hx hy
      neg_mem' := fun hx => neg_mem hx
      one_mem' := hA_one
      mul_mem' := fun hx hy => hA_mul _ hx _ hy
      inv_mem' := hA_inv }
  have hFtop : F = ⊤ := by
    rw [eq_top_iff, ← hr]
    refine Subfield.closure_le.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    simpa [F] using AddSubgroup.subset_closure
      (Set.mem_range_self (f := fun k : ℕ => r ^ k) 1)
  have hAuniv : (A : Set K) = Set.univ := by
    have hF : (F : Set K) = Set.univ := by rw [hFtop]; rfl
    simpa [F] using hF
  exact SetLike.ext' hAuniv

theorem transvection_mem_of_diag {n : ℕ} {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    {D : SpecialLinearGroup (Fin n) K} (hD : D ∈ H) {d : Fin n → K}
    (hDcoe : (D : Matrix (Fin n) (Fin n) K) = diagonal d)
    {i j : Fin n} (hij : i ≠ j) {s : K}
    (hs : SpecialLinearGroup.transvection hij s ∈ H) :
    ∀ t ∈ AddSubgroup.closure (Set.range fun k : ℕ => (d i / d j) ^ k),
      SpecialLinearGroup.transvection hij (s * t) ∈ H := by
  let B : AddSubgroup K :=
    { carrier := {t : K | SpecialLinearGroup.transvection hij (s * t) ∈ H}
      zero_mem' := by
        change SpecialLinearGroup.transvection hij (s * 0) ∈ H
        simpa using H.one_mem
      add_mem' := by
        intro x y hx hy
        have hx' : SpecialLinearGroup.transvection hij (s * x) ∈ H := hx
        have hy' : SpecialLinearGroup.transvection hij (s * y) ∈ H := hy
        change SpecialLinearGroup.transvection hij (s * (x + y)) ∈ H
        have hxy : s * (x + y) = s * x + s * y := by ring
        rw [hxy, SpecialLinearGroup.transvection_add]
        exact H.mul_mem hx' hy'
      neg_mem' := by
        intro x hx
        have hx' : SpecialLinearGroup.transvection hij (s * x) ∈ H := hx
        change SpecialLinearGroup.transvection hij (s * (-x)) ∈ H
        have hxy : s * (-x) = -(s * x) := by ring
        rw [hxy, ← SpecialLinearGroup.transvection_inv]
        exact H.inv_mem hx' }
  have hrange : Set.range (fun k : ℕ => (d i / d j) ^ k) ⊆ B := by
    rintro t ⟨k, rfl⟩
    induction k with
    | zero => simpa [B] using hs
    | succ k ih =>
        have ih' : SpecialLinearGroup.transvection hij (s * (d i / d j) ^ k) ∈ H := by
          simpa [B] using ih
        have hconj := CFSG.LieType.Universal.SpecialLinear.conj_transvection_of_coe_eq_diagonal
          (F := K) hDcoe hij (s * (d i / d j) ^ k)
        have hmem : D * SpecialLinearGroup.transvection hij (s * (d i / d j) ^ k) * D⁻¹ ∈ H :=
          H.mul_mem (H.mul_mem hD ih') (H.inv_mem hD)
        rw [hconj] at hmem
        have hratio : d i * (s * (d i / d j) ^ k) * (d j)⁻¹ =
            s * (d i / d j) ^ (k + 1) := by
          rw [pow_succ]
          ring
        change SpecialLinearGroup.transvection hij (s * (d i / d j) ^ (k + 1)) ∈ H
        rwa [hratio] at hmem
  intro t ht
  exact (AddSubgroup.closure_le (K := B)).mpr hrange ht

theorem transvection_mem_of_diag_of_closure_eq_top {n : ℕ}
    {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    {D : SpecialLinearGroup (Fin n) K} (hD : D ∈ H) {d : Fin n → K}
    (hDcoe : (D : Matrix (Fin n) (Fin n) K) = diagonal d)
    {i j : Fin n} (hij : i ≠ j) {s : K}
    (hs : SpecialLinearGroup.transvection hij s ∈ H)
    (hspan : AddSubgroup.closure (Set.range fun k : ℕ => (d i / d j) ^ k) = ⊤) :
    ∀ t : K, SpecialLinearGroup.transvection hij (s * t) ∈ H := by
  intro t
  exact transvection_mem_of_diag hD hDcoe hij hs t (by rw [hspan]; exact AddSubgroup.mem_top t)

theorem eq_top_of_transvection_one_of_diag [Fintype K]
    (H : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hT : ∀ (i j : Fin 3) (hij : i ≠ j),
      SpecialLinearGroup.transvection hij (1 : K) ∈ H)
    {lam : K} (hlam : lam ≠ 0)
    (D : SpecialLinearGroup (Fin 3) K)
    (hDcoe : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![lam, 1, lam⁻¹])
    (hD : D ∈ H)
    (hclosure : Subfield.closure ({lam} : Set K) = ⊤) :
    H = ⊤ := by
  let d : Fin 3 → K := ![lam, 1, lam⁻¹]
  have hDcoe' : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    simpa [d] using hDcoe
  have hd0 : d 0 = lam := by simp [d]
  have hd1 : d 1 = 1 := by simp [d]
  have hd2 : d 2 = lam⁻¹ := by simp [d]
  have hspanlam : AddSubgroup.closure (Set.range fun k : ℕ => lam ^ k) = ⊤ :=
    addSubgroup_closure_pow_eq_top (r := lam) hclosure
  have hclosure_inv : Subfield.closure ({lam⁻¹} : Set K) = ⊤ := by
    rw [eq_top_iff, ← hclosure]
    refine Subfield.closure_le.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    simpa using inv_mem (Subfield.subset_closure (Set.mem_singleton (lam⁻¹)))
  have hspanlaminv : AddSubgroup.closure (Set.range fun k : ℕ => (lam⁻¹) ^ k) = ⊤ :=
    addSubgroup_closure_pow_eq_top (r := lam⁻¹) hclosure_inv
  have hspan01 : AddSubgroup.closure (Set.range fun k : ℕ => (d 0 / d 1) ^ k) = ⊤ := by
    have hrat : d 0 / d 1 = lam := by rw [hd0, hd1, div_one]
    simpa [hrat] using hspanlam
  have hspan12 : AddSubgroup.closure (Set.range fun k : ℕ => (d 1 / d 2) ^ k) = ⊤ := by
    have hrat : d 1 / d 2 = lam := by rw [hd1, hd2, one_div, inv_inv]
    simpa [hrat] using hspanlam
  have hspan10 : AddSubgroup.closure (Set.range fun k : ℕ => (d 1 / d 0) ^ k) = ⊤ := by
    have hrat : d 1 / d 0 = lam⁻¹ := by rw [hd1, hd0, one_div]
    simpa [hrat] using hspanlaminv
  have hspan21 : AddSubgroup.closure (Set.range fun k : ℕ => (d 2 / d 1) ^ k) = ⊤ := by
    have hrat : d 2 / d 1 = lam⁻¹ := by rw [hd2, hd1, div_one]
    simpa [hrat] using hspanlaminv
  have hX01 : ∀ t : K,
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t ∈ H := by
    intro t
    have h := transvection_mem_of_diag_of_closure_eq_top (H := H) (D := D) hD hDcoe'
      (show (0 : Fin 3) ≠ 1 by decide) (s := (1 : K)) (hT 0 1 (by decide)) hspan01 t
    simpa using h
  have hX12 : ∀ t : K,
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t ∈ H := by
    intro t
    have h := transvection_mem_of_diag_of_closure_eq_top (H := H) (D := D) hD hDcoe'
      (show (1 : Fin 3) ≠ 2 by decide) (s := (1 : K)) (hT 1 2 (by decide)) hspan12 t
    simpa using h
  have hX10 : ∀ t : K,
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t ∈ H := by
    intro t
    have h := transvection_mem_of_diag_of_closure_eq_top (H := H) (D := D) hD hDcoe'
      (show (1 : Fin 3) ≠ 0 by decide) (s := (1 : K)) (hT 1 0 (by decide)) hspan10 t
    simpa using h
  have hX21 : ∀ t : K,
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t ∈ H := by
    intro t
    have h := transvection_mem_of_diag_of_closure_eq_top (H := H) (D := D) hD hDcoe'
      (show (2 : Fin 3) ≠ 1 by decide) (s := (1 : K)) (hT 2 1 (by decide)) hspan21 t
    simpa using h
  have hX02 : ∀ t : K,
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t ∈ H := by
    intro t
    have hcomm := SpecialLinearGroup.commutatorElement_transvection
      (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)
      (show (0 : Fin 3) ≠ 2 by decide) t 1
    have hmem : ⁅SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t,
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : K)⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hX01 t) (hX12 1))
        (H.inv_mem (hX01 t))) (H.inv_mem (hX12 1))
    rw [hcomm, mul_one] at hmem
    exact hmem
  have hX20 : ∀ t : K,
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t ∈ H := by
    intro t
    have hcomm := SpecialLinearGroup.commutatorElement_transvection
      (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) t 1
    have hmem : ⁅SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t,
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : K)⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hX21 t) (hX10 1))
        (H.inv_mem (hX21 t))) (H.inv_mem (hX10 1))
    rw [hcomm, mul_one] at hmem
    exact hmem
  refine closure_transvections_eq_top H ?_
  intro i j hij t
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact hX01 t
      | exact hX02 t
      | exact hX10 t
      | exact hX12 t
      | exact hX20 t
      | exact hX21 t

private def unitriMat (a b c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, a, c; 0, 1, b; 0, 0, 1]

private def unitri (a b c : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨unitriMat a b c, by
    rw [Matrix.det_fin_three]
    simp [unitriMat]⟩

private lemma unitri_coe (a b c : K) :
    (unitri a b c : Matrix (Fin 3) (Fin 3) K) = unitriMat a b c := rfl

private lemma unitriMat_mul (a b c a' b' c' : K) :
    unitriMat a b c * unitriMat a' b' c' = unitriMat (a + a') (b + b') (c + a * b' + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitriMat, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private lemma unitri_mul (a b c a' b' c' : K) :
    unitri a b c * unitri a' b' c' = unitri (a + a') (b + b') (c + a * b' + c') := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, unitri_coe, unitri_coe, unitri_coe]
  exact unitriMat_mul a b c a' b' c'

private def diag3 (s : K) (hs : s ≠ 0) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![s, 1, s⁻¹], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hs]⟩

private lemma diag3_coe (s : K) (hs : s ≠ 0) :
    (diag3 s hs : Matrix (Fin 3) (Fin 3) K) = diagonal ![s, 1, s⁻¹] := rfl

private lemma diag3_inv_coe (s : K) (hs : s ≠ 0) :
    (((diag3 s hs)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![s⁻¹, 1, s] := by
  rw [SpecialLinearGroup.coe_inv, diag3_coe, Matrix.adjugate_diagonal,
    Matrix.diagonal_eq_diagonal_iff]
  intro i
  fin_cases i
  · change (∏ j ∈ Finset.univ.erase (0 : Fin 3), ![s, 1, s⁻¹] j) =
      ![s⁻¹, 1, s] (0 : Fin 3)
    rw [show (Finset.univ.erase (0 : Fin 3)) = ({1, 2} : Finset (Fin 3)) by decide]
    simp
  · change (∏ j ∈ Finset.univ.erase (1 : Fin 3), ![s, 1, s⁻¹] j) =
      ![s⁻¹, 1, s] (1 : Fin 3)
    rw [show (Finset.univ.erase (1 : Fin 3)) = ({0, 2} : Finset (Fin 3)) by decide]
    simp [hs]
  · change (∏ j ∈ Finset.univ.erase (2 : Fin 3), ![s, 1, s⁻¹] j) =
      ![s⁻¹, 1, s] (2 : Fin 3)
    rw [show (Finset.univ.erase (2 : Fin 3)) = ({0, 1} : Finset (Fin 3)) by decide]
    simp

private lemma diagonal_mul_unitriMat_mul (s a b : K) (hs : s ≠ 0) :
    (diagonal ![s, 1, s⁻¹] : Matrix (Fin 3) (Fin 3) K) * unitriMat a b 0 *
        (diagonal ![s⁻¹, 1, s] : Matrix (Fin 3) (Fin 3) K) =
      unitriMat (s * a) (s * b) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitriMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, hs]
  all_goals ring

private lemma diag3_mul_unitri_mul_inv (s a b : K) (hs : s ≠ 0) :
    diag3 s hs * unitri a b 0 * (diag3 s hs)⁻¹ = unitri (s * a) (s * b) 0 := by
  apply Subtype.ext
  change (diag3 s hs : Matrix (Fin 3) (Fin 3) K) * (unitri a b 0 : Matrix (Fin 3) (Fin 3) K) *
    (((diag3 s hs)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (unitri (s * a) (s * b) 0 : Matrix (Fin 3) (Fin 3) K)
  rw [diag3_coe, unitri_coe, diag3_inv_coe, unitri_coe]
  exact diagonal_mul_unitriMat_mul s a b hs

private lemma unitri_transvection01 (a : K) :
    unitri a 0 0 = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a := by
  apply Subtype.ext
  rw [unitri_coe, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitriMat]

private lemma unitri_transvection12 (b : K) :
    unitri 0 b 0 = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) b := by
  apply Subtype.ext
  rw [unitri_coe, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitriMat]

private lemma unitri_transvection02 (c : K) :
    unitri 0 0 c = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c := by
  apply Subtype.ext
  rw [unitri_coe, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitriMat]

private lemma unitri_mul_transvection02 (a b c : K) [CharP K 2] :
    unitri a b c * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c =
      unitri a b 0 := by
  rw [← unitri_transvection02 c, unitri_mul]
  simp [CharTwo.add_self_eq_zero]

private lemma conj_transvection_swap (J : SpecialLinearGroup (Fin 3) K)
    (hJcoe : (J : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {i j : Fin 3} (hij : i ≠ j) (t : K) :
    J * SpecialLinearGroup.transvection hij t * J⁻¹ =
      SpecialLinearGroup.transvection ((Equiv.swap (0 : Fin 3) 2).injective.ne hij) t := by
  have hJcoeSigned : (J : Matrix (Fin 3) (Fin 3) K) =
      CFSG.LieType.Universal.SpecialLinear.signedPerm (Equiv.swap (0 : Fin 3) 2)
        (fun _ => (1 : K)) := by
    rw [hJcoe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.LieType.Universal.SpecialLinear.signedPerm_apply, Equiv.swap_apply_def]
  have h := CFSG.LieType.Universal.SpecialLinear.conj_transvection_of_coe_eq_signedPerm
    (g := J) (π := Equiv.swap (0 : Fin 3) 2) (ε := fun _ => (1 : K)) hJcoeSigned
    (fun s => by simp) hij t
  simpa using h

theorem eq_top_of_unitary_elements [Fintype K] [CharP K 2]
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {lam : K}
    (H : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hX02 : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : K) ∈ H)
    (J : SpecialLinearGroup (Fin 3) K)
    (hJcoe : (J : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hJ : J ∈ H)
    (U1 : SpecialLinearGroup (Fin 3) K)
    (hU1coe : (U1 : Matrix (Fin 3) (Fin 3) K) = !![1, 1, ω; 0, 1, 1; 0, 0, 1])
    (hU1 : U1 ∈ H)
    (U2 : SpecialLinearGroup (Fin 3) K)
    (hU2coe : (U2 : Matrix (Fin 3) (Fin 3) K) = !![1, ω, ω; 0, 1, ω ^ 2; 0, 0, 1])
    (hU2 : U2 ∈ H)
    (D : SpecialLinearGroup (Fin 3) K)
    (hDcoe : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![lam, 1, lam⁻¹])
    (hD : D ∈ H)
    (hclosure : Subfield.closure ({lam ^ 2} : Set K) = ⊤) :
    H = ⊤ := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hωsum : ω ^ 2 + ω = 1 := by
    simpa [add_assoc, CharTwo.add_self_eq_zero] using
      congrArg (fun x : K => x + 1) hω
  have hωne : ω ≠ 0 := by
    intro h
    rw [h] at hω
    simpa using hω
  let d : Fin 3 → K := ![lam, 1, lam⁻¹]
  have hDcoe' : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    simpa [d] using hDcoe
  have hd0 : d 0 = lam := by simp [d]
  have hd2 : d 2 = lam⁻¹ := by simp [d]
  have hspanLam2 : AddSubgroup.closure (Set.range fun k : ℕ => (lam ^ 2) ^ k) = ⊤ :=
    addSubgroup_closure_pow_eq_top (r := lam ^ 2) hclosure
  have hspan02 : AddSubgroup.closure (Set.range fun k : ℕ => (d 0 / d 2) ^ k) = ⊤ := by
    have hrat : d 0 / d 2 = lam ^ 2 := by
      rw [hd0, hd2, div_eq_mul_inv, inv_inv, pow_two]
    simpa [hrat] using hspanLam2
  have hX02all : ∀ t : K,
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t ∈ H := by
    intro t
    have h := transvection_mem_of_diag_of_closure_eq_top (H := H) (D := D) hD hDcoe'
      (show (0 : Fin 3) ≠ 2 by decide) (s := (1 : K)) hX02 hspan02 t
    simpa using h
  have hX20all : ∀ t : K,
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t ∈ H := by
    intro t
    have hmem : J * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t *
        J⁻¹ ∈ H := H.mul_mem (H.mul_mem hJ (hX02all t)) (H.inv_mem hJ)
    have hconj : J * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t *
        J⁻¹ = SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t := by
      rw [conj_transvection_swap J hJcoe (show (0 : Fin 3) ≠ 2 by decide) t]
      rfl
    simpa [hconj] using hmem
  have hDiag_mem : ∀ (s : K) (hs : s ≠ 0), diag3 s hs ∈ H := by
    intro s hs
    have hEq : diag3 s hs = Matrix.SpecialLinearGroup.diag2n h02 s hs := by
      apply Subtype.ext
      rw [diag3_coe, Matrix.SpecialLinearGroup.diag2n_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hEq, Matrix.SpecialLinearGroup.diag2n_decompose]
    refine H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem ?_ ?_) ?_) ?_) ?_) ?_
    all_goals first
      | exact hX02all _
      | exact hX20all _
  let V1 : SpecialLinearGroup (Fin 3) K :=
    U1 * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) ω
  let V2 : SpecialLinearGroup (Fin 3) K :=
    U2 * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) ω
  have hV1 : V1 ∈ H := H.mul_mem hU1 (hX02all ω)
  have hV2 : V2 ∈ H := H.mul_mem hU2 (hX02all ω)
  have hV1eq : V1 = unitri 1 1 0 := by
    apply Subtype.ext
    change (U1 : Matrix (Fin 3) (Fin 3) K) *
        (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) ω :
          Matrix (Fin 3) (Fin 3) K) =
      ((unitri (K := K) 1 1 0 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hU1coe, SpecialLinearGroup.transvection_coe, unitri_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, unitriMat, Matrix.one_apply,
        Matrix.single_apply, CharTwo.add_self_eq_zero]
  have hV2eq : V2 = unitri ω (ω ^ 2) 0 := by
    apply Subtype.ext
    change (U2 : Matrix (Fin 3) (Fin 3) K) *
        (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) ω :
          Matrix (Fin 3) (Fin 3) K) =
      ((unitri (K := K) ω (ω ^ 2) 0 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hU2coe, SpecialLinearGroup.transvection_coe, unitri_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, unitriMat, Matrix.one_apply,
        Matrix.single_apply, CharTwo.add_self_eq_zero]
  have hX01 : ∀ t : K,
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t ∈ H := by
    intro s'
    by_cases hs' : s' = 0
    · subst hs'
      simpa using H.one_mem
    · have hs1 : s' * ω ^ 2 ≠ 0 := mul_ne_zero hs' (pow_ne_zero 2 hωne)
      let A : SpecialLinearGroup (Fin 3) K :=
        diag3 (s' * ω ^ 2) hs1 * V1 * (diag3 (s' * ω ^ 2) hs1)⁻¹
      let B : SpecialLinearGroup (Fin 3) K :=
        diag3 s' hs' * V2 * (diag3 s' hs')⁻¹
      have hA_mem : A ∈ H :=
        H.mul_mem (H.mul_mem (hDiag_mem (s' * ω ^ 2) hs1) hV1)
          (H.inv_mem (hDiag_mem (s' * ω ^ 2) hs1))
      have hB_mem : B ∈ H :=
        H.mul_mem (H.mul_mem (hDiag_mem s' hs') hV2) (H.inv_mem (hDiag_mem s' hs'))
      have hA_eq : A = unitri (s' * ω ^ 2) (s' * ω ^ 2) 0 := by
        change diag3 (s' * ω ^ 2) hs1 * V1 * (diag3 (s' * ω ^ 2) hs1)⁻¹ = _
        rw [hV1eq, diag3_mul_unitri_mul_inv]
        simp
      have hB_eq : B = unitri (s' * ω) (s' * ω ^ 2) 0 := by
        change diag3 s' hs' * V2 * (diag3 s' hs')⁻¹ = _
        rw [hV2eq, diag3_mul_unitri_mul_inv]
      let gam : K := (s' * ω ^ 2) * (s' * ω ^ 2)
      have hP_eq : A * B = unitri s' 0 gam := by
        rw [hA_eq, hB_eq, unitri_mul]
        congr 1
        · rw [← mul_add, hωsum, mul_one]
        · rw [CharTwo.add_self_eq_zero]
        · simp [gam]
      have hP_mem : A * B ∈ H := H.mul_mem hA_mem hB_mem
      have hfinal : A * B * SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) gam =
          SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) s' := by
        rw [hP_eq, unitri_mul_transvection02, unitri_transvection01]
      have hmem : A * B * SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) gam ∈ H :=
        H.mul_mem hP_mem (hX02all gam)
      rwa [hfinal] at hmem
  have hX12 : ∀ t : K,
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t ∈ H := by
    intro s'
    by_cases hs' : s' = 0
    · subst hs'
      simpa using H.one_mem
    · have hs1 : s' * ω ≠ 0 := mul_ne_zero hs' hωne
      let A : SpecialLinearGroup (Fin 3) K :=
        diag3 (s' * ω) hs1 * V1 * (diag3 (s' * ω) hs1)⁻¹
      let B : SpecialLinearGroup (Fin 3) K :=
        diag3 s' hs' * V2 * (diag3 s' hs')⁻¹
      have hA_mem : A ∈ H :=
        H.mul_mem (H.mul_mem (hDiag_mem (s' * ω) hs1) hV1)
          (H.inv_mem (hDiag_mem (s' * ω) hs1))
      have hB_mem : B ∈ H :=
        H.mul_mem (H.mul_mem (hDiag_mem s' hs') hV2) (H.inv_mem (hDiag_mem s' hs'))
      have hA_eq : A = unitri (s' * ω) (s' * ω) 0 := by
        change diag3 (s' * ω) hs1 * V1 * (diag3 (s' * ω) hs1)⁻¹ = _
        rw [hV1eq, diag3_mul_unitri_mul_inv]
        simp
      have hB_eq : B = unitri (s' * ω) (s' * ω ^ 2) 0 := by
        change diag3 s' hs' * V2 * (diag3 s' hs')⁻¹ = _
        rw [hV2eq, diag3_mul_unitri_mul_inv]
      let gam : K := (s' * ω) * (s' * ω ^ 2)
      have hP_eq : A * B = unitri 0 s' gam := by
        rw [hA_eq, hB_eq, unitri_mul]
        congr 1
        · rw [CharTwo.add_self_eq_zero]
        · rw [← mul_add, add_comm ω (ω ^ 2), hωsum, mul_one]
        · simp [gam]
      have hP_mem : A * B ∈ H := H.mul_mem hA_mem hB_mem
      have hfinal : A * B * SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) gam =
          SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) s' := by
        rw [hP_eq, unitri_mul_transvection02, unitri_transvection12]
      have hmem : A * B * SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) gam ∈ H :=
        H.mul_mem hP_mem (hX02all gam)
      rwa [hfinal] at hmem
  have hX21 : ∀ t : K,
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t ∈ H := by
    intro t
    have hmem : J * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t *
        J⁻¹ ∈ H := H.mul_mem (H.mul_mem hJ (hX01 t)) (H.inv_mem hJ)
    have hconj : J * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t *
        J⁻¹ = SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t := by
      rw [conj_transvection_swap J hJcoe (show (0 : Fin 3) ≠ 1 by decide) t]
      rfl
    rwa [hconj] at hmem
  have hX10 : ∀ t : K,
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t ∈ H := by
    intro t
    have hmem : J * SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t *
        J⁻¹ ∈ H := H.mul_mem (H.mul_mem hJ (hX12 t)) (H.inv_mem hJ)
    have hconj : J * SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t *
        J⁻¹ = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t := by
      rw [conj_transvection_swap J hJcoe (show (1 : Fin 3) ≠ 2 by decide) t]
      rfl
    rwa [hconj] at hmem
  refine closure_transvections_eq_top H ?_
  intro i j hij t
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact hX01 t
      | exact hX02all t
      | exact hX10 t
      | exact hX12 t
      | exact hX20all t
      | exact hX21 t

end CFSG.LinearAlgebra.SLThreeRootGeneration
