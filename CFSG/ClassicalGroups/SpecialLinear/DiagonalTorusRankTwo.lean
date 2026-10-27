module

public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
import all CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

variable {F : Type} [Field F]

def twoToFin (i : Fin 2) : Fin 3 := Fin.castLE (by omega : 2 ≤ 3) i

def twoIndex : Fin 3 := ⟨2, by omega⟩

theorem twoToFin_ne_twoIndex (i : Fin 2) : twoToFin i ≠ twoIndex := by
  intro h
  have := congrArg Fin.val h
  simp [twoToFin, twoIndex] at this
  omega

theorem twoToFin_injective : Function.Injective twoToFin :=
  Fin.castLE_injective (by omega : 2 ≤ 3)

noncomputable def diagUnit2 (t : Fˣ) (i : Fin 2) : Fin 3 → Fˣ :=
  Function.update (Function.update 1 twoIndex (t⁻¹)) (twoToFin i) t

@[simp]
theorem diagUnit2_self (t : Fˣ) (i : Fin 2) :
    diagUnit2 (F := F) t i (twoToFin i) = t := by
  simp [diagUnit2, Function.update, twoToFin_ne_twoIndex i]

@[simp]
theorem diagUnit2_twoIndex (t : Fˣ) (i : Fin 2) :
    diagUnit2 (F := F) t i twoIndex = t⁻¹ := by
  simp [diagUnit2, Function.update, (twoToFin_ne_twoIndex i).symm]

theorem diagUnit2_of_ne (t : Fˣ) (i : Fin 2) {j : Fin 3}
    (hjp : j ≠ twoToFin i) (hjq : j ≠ twoIndex) :
    diagUnit2 (F := F) t i j = 1 := by
  simp [diagUnit2, Function.update, hjp, hjq]

theorem prod_diagUnit2 (t : Fˣ) (i : Fin 2) :
    (∏ j, diagUnit2 (F := F) t i j) = 1 := by
  classical
  have hp : twoToFin i ∈ (Finset.univ : Finset (Fin 3)) := Finset.mem_univ _
  have hq : twoIndex ∈ (Finset.univ : Finset (Fin 3)) \ {twoToFin i} := by
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨Finset.mem_univ _, (twoToFin_ne_twoIndex i).symm⟩
  rw [diagUnit2, Finset.prod_update_of_mem hp, Finset.prod_update_of_mem hq]
  simp

theorem prodHom_diagUnit2 (t : Fˣ) (i : Fin 2) :
    (prodHom 3 F) (diagUnit2 (F := F) t i) = 1 := by
  rw [prodHom.eq_1]
  exact prod_diagUnit2 t i

noncomputable def diagGen2 (t : Fˣ) (i : Fin 2) :
    SpecialLinearGroup (Fin 3) F :=
  diagSLHom 3 F ⟨diagUnit2 t i, MonoidHom.mem_ker.mpr (prodHom_diagUnit2 t i)⟩

theorem coe_diagGen2 (t : Fˣ) (i : Fin 2) :
    (diagGen2 t i : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun j => (diagUnit2 (F := F) t i j : F)) :=
  coe_diagSLHom 3 F _

theorem coe_diagGen2_pow (t : Fˣ) (i : Fin 2) (k : ℕ) :
    ((diagGen2 t i ^ k : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun j => (((diagUnit2 (F := F) t i) ^ k) j : F)) := by
  rw [diagGen2, ← map_pow (diagSLHom 3 F)
    ⟨diagUnit2 t i, MonoidHom.mem_ker.mpr (prodHom_diagUnit2 t i)⟩ k,
    coe_diagSLHom, Subgroup.coe_pow]

theorem coe_diagGen2_zpow (t : Fˣ) (i : Fin 2) (a : ℤ) :
    ((diagGen2 t i ^ a : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun j => (((diagUnit2 (F := F) t i) ^ a) j : F)) := by
  rw [diagGen2, coe_diagSLHom_zpow]

theorem diagGen2_mem_diagTorus (t : Fˣ) (i : Fin 2) :
    diagGen2 (F := F) t i ∈ diagTorus 3 F := by
  rw [mem_diagTorus_iff]
  exact ⟨diagUnit2 t i, prod_diagUnit2 t i, coe_diagGen2 t i⟩

theorem orderOf_diagGen2 (t : Fˣ) (i : Fin 2) {q : ℕ}
    (hq : q.Prime) (ht : orderOf t = q) :
    orderOf (diagGen2 (F := F) t i) = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have htq : t ^ q = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have htqi : (t⁻¹) ^ q = 1 := by
    rw [inv_pow, htq, inv_one]
  apply orderOf_eq_prime
  · apply Subtype.ext
    show ((diagGen2 t i ^ q : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (1 : Matrix (Fin 3) (Fin 3) F)
    rw [coe_diagGen2_pow, Matrix.diagonal_eq_one]
    funext j
    by_cases hj : j = twoToFin i
    · subst hj
      simp [htq]
    · by_cases hj' : j = twoIndex
      · subst hj'
        simp [hj, htqi]
      · simp [diagUnit2_of_ne t i hj hj']
  · intro h
    have hmat : (diagUnit2 (F := F) t i (twoToFin i) : F) = 1 := by
      have h' := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
        (g : Matrix (Fin 3) (Fin 3) F) (twoToFin i) (twoToFin i)) h
      simpa [coe_diagGen2, SpecialLinearGroup.coe_one, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq] using h'
    rw [diagUnit2_self] at hmat
    have ht1 : t = 1 := Units.ext hmat
    rw [ht1] at ht
    rw [orderOf_one] at ht
    exact hq.ne_one ht.symm

theorem commute_diagGen2 (t : Fˣ) (i j : Fin 2) :
    Commute (diagGen2 (F := F) t i) (diagGen2 (F := F) t j) := by
  apply Subtype.ext
  change (diagGen2 (F := F) t i : Matrix (Fin 3) (Fin 3) F) *
      (diagGen2 (F := F) t j : Matrix (Fin 3) (Fin 3) F) =
    (diagGen2 (F := F) t j : Matrix (Fin 3) (Fin 3) F) *
      (diagGen2 (F := F) t i : Matrix (Fin 3) (Fin 3) F)
  rw [coe_diagGen2, coe_diagGen2, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

theorem toLin'_diagGen2_zpow_single (t : Fˣ) (i : Fin 2) (a : ℤ) :
    SpecialLinearGroup.toLin' (diagGen2 (F := F) t i ^ a)
        (Pi.single (twoToFin i) 1) =
      Pi.single (twoToFin i)
        (((diagUnit2 (F := F) t i ^ a) (twoToFin i) : Fˣ) : F) := by
  rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, coe_diagGen2_zpow,
    Matrix.diagonal_mulVec_single]
  simp

theorem dvd_of_diagGen2_zpow_fixes (t : Fˣ) (i : Fin 2) {q : ℕ}
    (ht : orderOf t = q) {a : ℤ}
    (h : SpecialLinearGroup.toLin' (diagGen2 (F := F) t i ^ a)
        (Pi.single (twoToFin i) 1) = Pi.single (twoToFin i) 1) :
    (q : ℤ) ∣ a := by
  rw [toLin'_diagGen2_zpow_single] at h
  have hval : (((diagUnit2 (F := F) t i ^ a) (twoToFin i) : Fˣ) : F) = 1 := by
    have := congrFun h (twoToFin i)
    simpa using this
  have hval' : (diagUnit2 (F := F) t i ^ a) (twoToFin i) = 1 :=
    Units.ext hval
  have hds : diagUnit2 (F := F) t i (twoToFin i) = t := by
    simp [diagUnit2, Function.update, twoToFin_ne_twoIndex i]
  have hta : t ^ a = 1 := by
    rw [← hds]
    change (diagUnit2 (F := F) t i (twoToFin i)) ^ a = 1
    exact hval'
  rw [← ht]
  exact orderOf_dvd_iff_zpow_eq_one.mpr hta

theorem toLin'_diagGen2_single_of_ne (t : Fˣ) {i j : Fin 2} (hij : i ≠ j) :
    SpecialLinearGroup.toLin' (diagGen2 (F := F) t i)
        (Pi.single (twoToFin j) 1) = Pi.single (twoToFin j) 1 := by
  have hpj : twoToFin i ≠ twoToFin j := by
    intro h
    exact hij (twoToFin_injective h)
  have hqj : twoIndex ≠ twoToFin j := by
    intro h
    have := congrArg Fin.val h
    simp [twoIndex, twoToFin] at this
    omega
  rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, coe_diagGen2,
    Matrix.diagonal_mulVec_single]
  have hval : diagUnit2 (F := F) t i (twoToFin j) = 1 :=
    diagUnit2_of_ne t i hpj.symm hqj.symm
  rw [hval]
  simp

theorem two_le_pRank_diagTorus {F : Type} [Field F] [Finite F] [CharP F 2] {q : ℕ}
    (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) :
    2 ≤ CFSG.Open.pRank q (diagTorus 3 F) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd' : q ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact hdvd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' q hdvd'
  obtain ⟨T, hTle, -, -, hTrank⟩ :=
    CFSG.exists_elemAbelian_of_commuting_moving (F := F) (X := Fin 3 → F)
      (G := SpecialLinearGroup (Fin 3) F) (ι := Fin 2) (r := q) hq
      (fun i : Fin 2 => diagGen2 (F := F) t i)
      (fun i : Fin 2 => Pi.single (twoToFin i) 1)
      (SpecialLinearGroup.toLin' : SpecialLinearGroup (Fin 3) F →*
        ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)))
      (fun i => diagGen2_mem_diagTorus t i)
      (fun i => orderOf_diagGen2 t i hq ht)
      (fun i j => commute_diagGen2 t i j)
      (fun i a h => dvd_of_diagGen2_zpow_fixes t i ht h)
      (fun i j hij => toLin'_diagGen2_single_of_ne t hij)
  have hcard : Nat.card (Fin 2) = 2 := by simp
  rw [hcard] at hTrank
  exact hTrank.trans (CFSG.SectionRank.pRank_mono hq.one_lt hTle)

end CFSG.ClassicalGroups.SpecialLinear

end
