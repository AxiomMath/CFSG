module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerMain
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5ClassPg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.StandardType.Line63.H5
open CFSG.StandardType.TypeA.PGLTor

theorem pow_eq_one_of_mem_isElemAbelian {G : Type*} [Group G] {p : ℕ} {A : Subgroup G}
    (hA : IsElemAbelian p A) {a : G} (ha : a ∈ A) : a ^ p = 1 :=
  hA.2 a ha

theorem not_three_dvd_two_pow_sub_one {n : ℕ} (hpq : 3 ∣ 2 ^ n + 1) :
    ¬ 3 ∣ 2 ^ n - 1 := by
  intro hd
  have hsub := Nat.dvd_sub hpq hd
  have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hdiff : (2 : ℕ) ^ n + 1 - (2 ^ n - 1) = 2 := by omega
  rw [hdiff] at hsub
  norm_num at hsub

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  have h2 : 2 ∣ 2 ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ⟨2 ^ k, by rw [pow_succ]; ring⟩
  obtain ⟨m, hm⟩ := h2
  have hpos : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact ⟨m - 1, by omega⟩

theorem mem_primeFormUnitary_of_pow_three_eq_one {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) {M : GL (Fin 6) K}
    (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)) (hM3 : M ^ 3 = 1) :
    M ∈ primeFormUnitary h (idGram K 6) := by
  classical
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hM
  have hn : 1 ≤ n := h.one_le
  have hmap : ((M : Matrix (Fin 6) (Fin 6) K).map h.bar) =
      (M : Matrix (Fin 6) (Fin 6) K).map (fun x => x ^ 2 ^ n) := by
    ext i j
    exact h.bar_apply (M i j)
  have hμbar : ((M : Matrix (Fin 6) (Fin 6) K).map h.bar).transpose * M =
      μ • (1 : Matrix (Fin 6) (Fin 6) K) := by
    rw [hmap]
    exact hμ
  have hbar_det : ((M : Matrix (Fin 6) (Fin 6) K).map h.bar).det =
      (M : Matrix (Fin 6) (Fin 6) K).det ^ 2 ^ n := by
    have h1 : (M : Matrix (Fin 6) (Fin 6) K).map h.bar = h.bar.mapMatrix M := rfl
    rw [h1, ← RingHom.map_det h.bar, h.bar_apply]
  have hμ6 : μ ^ 6 = 1 := by
    have hdet := congrArg Matrix.det hμbar
    rw [Matrix.det_mul, Matrix.det_transpose, hbar_det, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one] at hdet
    have hM3' : ((M ^ 3 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        (M : Matrix (Fin 6) (Fin 6) K) ^ 3 := Units.val_pow_eq_pow_val M 3
    have hM3m : (M : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1 := by
      rw [← hM3', hM3, Units.val_one]
    have hdet3 : (M : Matrix (Fin 6) (Fin 6) K).det ^ 3 = 1 := by
      have := congrArg Matrix.det hM3m
      rwa [Matrix.det_pow, Matrix.det_one] at this
    obtain ⟨k, hk⟩ := hpq
    have hdetq : (M : Matrix (Fin 6) (Fin 6) K).det ^ (2 ^ n + 1) = 1 := by
      rw [hk, pow_mul, hdet3, one_pow]
    have hdet1 : (M : Matrix (Fin 6) (Fin 6) K).det ^ 2 ^ n *
        (M : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      rw [← pow_succ]
      exact hdetq
    rw [hdet1] at hdet
    exact hdet.symm
  have hμq' : μ ^ (2 ^ n - 1) = 1 := by
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    have h : μ ^ (2 ^ n - 1) * μ = μ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      exact hμq
    exact mul_right_cancel₀ hμ0 (by rw [one_mul]; exact h)
  have hdvd6 : orderOf μ ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hμ6
  have hdvdq : orderOf μ ∣ 2 ^ n - 1 := orderOf_dvd_iff_pow_eq_one.mpr hμq'
  have hoddq : Odd (2 ^ n - 1) := odd_two_pow_sub_one hn
  have hnot2 : ¬ 2 ∣ 2 ^ n - 1 := by
    rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := hoddq
    omega
  have hnot3 : ¬ 3 ∣ 2 ^ n - 1 := not_three_dvd_two_pow_sub_one hpq
  have hle : orderOf μ ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  have hμ1 : μ = 1 := by
    interval_cases h : orderOf μ
    · have hzero : 2 ^ n - 1 = 0 := by simpa [zero_dvd_iff] using hdvdq
      have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
      omega
    · exact orderOf_eq_one_iff.mp h
    · exact absurd hdvdq hnot2
    · exact absurd hdvdq hnot3
    · norm_num at hdvd6
    · norm_num at hdvd6
    · exact absurd (dvd_trans (by norm_num : 2 ∣ 6) hdvdq) hnot2
  rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one, hmap]
  simpa [hμ1] using hμ


theorem exists_unitary_rescale {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) {M : GL (Fin 6) K}
    (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n))
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    {l c : Kˣ} (hl : M ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) l) (hc : c ^ 3 = l) :
    ∃ (M' : GL (Fin 6) K) (_ : M' ∈ LargeEvenGUSet (Fin 6) K (2 ^ n))
      (hM'N : M' ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
      M' ^ 3 = 1 ∧ M' ∈ primeFormUnitary h (idGram K 6) ∧
        TableB.projConj (unitarySU 2 n K 6)
            ⟨M, hMN⟩ =
          TableB.projConj (unitarySU 2 n K 6) ⟨M', hM'N⟩ := by
  classical
  haveI : Finite K := h.finite
  let M' : GL (Fin 6) K := Matrix.GeneralLinearGroup.scalar (Fin 6) c⁻¹ * M
  have hM'gu : M' ∈ LargeEvenGUSet (Fin 6) K (2 ^ n) :=
    scalar_mul_mem_gu h c⁻¹ hM
  have hscalN : Matrix.GeneralLinearGroup.scalar (Fin 6) c⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    TableB.scalar_mem_normalizer (unitarySU 2 n K 6) ⟨c⁻¹, rfl⟩
  have hM'N : M' ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    Subgroup.mul_mem _ hscalN hMN
  have hM'3 : M' ^ 3 = 1 := by
    dsimp only [M']
    rw [Commute.mul_pow (TypeA.PGLTor.commute_scalar c⁻¹ M) 3, ← map_pow, hl]
    have hinv : (c⁻¹) ^ 3 = l⁻¹ := by rw [inv_pow, hc]
    rw [hinv, ← map_mul, inv_mul_cancel, map_one]
  have hM'u : M' ∈ primeFormUnitary h (idGram K 6) :=
    mem_primeFormUnitary_of_pow_three_eq_one h hpq hM'gu hM'3
  refine ⟨M', hM'gu, hM'N, hM'3, hM'u, ?_⟩
  have heq : (⟨M', hM'N⟩ : Subgroup.normalizer
      (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
      (⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c⁻¹, hscalN⟩ : Subgroup.normalizer
        (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) * ⟨M, hMN⟩ :=
    Subtype.ext rfl
  have hsc1 : TableB.projConj (unitarySU 2 n K 6)
      ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c⁻¹, hscalN⟩ = 1 :=
    TableB.projConj_of_scalar (unitarySU 2 n K 6) ⟨c⁻¹, rfl⟩
  rw [heq, map_mul, hsc1, one_mul]

theorem fieldType_of_gu_pow_three_eq_scalar_not_cube {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {M : GL (Fin 6) K}
    (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n))
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    {l : Kˣ} (hM3 : M ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) l)
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l) :
    FieldType h (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) :=
  ⟨M, hM, l, hM3, hl, congrArg (TableB.projConj (unitarySU 2 n K 6)) (Subtype.ext rfl)⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
