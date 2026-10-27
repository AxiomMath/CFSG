module

public import CFSG.LieType.SpecialLinear.TypeLabel.Basic
public import CFSG.LieType.SpecialLinear.CurtisDatum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.SpecialLinear
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

noncomputable section

variable (m : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {k : Type} [Field k]

theorem sum_bExp_eq (ε : Fin f → Finset (Fin (m + 1))) :
    ∑ a, CFSG.LieType.Universal.Unitary.bExp ε a =
      ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ) := by
  have hcard : ∀ j : Fin (m + 1),
      (Finset.univ.filter fun a : Fin (m + 1) => a < j).card = (j : ℕ) := by
    intro j
    have hIio : (Finset.univ.filter fun a : Fin (m + 1) => a < j) = Finset.Iio j := by
      ext a
      simp
    rw [hIio, Fin.card_Iio]
  simp only [CFSG.LieType.Universal.Unitary.bExp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  calc ∑ a : Fin (m + 1), ((ε r).filter fun j => a < j).card
      = ∑ a : Fin (m + 1), ∑ j ∈ ε r, (if a < j then 1 else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.card_filter]
    _ = ∑ j ∈ ε r, ∑ a : Fin (m + 1), (if a < j then 1 else 0) := Finset.sum_comm
    _ = ∑ j ∈ ε r, (j : ℕ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_boole, hcard]
        simp

theorem scalarElement_mem_H (c : Fˣ) (hc : c ^ (m + 1) = 1) :
    LinearFlag.scalarElement c hc ∈ (curtisDatum m F 2).H := by
  rw [show (curtisDatum m F 2).H = ⨆ j, torus m F j from rfl]
  rw [mem_iSup_torus_iff, LinearFlag.coe_scalarElement, Matrix.scalar_apply]
  exact Matrix.isDiag_diagonal _

omit [Finite F] [CharP F 2] in
theorem slChiEps_scalarElement (φ : F →+* k) (ε : Fin f → Finset (Fin (m + 1))) (c : Fˣ)
    (hc : c ^ (m + 1) = 1) :
    slChiEps m φ ε (LinearFlag.scalarElement c hc) =
      φ ((c : F) ^ ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ)) := by
  simp only [slChiEps, LinearFlag.coe_scalarElement, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq]
  rw [Finset.prod_pow_eq_pow_sum, sum_bExp_eq]

theorem orderOf_dvd_of_isCoverType_scalar [CharP k 2] [Algebra F k] {V : Type*} [AddCommGroup V]
    [Module k V] {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) {ε : Fin f → Finset (Fin (m + 1))}
    (hε : ∀ g ∈ (curtisDatum m F 2).H, χ g = slChiEps m (algebraMap F k) ε g)
    {c : Fˣ} (hc : c ^ (m + 1) = 1) (h1 : ρ (LinearFlag.scalarElement c hc) = 1) :
    orderOf c ∣ ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ) := by
  set z := LinearFlag.scalarElement c hc with hz
  have hzH : z ∈ (curtisDatum m F 2).H := scalarElement_mem_H m c hc
  have hρy : ρ z y = y := by
    rw [hz, h1]
    rfl
  have hχy : χ z • y = y := by
    rw [← ht.2.2.1 z hzH, hρy]
  have hχ : χ z = 1 := by
    refine (smul_left_injective k ht.2.1) ?_
    change χ z • y = 1 • y
    rw [hχy, one_smul]
  have hχ' : slChiEps m (algebraMap F k) ε z = 1 := by
    rw [← hε z hzH, hχ]
  rw [slChiEps_scalarElement m (algebraMap F k) ε c hc] at hχ'
  have hpow : (c : F) ^ (∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ)) = 1 :=
    (algebraMap F k).injective (by rw [hχ', map_one])
  refine orderOf_dvd_iff_pow_eq_one.mpr ?_
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact hpow

omit [CharP F 2] in
theorem exists_orderOf_eq_of_dvd (hF : Nat.card F = 2 ^ f) {r : ℕ} (hrm : r ∣ m + 1)
    (hrq : r ∣ 2 ^ f - 1) : ∃ c : Fˣ, orderOf c = r ∧ c ^ (m + 1) = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hf1 : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := Nat.eq_zero_of_not_pos h
    have h2 : 1 < Nat.card F := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [hF, hf0, pow_zero] at h2
    exact lt_irrefl 1 h2
  have hpos : 0 < 2 ^ f - 1 := by
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    omega
  have hcard : Nat.card Fˣ = 2 ^ f - 1 := by
    rw [Nat.card_units, hF]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = 2 ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hrdvd : r ∣ orderOf g := by
    rw [hord]
    exact hrq
  have hord0 : orderOf g ≠ 0 := by
    rw [hord]
    omega
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Nat.zero_dvd] at hrq
    omega
  refine ⟨g ^ ((2 ^ f - 1) / r), ?_, ?_⟩
  · rw [← hord]
    exact orderOf_pow_orderOf_div hord0 hrdvd
  · have hdvd : 2 ^ f - 1 ∣ (2 ^ f - 1) / r * (m + 1) := by
      obtain ⟨t, ht⟩ := hrq
      obtain ⟨u, hu⟩ := hrm
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      refine ⟨u, ?_⟩
      rw [ht, hu, Nat.mul_div_cancel_left t hrpos]
      ring
    obtain ⟨u, hu⟩ := hdvd
    rw [← pow_mul, hu, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]

end

end CFSG.LieType.SpecialLinear
