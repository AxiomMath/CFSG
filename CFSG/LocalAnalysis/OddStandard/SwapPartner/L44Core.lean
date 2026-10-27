module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Data
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44AltEight
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44GraphFixed
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Centralizer

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Field K] {Y : Type*} [Group Y]

private theorem conj_mem_semilinearAutGroup_four (x : projectiveSL 4 K) :
    MulAut.conj x ∈ semilinearAutGroup 4 K := by
  obtain ⟨g, rfl⟩ := proj_surjective 4 K x
  rw [← conjAut_toGL]
  exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

private theorem inner_le_semilinearAutGroup_four :
    inner (projectiveSL 4 K) ≤ semilinearAutGroup 4 K := by
  rintro f ⟨x, rfl⟩
  exact conj_mem_semilinearAutGroup_four x

theorem apply_not_mem_semilinearAutGroup (hK : Nat.card K = 4) (θ : MulAut (projectiveSL 4 K))
    (A : Subgroup (projectiveSL 4 K)) (eA : A ≃* alternatingGroup (Fin 8))
    (hθA : ∀ a ∈ A, θ a ∈ A) (hθout : ¬ ∃ a ∈ A, ∀ x ∈ A, θ x = a * x * a⁻¹) :
    θ ∉ semilinearAutGroup 4 K := by
  intro hθE
  obtain ⟨y, _hyA, hy7, a, _haA, hay⟩ :=
    exists_inverting_sevenElement A eA θ hθA hθout
  have hmem : MulAut.conj a * θ ∈ semilinearAutGroup 4 K :=
    mul_mem (conj_mem_semilinearAutGroup_four a) hθE
  have hval : (MulAut.conj a * θ) y = y⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply, hay]
  exact not_mem_semilinearAutGroup_of_apply_eq_inv hK hy7 hval hmem

theorem apply_mem_semilinearAutGroup_not_mem_inner (hK : Nat.card K = 4)
    (θ : MulAut (projectiveSL 4 K)) (A : Subgroup (projectiveSL 4 K))
    (eA : A ≃* alternatingGroup (Fin 8)) (hθ1 : θ ≠ 1) (hθ2 : θ * θ = 1)
    (hθA : ∀ a ∈ A, θ a = a) : θ ∈ semilinearAutGroup 4 K ∧ θ ∉ inner (projectiveSL 4 K) := by
  obtain ⟨y, hyA, hy7⟩ := exists_mem_orderOf_seven A eA
  have hyfix : θ y = y := hθA y hyA
  refine ⟨mem_semilinearAutGroup_of_apply_eq hK hy7 hyfix, ?_⟩
  intro hθinner
  obtain ⟨x, hx⟩ := hθinner
  have hconj_y : MulAut.conj x y = y := by rw [hx, hyfix]
  have hyx : y * x = x * y := by
    have h := hconj_y
    rw [MulAut.conj_apply] at h
    calc y * x = (x * y * x⁻¹) * x := by rw [h]
      _ = x * y := by group
  have hxx_comm : ∀ z : projectiveSL 4 K, z * (x * x) = (x * x) * z := by
    intro z
    have hcongr : MulAut.conj (x * x) z = z := by
      have h1 : MulAut.conj (x * x) = (1 : MulAut (projectiveSL 4 K)) := by
        rw [map_mul, hx, hθ2]
      rw [h1, MulAut.one_apply]
    have h2 : (x * x) * z = z * (x * x) := by
      rw [MulAut.conj_apply] at hcongr
      exact mul_inv_eq_iff_eq_mul.mp hcongr
    exact h2.symm
  have hxx : x * x = 1 := center_projectiveSL_four hK (x * x) hxx_comm
  have hx1 : x = 1 := eq_one_of_commute_of_orderOf_seven hK hy7 hxx hyx
  exact hθ1 (by rw [← hx, hx1, map_one])

theorem card_centralizer_ge_and_not_seven_dvd [Finite Y] (hK : Nat.card K = 4)
    (Ψ : Y →* MulAut (projectiveSL 4 K)) (hΨ : Function.Injective Ψ)
    (hinn : ∀ x : projectiveSL 4 K, ∃ s : Y, Ψ s = MulAut.conj x)
    (A : Subgroup (projectiveSL 4 K)) (eA : A ≃* alternatingGroup (Fin 8))
    (t d : Y) (ht1 : t ≠ 1) (ht2 : t * t = 1) (htA : ∀ a ∈ A, Ψ t a = a)
    (hd2 : d * d = 1) (hdt : d * t = t * d) (hdA : ∀ a ∈ A, Ψ d a ∈ A)
    (hdout : ¬ ∃ a ∈ A, ∀ x ∈ A, Ψ d x = a * x * a⁻¹) :
    15360 ≤ Nat.card (Subgroup.centralizer ({d} : Set Y)) ∧
      ¬ 7 ∣ Nat.card (Subgroup.centralizer ({d} : Set Y)) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hZ : ∀ z : projectiveSL 4 K, (∀ x, x * z = z * x) → z = 1 :=
    center_projectiveSL_four hK
  have hdE : Ψ d ∉ semilinearAutGroup 4 K :=
    apply_not_mem_semilinearAutGroup hK (Ψ d) A eA hdA hdout
  have ht1' : Ψ t ≠ 1 := by
    intro h
    exact ht1 (hΨ (h.trans (map_one Ψ).symm))
  have ht2' : Ψ t * Ψ t = 1 := by rw [← map_mul, ht2, map_one]
  obtain ⟨htE, htI⟩ :=
    apply_mem_semilinearAutGroup_not_mem_inner hK (Ψ t) A eA ht1' ht2' htA
  have hdtE : Ψ (d * t) ∉ semilinearAutGroup 4 K := by
    rw [map_mul]
    intro h
    apply hdE
    have h2 : Ψ d * Ψ t * (Ψ t)⁻¹ ∈ semilinearAutGroup 4 K := mul_mem h (inv_mem htE)
    have h3 : Ψ d * Ψ t * (Ψ t)⁻¹ = Ψ d := by group
    rwa [h3] at h2
  have hdI : Ψ d ∉ inner (projectiveSL 4 K) :=
    fun h => hdE (inner_le_semilinearAutGroup_four h)
  have hdtI : Ψ (d * t) ∉ inner (projectiveSL 4 K) :=
    fun h => hdtE (inner_le_semilinearAutGroup_four h)
  let e : Fin 4 → Y := ![1, d, t, d * t]
  have hd_inv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hdt' : t * d = d * t := hdt.symm
  have hdtd : d * t * d = t := by rw [mul_assoc, hdt', ← mul_assoc, hd2, one_mul]
  have hdtt : d * t * t = d := by rw [mul_assoc, ht2, mul_one]
  have hed : ∀ i, e i * d = d * e i := by
    intro i
    fin_cases i <;>
      simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2, ht2,
        hdt', hdtd, hdtt, inv_one, one_mul, mul_one]
  have hprod : ∀ i j, i ≠ j →
      e i * (e j)⁻¹ = d ∨ e i * (e j)⁻¹ = t ∨ e i * (e j)⁻¹ = d * t := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · left; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2, ht2,
        hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · right; left; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2,
        ht2, hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · right; right; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2,
        ht2, hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · left; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2, ht2,
        hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · exact absurd rfl hij
    · right; right; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2,
        ht2, hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · right; left; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2,
        ht2, hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · right; left; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2,
        ht2, hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · right; right; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2,
        ht2, hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · exact absurd rfl hij
    · left; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2, ht2,
        hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · right; right; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2,
        ht2, hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · right; left; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2,
        ht2, hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · left; simp only [e, Matrix.cons_val_zero', Matrix.cons_val_succ', ← mul_assoc, hd2, ht2,
        hdt', hdtd, hdtt, mul_inv_rev, hd_inv, ht_inv, inv_one, one_mul, mul_one]
    · exact absurd rfl hij
  have hne : ∀ i j, i ≠ j → Ψ (e i * (e j)⁻¹) ∉ inner (projectiveSL 4 K) := by
    intro i j hij
    rcases hprod i j hij with h | h | h
    · rw [h]; exact hdI
    · rw [h]; exact htI
    · rw [h]; exact hdtI
  have hdΨ2 : Ψ d * Ψ d = 1 := by rw [← map_mul, hd2, map_one]
  have h3840 : 3840 ≤ Nat.card (fixedSubgroup (Ψ d)) :=
    three_thousand_eight_hundred_forty_le_card_fixedSubgroup hK hdΨ2 hdE
  have h4le :
      4 * Nat.card (fixedSubgroup (Ψ d)) ≤ Nat.card (Subgroup.centralizer ({d} : Set Y)) :=
    four_mul_card_fixedSubgroup_le Ψ hΨ hinn hZ d e hed hne
  refine ⟨?_, ?_⟩
  · have h15360 : 15360 ≤ 4 * Nat.card (fixedSubgroup (Ψ d)) := by
      have := Nat.mul_le_mul_left 4 h3840
      omega
    exact le_trans h15360 h4le
  · intro h7dvd
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 7 h7dvd
    have hz' : orderOf (z : Y) = 7 := (Subgroup.orderOf_coe z).trans hz
    have hdz : d * (z : Y) = (z : Y) * d :=
      (Subgroup.mem_centralizer_singleton_iff.mp z.2).symm
    have hOut : Nat.Coprime 7 (Nat.card (Outer (projectiveSL 4 K))) :=
      (show Nat.Coprime 7 4 by decide).of_dvd_right (card_outer_projectiveSL_four_dvd hK)
    obtain ⟨w, hw, hwdw⟩ := exists_fixed_orderOf_of_commute Ψ hΨ hZ hOut hz' hdz
    exact hdE (mem_semilinearAutGroup_of_apply_eq hK hw hwdw)

end CFSG.OddStandard.AltStdSec.SwapPartner
