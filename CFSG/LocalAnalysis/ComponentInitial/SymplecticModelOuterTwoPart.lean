module

public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Finset Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank

theorem scalar_mem_statedSp_iff {K : Type} [Field K] {r : ℕ} (hr : 1 ≤ r) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ StatedSp r K ↔ c ^ 2 = 1 :=
  CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hr c

theorem card_spScalars_eq_gcd (K : Type) [Field K] [Finite K] {r : ℕ} (hr : 1 ≤ r) :
    Nat.card (SymplecticHigher.spScalars r K) = Nat.gcd 2 (Nat.card K - 1) := by
  let φ : (powMonoidHom 2 : Kˣ →* Kˣ).ker → SymplecticHigher.spScalars r K := fun c =>
    ⟨⟨GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (c : Kˣ),
      (scalar_mem_statedSp_iff hr (c : Kˣ)).mpr c.2⟩, ⟨(c : Kˣ), rfl⟩⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun c c' h => ?_, fun z => ?_⟩
    · have h0 := congrArg (fun z : SymplecticHigher.spScalars r K =>
        (((z : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
          (Sum.inl ⟨0, hr⟩) (Sum.inl ⟨0, hr⟩)) h
      simp only [φ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at h0
      exact Subtype.ext (Units.ext h0)
    · obtain ⟨c, hc⟩ := z.2
      have hc2 : c ^ 2 = 1 := (scalar_mem_statedSp_iff hr c).mp (by
        rw [hc]
        exact (z : StatedSp r K).2)
      exact ⟨⟨c, hc2⟩, Subtype.ext (Subtype.ext hc)⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), IsCyclic.card_powMonoidHom_ker, Nat.card_units,
    Nat.gcd_comm]

theorem symplectic_model_outer_two_part_bound (T : Type) [Group T] (n p f : ℕ)
    (h : StatedClassicalModel T .PSp n p f) :
    Nat.card T = (p ^ f) ^ (n ^ 2) * (∏ j ∈ Icc 1 n, ((p ^ f) ^ (2 * j) - 1)) /
        Nat.gcd 2 (p ^ f - 1) ∧
      Nat.card (Outer T) ∣ 2 * f * Nat.gcd 2 (p ^ f - 1) ∧
      4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) ∧
      (3 ≤ n → Nat.card (Outer T) ∣ f * Nat.gcd 2 (p ^ f - 1)) := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  set q := p ^ f with hq
  set P := ∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1) with hP
  set d := Nat.gcd 2 (q - 1) with hd
  have hZ : Nat.card (SymplecticHigher.spScalars n K) = d := by
    rw [card_spScalars_eq_gcd K (by omega), hK]
  have hSp : Nat.card (StatedSp n K) = q ^ (n ^ 2) * P := by
    rw [SymplecticFlag.card_statedSp, hK]
  have hcardT : Nat.card T = Nat.card (StatedProj (StatedSp n K)) := Nat.card_congr e.toEquiv
  have hcardO : Nat.card (Outer T) = Nat.card (Outer (StatedProj (StatedSp n K))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
  have hd0 : d ≠ 0 := Nat.gcd_ne_zero_left (by norm_num)
  have hmul : Nat.card T * d = q ^ (n ^ 2) * P := by
    rw [hcardT, ← hZ, mul_comm, ← hSp]
    exact Subgroup.card_mul_index _
  have hord : Nat.card T = q ^ (n ^ 2) * P / d := by
    rw [← hmul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]
  obtain ⟨hout, hout3⟩ := SymplecticHigher.outer_card_dvd hp hf hK hn
  rw [← hcardO] at hout hout3
  suffices hpair : 4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) from
    ⟨hord, hout, hpair.1, hpair.2, hout3⟩
  have hq2 : 2 ≤ q := le_trans hp.two_le (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
  have hqj : ∀ j ∈ Icc 1 n, 2 ≤ q ^ (2 * j) := fun j hj => le_trans hq2 (by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (2 * j) := Nat.pow_le_pow_right (by omega) (by simp at hj; omega))
  have hfac0 : ∀ j ∈ Icc 1 n, q ^ (2 * j) - 1 ≠ 0 := fun j hj => by have := hqj j hj; omega
  have hP0 : P ≠ 0 := prod_ne_zero_iff.mpr hfac0
  have hqN0 : q ^ (n ^ 2) ≠ 0 := pow_ne_zero _ (by omega)
  have hT0 : Nat.card T ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact mul_ne_zero hqN0 hP0 hmul.symm
  have h2adic : ordProj[2] (Nat.card T) * ordProj[2] d =
      ordProj[2] (q ^ (n ^ 2)) * ordProj[2] P := by
    rw [← Nat.ordProj_mul 2 hT0 hd0, hmul, Nat.ordProj_mul 2 hqN0 hP0]
  have hPprod : ordProj[2] P = ∏ j ∈ Icc 1 n, ordProj[2] (q ^ (2 * j) - 1) :=
    ordProj_two_prod _ _ hfac0
  have hfbounds := (lie_order_two_adic_arithmetic).2.2 f hf
  have hf2pos : 0 < ordProj[2] f := Nat.ordProj_pos f 2
  have h2 : ordProj[2] 2 = 2 := ordProj_two_two_pow 1
  have hf0 : f ≠ 0 := by omega
  have ho := ordProj_two_le_of_dvd (mul_ne_zero (mul_ne_zero two_ne_zero hf0) hd0) hout
  rw [Nat.ordProj_mul 2 (mul_ne_zero two_ne_zero hf0) hd0, Nat.ordProj_mul 2 two_ne_zero hf0,
    h2] at ho
  rcases eq_or_ne p 2 with rfl | hp2
  ·
    have hqeven : Even q := (Nat.even_pow' (by omega)).mpr even_two
    have hd1 : ordProj[2] d = 1 :=
      ordProj_two_eq_one_of_odd (Odd.of_dvd_nat (Nat.Even.sub_odd (by omega) hqeven odd_one)
        (Nat.gcd_dvd_right 2 (q - 1)))
    have hP1 : ordProj[2] P = 1 := by
      rw [hPprod]
      refine prod_eq_one fun j hj => ordProj_two_eq_one_of_odd ?_
      have hqje : Even (q ^ (2 * j)) := (Nat.even_pow' (by simp at hj; omega)).mpr hqeven
      exact Nat.Even.sub_odd (by have := hqj j hj; omega) hqje odd_one
    have ha : ordProj[2] (Nat.card T) = 2 ^ (f * n ^ 2) := by
      rw [hd1, mul_one, hP1, mul_one, hq, ← pow_mul, ordProj_two_two_pow] at h2adic
      exact h2adic
    rw [hd1, mul_one] at ho
    have hn2 : 3 ≤ n ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hn 2)
    have hle : 2 ^ (3 * f) ≤ 2 ^ (f * n ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm 3 f]; exact Nat.mul_le_mul_left f hn2)
    have h8 : 8 ≤ 2 ^ (3 * f) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [ha]
    exact ⟨by omega, by omega⟩
  ·
    have hqodd : Odd q := (hp.odd_of_ne_two hp2).pow
    have hd2 : d = 2 := Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one))
    have hqN1 : ordProj[2] (q ^ (n ^ 2)) = 1 := ordProj_two_eq_one_of_odd hqodd.pow
    rw [hqN1, one_mul, hd2, h2, hPprod] at h2adic
    rw [hd2, h2] at ho
    have h8 := ((lie_order_two_adic_arithmetic).1 p f hp hp2 hf).2
    rw [← hq] at h8
    have hq4 : q ^ 4 - 1 ≠ 0 := by
      have : 2 ≤ q ^ 4 := le_trans hq2 (by
        calc q = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num))
      omega
    have hB : ordProj[2] (q ^ 2 - 1) ≤ ordProj[2] (q ^ 4 - 1) := by
      refine ordProj_two_le_of_dvd hq4 ?_
      have h := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 2
      rwa [one_pow, show (q ^ 2) ^ 2 = q ^ 4 by ring] at h
    have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 n := by
      intro j hj
      simp only [mem_insert, mem_singleton] at hj
      rw [mem_Icc]
      omega
    have hPge : ordProj[2] (q ^ 2 - 1) * ordProj[2] (q ^ 4 - 1) ≤
        ∏ j ∈ Icc 1 n, ordProj[2] (q ^ (2 * j) - 1) := by
      calc ordProj[2] (q ^ 2 - 1) * ordProj[2] (q ^ 4 - 1) =
          ∏ j ∈ ({1, 2} : Finset ℕ), ordProj[2] (q ^ (2 * j) - 1) := by
            rw [prod_pair (by norm_num)]
        _ ≤ _ := prod_le_prod_of_subset_of_one_le hsub fun j _ _ => Nat.ordProj_pos _ _
    have hBB : 64 * ordProj[2] f * ordProj[2] f ≤ ordProj[2] (Nat.card T) * 2 := by
      rw [h2adic]
      calc 64 * ordProj[2] f * ordProj[2] f = (8 * ordProj[2] f) * (8 * ordProj[2] f) := by ring
        _ ≤ ordProj[2] (q ^ 2 - 1) * ordProj[2] (q ^ 4 - 1) :=
          Nat.mul_le_mul h8 (h8.trans hB)
        _ ≤ _ := hPge
    exact ⟨by nlinarith, by nlinarith⟩

end CFSG.LocalAnalysis.ComponentInitial
