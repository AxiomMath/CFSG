module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Seg27Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpDihedral

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private theorem gamma_invTwoI_orderOf_sq_ne_two {x : G} (h : orderOf x = 3 ∨ orderOf x = 6) :
    orderOf (x ^ 2) ≠ 2 := by
  have hx6 : x ^ 6 = 1 := by
    rcases h with h | h
    · have hx3 : x ^ 3 = 1 := by rw [← h]; exact pow_orderOf_eq_one x
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul x 3 2, hx3, one_pow]
    · rw [← h]; exact pow_orderOf_eq_one x
  have h6 : (x ^ 2) ^ 3 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul x 2 3] at hx6
    exact hx6
  intro h2
  have hdvd : orderOf (x ^ 2) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h6
  rw [h2] at hdvd
  norm_num at hdvd

private theorem gamma_invTwoI_sq_mul_eq_one {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hc : x * y = y * x) : (x * y) ^ 2 = 1 := by
  have hcomm : Commute x y := hc
  rw [hcomm.mul_pow 2, hx, hy, mul_one]

theorem gamma_sixA_eq (H : GammaHyps a z) {y b : G} (hy : y ∈ orb6A a a)
    (hb : b ∈ orb2A a a ∩ orb2A a y) : b = (a * y) ^ 3 := by
  obtain ⟨hb0, hrow⟩ := tableV_orb6A_row H.h hy
  have hset := (H.hPerp.self).perp_4B_6A ((a * y) ^ 3) hb0 y (Or.inr hrow)
  have hbcenter : b ∈ centerOf (Subgroup.closure {a, y}) ∧ b ≠ 1 := by
    have hmem : b ∈ {w : G | w ∈ centerOf (Subgroup.closure {a, y}) ∧ w ≠ 1} := hset ▸ hb
    simpa only [Set.mem_setOf_eq] using hmem
  exact (perp_center_closure_pair (c := y) (H.sq_a (IsConj.refl a)) (H.sq_a hy.1)
    (k := 3) (by norm_num) (by rw [hy.2.1]) b).mp hbcenter

theorem gamma_partner (H : GammaHyps a z) {y b : G} (hy : y ∈ orb3A a a ∪ orb6A a a)
    (hb : b ∈ orb2A a a ∩ orb2A a y) :
    ∃ c ∈ orb6A a y, (y * c) ^ 3 = b ∧ Gxy y c ≤ Gx a := by
  rcases hy with hy | hy
  ·
    obtain ⟨hyA, hord3, -⟩ := hy
    have hbA : IsConj a b := hb.1.1
    have hab : a * b = b * a := H.comm_of_orb2A (IsConj.refl a) hb.1
    have hby : y * b = b * y := H.comm_of_orb2A hyA hb.2
    have hya : y * a = (a * y)⁻¹ := by
      rw [mul_inv_rev, H.inv_a (IsConj.refl a), H.inv_a hyA]
    have hord3' : orderOf (y * a) = 3 := by
      rw [hya, orderOf_inv]
      exact hord3
    have hcomm_yab : Commute (y * a) b := by
      show (y * a) * b = b * (y * a)
      calc (y * a) * b = y * (a * b) := by rw [mul_assoc]
        _ = y * (b * a) := by rw [hab]
        _ = (y * b) * a := by rw [mul_assoc]
        _ = (b * y) * a := by rw [hby]
        _ = b * (y * a) := by rw [mul_assoc]
    have hcube : (y * (a * b)) ^ 3 = b := by
      have hmul : y * (a * b) = (y * a) * b := (mul_assoc y a b).symm
      have h3 : (y * a) ^ 3 = 1 := by rw [← hord3']; exact pow_orderOf_eq_one (y * a)
      have hb3 : b ^ 3 = b := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, H.sq_a hbA, one_mul, pow_one]
      rw [hmul, hcomm_yab.mul_pow 3, h3, one_mul, hb3]
    have hord6 : orderOf (y * (a * b)) = 6 := by
      have hco : (orderOf (y * a)).Coprime (orderOf b) := by
        rw [hord3', H.orderOf_a hbA]
        decide
      rw [show y * (a * b) = (y * a) * b by rw [mul_assoc],
        hcomm_yab.orderOf_mul_eq_mul_orderOf_of_coprime hco, hord3', H.orderOf_a hbA]
    refine ⟨a * b, ⟨hb.1.2, hord6, ?_⟩, hcube, ?_⟩
    · rw [hcube]; exact hb.1.1
    · intro g hg
      rw [mem_Gxy] at hg
      obtain ⟨hgy, hgc⟩ := hg
      rw [mem_Gx] at hgy hgc ⊢
      have hcomm2 : Commute g (y * (a * b)) := by
        show g * (y * (a * b)) = (y * (a * b)) * g
        calc g * (y * (a * b)) = (g * y) * (a * b) := by rw [mul_assoc]
          _ = (y * g) * (a * b) := by rw [hgy]
          _ = y * (g * (a * b)) := by rw [mul_assoc]
          _ = y * ((a * b) * g) := by rw [hgc]
          _ = (y * (a * b)) * g := by rw [← mul_assoc]
      have hgb : Commute g b := by
        have h := hcomm2.pow_right 3
        rwa [hcube] at h
      have habb : (a * b) * b = a := by
        rw [mul_assoc, H.mul_self_a hbA, mul_one]
      have h1 : Commute (a * b) g := hgc
      have h2 : Commute b g := hgb.symm
      have h3 : Commute ((a * b) * b) g := h1.mul_left h2
      rwa [habb] at h3
  ·
    have hbeq : b = (a * y) ^ 3 := gamma_sixA_eq H hy hb
    obtain ⟨hyA, hord6, hy6⟩ := hy
    have hbA : IsConj a b := hb.1.1
    have hya : y * a = (a * y)⁻¹ := by
      rw [mul_inv_rev, H.inv_a (IsConj.refl a), H.inv_a hyA]
    have hcube : (y * a) ^ 3 = b := by
      rw [hya, inv_pow, hbeq, H.inv_a hy6]
    refine ⟨a, ⟨IsConj.refl a, ?_, ?_⟩, hcube, ?_⟩
    · rw [hya, orderOf_inv]; exact hord6
    · rw [hcube]; exact hbA
    · intro g hg
      rw [mem_Gxy] at hg
      exact hg.2

theorem gamma_inv_two_i (H : GammaHyps a z) {y t b : G} (hy : y ∈ orb3A a a ∪ orb6A a a)
    (hb : b ∈ orb2A a a ∩ orb2A a y) (ht : t ∈ orb2A a y)
    (htb : t ∈ orb2A a b ∪ orb2B a z b ∪ orb3A a b ∪ orb4B a b ∪ orb6A a b) :
    ∃ s : G, orderOf s = 2 ∧ s ∈ Gxyz a y t := by
  obtain ⟨c, hc, hc3, hca⟩ := gamma_partner H hy hb
  have hyA : IsConj a y := by rcases hy with h | h <;> exact h.1
  have hbA : IsConj a b := hb.1.1
  have hyb : y ∈ orb2A a b := H.orb2A_symm hyA hb.2
  rcases gamma_rows H hbA hyb ht with hcomm | ⟨-, hS6⟩ | ⟨hz4, -⟩ | ⟨c', hc', hc'3, hle⟩
  · refine ⟨b, H.orderOf_a hbA, ?_⟩
    rw [mem_Gxyz]
    exact ⟨mem_Gx.mpr (H.comm_of_orb2A (IsConj.refl a) hb.1),
      mem_Gx.mpr (H.comm_of_orb2A hyA hb.2), mem_Gx.mpr hcomm⟩
  · obtain ⟨s, hs, hsord⟩ :=
      gamma_seg27_S5y_S6 H hbA hyb hc hc3 (L := Gxyz b y t)
        (by rw [Gxyz_eq_inf]; exact inf_le_left) hS6
    rw [Subgroup.mem_inf] at hs
    obtain ⟨hsyc, hsbt⟩ := hs
    refine ⟨s, hsord, ?_⟩
    rw [mem_Gxyz]
    exact ⟨hca hsyc, (mem_Gxy.mp hsyc).1, (mem_Gxyz.mp hsbt).2.2⟩
  · rcases htb with (((ht2A | ht2B) | ht3A) | ht4B) | ht6A
    · exfalso
      have hbt2 : (b * t) ^ 2 = 1 :=
        gamma_invTwoI_sq_mul_eq_one (H.sq_a hbA) (H.sq_a ht2A.1) (H.comm_of_orb2A hbA ht2A)
      rw [hbt2] at hz4
      exact H.ne_one_z (IsConj.refl z) (isConj_one_left.mp hz4)
    · exfalso
      have hbt2 : (b * t) ^ 2 = 1 :=
        gamma_invTwoI_sq_mul_eq_one (H.sq_a hbA) (H.sq_a ht2B.1) (H.comm_of_orb2B hbA ht2B)
      rw [hbt2] at hz4
      exact H.ne_one_z (IsConj.refl z) (isConj_one_left.mp hz4)
    · exfalso
      exact gamma_invTwoI_orderOf_sq_ne_two (Or.inl ht3A.2.1) (H.orderOf_z hz4)
    · exfalso
      exact H.not_isConj_both ht4B.2 hz4
    · exfalso
      exact gamma_invTwoI_orderOf_sq_ne_two (Or.inr ht6A.2.1) (H.orderOf_z hz4)
  · obtain ⟨s, hs, hsord⟩ := gamma_seg27_S5_S5 H hbA hyb hc' hc'3 hc hc3
    rw [Subgroup.mem_inf] at hs
    obtain ⟨hsbc, hsyc⟩ := hs
    refine ⟨s, hsord, ?_⟩
    rw [mem_Gxyz]
    exact ⟨hca hsyc, (mem_Gxy.mp hsyc).1, (mem_Gxyz.mp (hle hsbc)).2.2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
