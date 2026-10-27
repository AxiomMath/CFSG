module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private lemma gamma_comm_of_comm_mul_cube {b u y g : G} (hb : Commute b g)
    (hu : Commute u g) (hcube : (b * u) ^ 3 = y) : Commute y g := by
  have hbu : Commute (b * u) g := hb.mul_left hu
  have h := (hbu.pow_left 3).eq
  rw [hcube] at h
  exact h

theorem gamma_rows (H : GammaHyps a z) {b y t : G} (hb : IsConj a b) (hy : y ∈ orb2A a b)
    (ht : t ∈ orb2A a y) :
    t * b = b * t ∨ ((b * t) ^ 2 = y ∧ IsShapeZ2TimesSym 6 ↥(Gxyz b y t)) ∨
      (IsConj z ((b * t) ^ 2) ∧ Nat.card ↥(Gxyz b y t) = 64) ∨
      (∃ c ∈ orb6A a b, (b * c) ^ 3 = y ∧ Gxy b c ≤ Gxyz b y t) := by
  have hyb : b * y = y * b := H.comm_of_orb2A hb hy
  have hyt : y * t = t * y := H.comm_of_orb2A hy.1 ht
  have hy' : y ∈ orb2A b b := (gamma_orb2A_eq hb b).symm ▸ hy
  have hT : TableIVFacts b z := H.hT4 b z hb (IsConj.refl z)
  have hF5b : IsF5Type b z := isF5Type_of_isConj H.h hb (IsConj.refl z)
  rcases eq_or_ne t b with htb | htb
  · left; rw [htb]
  rcases eq_or_ne t (b * y) with htby | htby
  · left
    rw [htby]
    exact ((Commute.refl b).mul_left (show Commute y b from hyb.symm)).eq
  have hbase : t ∈ sBase b y :=
    ⟨(gamma_isConj_iff hb t).2 ht.1, (gamma_isConj_iff hb (y * t)).2 ht.2, htb, htby⟩
  obtain ⟨i, hti⟩ := (hT.partition y hy').cover t hbase
  fin_cases i
  ·
    have hti0 : t ∈ sBase b y ∧ IsConj b (b * t) := hti
    left
    exact (H.comm_of_orb2A hb ⟨ht.1, (gamma_isConj_iff hb (b * t)).1 hti0.2⟩).symm
  ·
    have hti1 : t ∈ sBase b y ∧ IsConj z (b * t) := hti
    left
    exact (H.comm_of_orb2B hb ⟨ht.1, hti1.2⟩).symm
  ·
    have hti2 : t ∈ sBase b y ∧ (b * t) ^ 2 = y := hti
    exact Or.inr (Or.inl ⟨hti2.2, hT.shape_4B y hy' t hti⟩)
  ·
    have hti3 : t ∈ sBase b y ∧ IsConj z ((b * t) ^ 2) := hti
    refine Or.inr (Or.inr (Or.inl ⟨hti3.2, ?_⟩))
    simpa [Gxyz_eq_inf] using hT.card_stab y hy' 3 t hti
  ·
    have hti4 : t ∈ sBase b y ∧ orderOf (b * t) = 3 := hti
    have hytC : Commute t y := hyt.symm
    have hcy : Commute (b * t) y := (show Commute b y from hyb).mul_left hytC
    have hbt3 : (b * t) ^ 3 = 1 := by
      rw [← hti4.2]
      exact pow_orderOf_eq_one (b * t)
    have hy3 : y ^ 3 = y := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, H.sq_a hy.1, one_mul]
    have hcube4 : (b * (t * y)) ^ 3 = y := by
      rw [← mul_assoc, hcy.mul_pow 3, hbt3, hy3, one_mul]
    have hord4 : orderOf (b * (t * y)) = 6 := by
      rw [← mul_assoc]
      have hco : (orderOf (b * t)).Coprime (orderOf y) := by
        rw [hti4.2, H.orderOf_a hy.1]
        decide
      rw [hcy.orderOf_mul_eq_mul_orderOf_of_coprime hco, hti4.2, H.orderOf_a hy.1]
    have hc6 : t * y ∈ orb6A a b := by
      refine ⟨?_, hord4, ?_⟩
      · rw [hyt.symm]
        exact ht.2
      · rw [hcube4]
        exact hy.1
    refine Or.inr (Or.inr (Or.inr ⟨t * y, hc6, hcube4, ?_⟩))
    intro g hg
    obtain ⟨hgb, hgty⟩ := mem_Gxy.mp hg
    have hgy : Commute y g :=
      gamma_comm_of_comm_mul_cube (show Commute b g from mem_Gx.mp hgb)
        (show Commute (t * y) g from mem_Gx.mp hgty) hcube4
    have hgt : Commute t g := by
      have h1 : Commute ((t * y) * y⁻¹) g :=
        (show Commute (t * y) g from mem_Gx.mp hgty).mul_left hgy.inv_left
      have h2 : ((t * y) * y⁻¹) * g = g * ((t * y) * y⁻¹) := h1.eq
      have h3 : (t * y) * y⁻¹ = t := by rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [h3] at h2
      exact h2
    exact mem_Gxyz.mpr ⟨hgb, mem_Gx.mpr hgy, mem_Gx.mpr hgt⟩
  ·
    have hti5 : t ∈ sBase b y ∧ (b * t) ^ 3 = y := hti
    have hyb' : IsConj b y := (gamma_isConj_iff hb y).2 hy.1
    obtain ⟨hord5, hcube5⟩ := perp_orderOf_row_five hF5b hyb' hti
    have ht6 : t ∈ orb6A a b := ⟨ht.1, hord5, by rw [hcube5]; exact hy.1⟩
    refine Or.inr (Or.inr (Or.inr ⟨t, ht6, hcube5, ?_⟩))
    intro g hg
    obtain ⟨hgb, hgt⟩ := mem_Gxy.mp hg
    have hgy : Commute y g :=
      gamma_comm_of_comm_mul_cube (show Commute b g from mem_Gx.mp hgb)
        (show Commute t g from mem_Gx.mp hgt) hcube5
    exact mem_Gxyz.mpr ⟨hgb, mem_Gx.mpr hgy, hgt⟩

theorem gamma_rows_classes (H : GammaHyps a z) {b y t : G} (hb : IsConj a b)
    (hy : y ∈ orb2A a b) (ht : t ∈ orb2A a y) :
    t = b ∨ t ∈ orb2A a b ∪ orb2B a z b ∪ orb3A a b ∪ orb4B a b ∪ orb6A a b ∨
      t ∈ orb4A a z b := by
  have hyb : b * y = y * b := H.comm_of_orb2A hb hy
  have hyt : y * t = t * y := H.comm_of_orb2A hy.1 ht
  have hy' : y ∈ orb2A b b := (gamma_orb2A_eq hb b).symm ▸ hy
  have hT : TableIVFacts b z := H.hT4 b z hb (IsConj.refl z)
  have hF5b : IsF5Type b z := isF5Type_of_isConj H.h hb (IsConj.refl z)
  rcases eq_or_ne t b with htb | htb
  · exact Or.inl htb
  by_cases hcomm : t * b = b * t
  · right; left
    have hbtC : Commute b t := hcomm.symm
    have hsq : (b * t) ^ 2 = 1 := by
      rw [hbtC.mul_pow 2, H.sq_a hb, H.sq_a ht.1]
      simp
    have hbt_ne : b * t ≠ 1 := by
      intro h1
      have h2 : t = b := by
        have h3 : b * (b * t) = b * 1 := by rw [h1]
        rw [← mul_assoc, H.mul_self_a hb, one_mul, mul_one] at h3
        exact h3
      exact htb h2
    have hord : orderOf (b * t) = 2 := orderOf_eq_prime hsq hbt_ne
    rcases (H.hCls.self).inv_two (b * t) hord with hac | hzc
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨ht.1, hac⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨ht.1, hzc⟩)))
  · right
    have htby : t ≠ b * y := by
      intro h
      apply hcomm
      rw [h]
      exact ((Commute.refl b).mul_left (show Commute y b from hyb.symm)).eq
    have hbase : t ∈ sBase b y :=
      ⟨(gamma_isConj_iff hb t).2 ht.1, (gamma_isConj_iff hb (y * t)).2 ht.2, htb, htby⟩
    obtain ⟨i, hti⟩ := (hT.partition y hy').cover t hbase
    fin_cases i
    ·
      have hti0 : t ∈ sBase b y ∧ IsConj b (b * t) := hti
      have hcomm' : t * b = b * t :=
        (H.comm_of_orb2A hb ⟨ht.1, (gamma_isConj_iff hb (b * t)).1 hti0.2⟩).symm
      exact absurd hcomm' hcomm
    ·
      have hti1 : t ∈ sBase b y ∧ IsConj z (b * t) := hti
      exact absurd (H.comm_of_orb2B hb ⟨ht.1, hti1.2⟩).symm hcomm
    ·
      have hti2 : t ∈ sBase b y ∧ (b * t) ^ 2 = y := hti
      exact Or.inl (Or.inl (Or.inr ⟨ht.1, by rw [hti2.2]; exact hy.1⟩))
    ·
      have hti3 : t ∈ sBase b y ∧ IsConj z ((b * t) ^ 2) := hti
      exact Or.inr ⟨ht.1, hti3.2⟩
    ·
      have hti4 : t ∈ sBase b y ∧ orderOf (b * t) = 3 := hti
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨ht.1, hti4.2, ⟨y, hy, H.orb2A_symm hy.1 ht⟩⟩)))
    ·
      have hti5 : t ∈ sBase b y ∧ (b * t) ^ 3 = y := hti
      have hyb' : IsConj b y := (gamma_isConj_iff hb y).2 hy.1
      obtain ⟨hord5, hcube5⟩ := perp_orderOf_row_five hF5b hyb' hti
      exact Or.inl (Or.inr ⟨ht.1, hord5, by rw [hcube5]; exact hy.1⟩)

end CFSG.EvenSporadicStandard.HNRecog.Section3
