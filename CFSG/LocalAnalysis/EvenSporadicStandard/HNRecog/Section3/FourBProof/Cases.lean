module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.ShapeK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Pairing

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p q : G}

private theorem fourB_ne_b_of_mem {i : Fin 7} (hi : i ≠ 0) {t : G}
    (ht : t ∈ fourBSetP a z p q i) (H : FourBHyps a z) (P : FourBPair a p q) :
    t ≠ (p * q) ^ 2 := by
  intro h
  have h0 : t ∈ fourBSetP a z p q 0 := by
    rw [h]
    simp [fourBSetP]
  exact (Set.disjoint_left.mp (fourB_set_disjoint H P i 0 hi) ht) h0

theorem fourB_case_i (H : FourBHyps a z) (P : FourBPair a p q) {t : G}
    (ht : t ∈ fourBSetP a z p q 1) :
    t * (p * q) ^ 2 ∈ fourBSetP a z p q 2 ∧ Gxyz p t q = Gxyz p (t * (p * q) ^ 2) q ∧
      IsShapeTwoTwoTimesD8 ↥(Gxyz p t q) := by
  have hsub := fourB_set_subset H P 1 ht
  simp only [Set.mem_setOf_eq] at hsub
  obtain ⟨htK, ht2⟩ := hsub
  refine ⟨fourB_mul_b_one H P t ht, fourB_Gxyz_mul_b p t q, ?_⟩
  have htb : t ≠ (p * q) ^ 2 := fourB_ne_b_of_mem (by decide) ht H P
  show Nonempty (↥(Gxyz p t q) ≃* Elem2 2 × DihedralGroup 4)
  rw [fourB_Gxyz_eq_inf]
  exact fourB_shape_D8 (fourB_shape_K H P) (fourB_b_mem H P)
    (fun k hk => mul_inv_eq_iff_eq_mul.mp (fourB_conj_b hk)) (fourB_orderOf_b H P)
    htK ht2 htb (Or.inl (fourB_one_mem_derived H P t ht))

theorem fourB_case_ii (H : FourBHyps a z) (P : FourBPair a p q) {t : G}
    (ht : t ∈ fourBSetP a z p q 4) :
    t * (p * q) ^ 2 ∈ fourBSetP a z p q 3 ∧ Gxyz p t q = Gxyz p (t * (p * q) ^ 2) q ∧
      IsShapeTwoTwoTimesS4 ↥(Gxyz p t q) := by
  have hsub := fourB_set_subset H P 4 ht
  simp only [Set.mem_setOf_eq] at hsub
  obtain ⟨htK, ht2⟩ := hsub
  refine ⟨fourB_mul_b_four H P t ht, fourB_Gxyz_mul_b p t q, ?_⟩
  have htb : t ≠ (p * q) ^ 2 := fourB_ne_b_of_mem (by decide) ht H P
  show Nonempty (↥(Gxyz p t q) ≃* Elem2 2 × Sym 4)
  rw [fourB_Gxyz_eq_inf]
  exact fourB_shape_S4 (fourB_shape_K H P) (fourB_b_mem H P)
    (fun k hk => mul_inv_eq_iff_eq_mul.mp (fourB_conj_b hk)) (fourB_orderOf_b H P)
    htK ht2 htb
    (fourB_not_mem_derived H P (i := 4) (by decide) ht)
    (fourB_not_mem_derived H P (i := 3) (by decide) (fourB_mul_b_four H P t ht))

theorem fourB_case_iii (H : FourBHyps a z) (P : FourBPair a p q) {t : G}
    (ht : t ∈ fourBSetP a z p q 6) :
    t * (p * q) ^ 2 ∈ fourBSetP a z p q 5 ∧ Gxyz p t q = Gxyz p (t * (p * q) ^ 2) q ∧
      IsShapeTwoTwoTimesS4 ↥(Gxyz p t q) := by
  have hsub := fourB_set_subset H P 6 ht
  simp only [Set.mem_setOf_eq] at hsub
  obtain ⟨htK, ht2⟩ := hsub
  refine ⟨fourB_mul_b_six H P t ht, fourB_Gxyz_mul_b p t q, ?_⟩
  have htb : t ≠ (p * q) ^ 2 := fourB_ne_b_of_mem (by decide) ht H P
  show Nonempty (↥(Gxyz p t q) ≃* Elem2 2 × Sym 4)
  rw [fourB_Gxyz_eq_inf]
  exact fourB_shape_S4 (fourB_shape_K H P) (fourB_b_mem H P)
    (fun k hk => mul_inv_eq_iff_eq_mul.mp (fourB_conj_b hk)) (fourB_orderOf_b H P)
    htK ht2 htb
    (fourB_not_mem_derived H P (i := 6) (by decide) ht)
    (fourB_not_mem_derived H P (i := 5) (by decide) (fourB_mul_b_six H P t ht))

end CFSG.EvenSporadicStandard.HNRecog.Section3
