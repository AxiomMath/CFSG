module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p q : G}

@[expose] def fourBSetP (a z p q : G) : Fin 7 → Set G :=
  ![{(p * q) ^ 2},
    orb2B a z p ∩ orb2B a z q,
    orb2BB a z p ∩ orb2BB a z q,
    orb2A a p ∩ orb2B a z q,
    orb2AB a z p ∩ orb2BB a z q,
    orb2A a q ∩ orb2B a z p,
    orb2AB a z q ∩ orb2BB a z p]

theorem fourBSetP_swap_three (a z p q : G) : fourBSetP a z q p 3 = fourBSetP a z p q 5 := rfl

theorem fourBSetP_swap_four (a z p q : G) : fourBSetP a z q p 4 = fourBSetP a z p q 6 := rfl

private lemma fourB_conj_fix {x k : G} (hk : k ∈ Gx x) : k * x * k⁻¹ = x := by
  have h : k * x = x * k := (mem_Gx.mp hk).symm
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

private lemma fourB_isConj_conj {u v k : G} (h : IsConj u v) : IsConj u (k * v * k⁻¹) :=
  h.trans (isConj_iff.2 ⟨k, rfl⟩)

private lemma fourB_conj_mem_orb2A {a x k c : G} (hk : k ∈ Gx x) (hc : c ∈ orb2A a x) :
    k * c * k⁻¹ ∈ orb2A a x := by
  refine ⟨fourB_isConj_conj hc.1, ?_⟩
  rw [mul_conj_of_fix (fourB_conj_fix hk)]
  exact fourB_isConj_conj hc.2

private lemma fourB_conj_mem_orb2B {a z x k c : G} (hk : k ∈ Gx x) (hc : c ∈ orb2B a z x) :
    k * c * k⁻¹ ∈ orb2B a z x := by
  refine ⟨fourB_isConj_conj hc.1, ?_⟩
  rw [mul_conj_of_fix (fourB_conj_fix hk)]
  exact fourB_isConj_conj hc.2

private lemma fourB_conj_mem_orb2AB {a z x k c : G} (hk : k ∈ Gx x) (hc : c ∈ orb2AB a z x) :
    k * c * k⁻¹ ∈ orb2AB a z x := by
  refine ⟨fourB_isConj_conj hc.1, ?_⟩
  rw [mul_conj_of_fix (fourB_conj_fix hk)]
  exact fourB_isConj_conj hc.2

private lemma fourB_conj_mem_orb2BB {a z x k c : G} (hk : k ∈ Gx x) (hc : c ∈ orb2BB a z x) :
    k * c * k⁻¹ ∈ orb2BB a z x := by
  refine ⟨fourB_isConj_conj hc.1, ?_⟩
  rw [mul_conj_of_fix (fourB_conj_fix hk)]
  exact fourB_isConj_conj hc.2

private lemma fourB_classes_of_mem (H : FourBHyps a z) (P : FourBPair a p q) {i : Fin 7}
    {t : G} (ht : t ∈ fourBSetP a z p q i) :
    (IsConj a t ∨ IsConj z t) ∧ (IsConj a (p * t) ∨ IsConj z (p * t)) ∧
      (IsConj a (q * t) ∨ IsConj z (q * t)) := by
  fin_cases i <;>
    simp only [fourBSetP, orb2A, orb2B, orb2AB, orb2BB, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_singleton_iff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue, Fin.reduceFinMk] at ht
  · rw [ht]
    exact ⟨Or.inl P.hb, Or.inl (fourB_isConj_pb H P), Or.inl (fourB_isConj_qb H P)⟩
  · exact ⟨Or.inl ht.1.1, Or.inr ht.1.2, Or.inr ht.2.2⟩
  · exact ⟨Or.inr ht.1.1, Or.inr ht.1.2, Or.inr ht.2.2⟩
  · exact ⟨Or.inl ht.1.1, Or.inl ht.1.2, Or.inr ht.2.2⟩
  · exact ⟨Or.inr ht.1.1, Or.inl ht.1.2, Or.inr ht.2.2⟩
  · exact ⟨Or.inl ht.1.1, Or.inr ht.2.2, Or.inl ht.1.2⟩
  · exact ⟨Or.inr ht.1.1, Or.inr ht.2.2, Or.inl ht.1.2⟩

private lemma fourB_subset_of_classes (H : FourBHyps a z) (P : FourBPair a p q) {t : G}
    (htA : IsConj a t ∨ IsConj z t) (hpA : IsConj a (p * t) ∨ IsConj z (p * t))
    (hqA : IsConj a (q * t) ∨ IsConj z (q * t)) :
    t ∈ Gxy p q ∧ orderOf t = 2 := by
  have ht2 : orderOf t = 2 :=
    htA.elim (perp_orderOf_of_isConj_a H.h) (perp_orderOf_of_isConj_z H.h)
  refine ⟨mem_Gxy.mpr ⟨mem_Gx.mpr ?_, mem_Gx.mpr ?_⟩, ht2⟩
  · exact fourB_comm_of_cls H (Or.inl P.hp) htA hpA
  · exact fourB_comm_of_cls H (Or.inl P.hq) htA hqA

theorem fourB_set_subset (H : FourBHyps a z) (P : FourBPair a p q) (i : Fin 7) :
    fourBSetP a z p q i ⊆ {t | t ∈ Gxy p q ∧ orderOf t = 2} := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := fourB_classes_of_mem H P ht
  exact fourB_subset_of_classes H P h1 h2 h3

private def fourBPat : Fin 7 → Bool × Bool × Bool :=
  ![(true, true, true), (true, false, false), (false, false, false), (true, true, false),
    (false, true, false), (true, false, true), (false, false, true)]

private lemma fourBPat_injective : Function.Injective fourBPat := by
  decide

private lemma fourB_pat_of_mem (H : FourBHyps a z) (P : FourBPair a p q) {i : Fin 7} {t : G}
    (ht : t ∈ fourBSetP a z p q i) :
    (IsConj a t ↔ (fourBPat i).1 = true) ∧ (IsConj a (p * t) ↔ (fourBPat i).2.1 = true) ∧
      (IsConj a (q * t) ↔ (fourBPat i).2.2 = true) := by
  have hn : ∀ {y : G}, IsConj z y → ¬ IsConj a y := fun h h' => fourB_not_both H h' h
  have yes : ∀ {y : G}, IsConj a y → (IsConj a y ↔ true = true) :=
    fun h => ⟨fun _ => rfl, fun _ => h⟩
  have no : ∀ {y : G}, IsConj z y → (IsConj a y ↔ false = true) :=
    fun h => ⟨fun h' => absurd h' (hn h), fun h' => absurd h' (by decide)⟩
  fin_cases i
  · have h : t = (p * q) ^ 2 := ht
    subst h
    exact ⟨yes P.hb, yes (fourB_isConj_pb H P), yes (fourB_isConj_qb H P)⟩
  · have h : (IsConj a t ∧ IsConj z (p * t)) ∧ (IsConj a t ∧ IsConj z (q * t)) := ht
    exact ⟨yes h.1.1, no h.1.2, no h.2.2⟩
  · have h : (IsConj z t ∧ IsConj z (p * t)) ∧ (IsConj z t ∧ IsConj z (q * t)) := ht
    exact ⟨no h.1.1, no h.1.2, no h.2.2⟩
  · have h : (IsConj a t ∧ IsConj a (p * t)) ∧ (IsConj a t ∧ IsConj z (q * t)) := ht
    exact ⟨yes h.1.1, yes h.1.2, no h.2.2⟩
  · have h : (IsConj z t ∧ IsConj a (p * t)) ∧ (IsConj z t ∧ IsConj z (q * t)) := ht
    exact ⟨no h.1.1, yes h.1.2, no h.2.2⟩
  · have h : (IsConj a t ∧ IsConj a (q * t)) ∧ (IsConj a t ∧ IsConj z (p * t)) := ht
    exact ⟨yes h.1.1, no h.2.2, yes h.1.2⟩
  · have h : (IsConj z t ∧ IsConj a (q * t)) ∧ (IsConj z t ∧ IsConj z (p * t)) := ht
    exact ⟨no h.1.1, no h.2.2, yes h.1.2⟩

theorem fourB_set_disjoint (H : FourBHyps a z) (P : FourBPair a p q) (i j : Fin 7) (hij : i ≠ j) :
    Disjoint (fourBSetP a z p q i) (fourBSetP a z p q j) := by
  rw [Set.disjoint_left]
  intro t hi hj
  obtain ⟨h1, h2, h3⟩ := fourB_pat_of_mem H P hi
  obtain ⟨k1, k2, k3⟩ := fourB_pat_of_mem H P hj
  apply hij
  apply fourBPat_injective
  have e1 : (fourBPat i).1 = (fourBPat j).1 := by
    rw [← Bool.coe_iff_coe]; exact h1.symm.trans k1
  have e2 : (fourBPat i).2.1 = (fourBPat j).2.1 := by
    rw [← Bool.coe_iff_coe]; exact h2.symm.trans k2
  have e3 : (fourBPat i).2.2 = (fourBPat j).2.2 := by
    rw [← Bool.coe_iff_coe]; exact h3.symm.trans k3
  exact Prod.ext e1 (Prod.ext e2 e3)

theorem fourB_set_conj (i : Fin 7) :
    ∀ k ∈ Gxy p q, ∀ c ∈ fourBSetP a z p q i, k * c * k⁻¹ ∈ fourBSetP a z p q i := by
  intro k hk c hc
  obtain ⟨hkp, hkq⟩ := mem_Gxy.mp hk
  fin_cases i <;>
    simp only [fourBSetP, Set.mem_inter_iff, Set.mem_singleton_iff, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
      Fin.reduceFinMk] at hc ⊢
  · rw [hc]
    exact fourB_conj_b hk
  · exact ⟨fourB_conj_mem_orb2B hkp hc.1, fourB_conj_mem_orb2B hkq hc.2⟩
  · exact ⟨fourB_conj_mem_orb2BB hkp hc.1, fourB_conj_mem_orb2BB hkq hc.2⟩
  · exact ⟨fourB_conj_mem_orb2A hkp hc.1, fourB_conj_mem_orb2B hkq hc.2⟩
  · exact ⟨fourB_conj_mem_orb2AB hkp hc.1, fourB_conj_mem_orb2BB hkq hc.2⟩
  · exact ⟨fourB_conj_mem_orb2A hkq hc.1, fourB_conj_mem_orb2B hkp hc.2⟩
  · exact ⟨fourB_conj_mem_orb2AB hkq hc.1, fourB_conj_mem_orb2BB hkp hc.2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
