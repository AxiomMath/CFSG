module

public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem gamma_coord_eq (γ e : Fin (n - 1) → ℤ) (h : toStdB (n - 1) γ = e) (j : Fin (n - 1)) :
    γ j = ∑ x : Fin (n - 1), if x.val ≤ j.val then e x else 0 := by
  have : γ = ofStdB (n - 1) e := by rw [← h, ofStdB_toStdB]
  rw [this]
  rfl

theorem sum_partial_single_add_single {m : ℕ} (a b' : Fin m) (x0 y0 : ℤ) (k : ℕ) :
    (∑ x : Fin m, if x.val ≤ k then (Pi.single a x0 + Pi.single b' y0 : Fin m → ℤ) x else 0) =
      (if a.val ≤ k then x0 else 0) + (if b'.val ≤ k then y0 else 0) := by
  simp only [Pi.add_apply, ite_add_zero, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single a]
    · simp
    · intro x _ hx
      simp [Pi.single_apply, hx]
    · simp
  · rw [Finset.sum_eq_single b']
    · simp
    · intro x _ hx
      simp [Pi.single_apply, hx]
    · simp

theorem minusLong_mem_radical (j : Fin (n - 1)) {a b' : Fin (n - 1)} (hab : a ≠ b') (t : Bool)
    (ha : a.val ≤ j.val) (hb : j.val < b'.val ∨ (b'.val ≤ j.val ∧ t = true)) (r : K) :
    (minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd r) ∈
      CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j := by
  set e : Fin (n - 1) → ℤ := Pi.single a (boolSign true) + Pi.single b' (boolSign t) with he
  have h : toStdB (n - 1) (ofStdB (n - 1) e) = e := toStdB_ofStdB (n - 1) e
  have hγ := mem_roots_of_toStdB_eq_long n hab true t (γ := ofStdB (n - 1) e) h
  have hpos : 0 < ofStdB (n - 1) e j := by
    rw [gamma_coord_eq (n := n) (ofStdB (n - 1) e) e h j, he]
    rw [sum_partial_single_add_single]
    cases t <;> simp only [boolSign_true, boolSign_false, Bool.false_eq_true, and_false, or_false,
      and_true] at hb ⊢ <;> split_ifs <;> omega
  exact CFSG.AGLEmbedding.LieOut.rootGroup_le_radical (D := minusDatum n hirr) hγ hpos
    (longRoot_mem_minusRootGroup n hirr hab true t h r)

theorem sum_partial_single {m : ℕ} (a : Fin m) (x0 : ℤ) (k : ℕ) :
    (∑ x : Fin m, if x.val ≤ k then (Pi.single a x0 : Fin m → ℤ) x else 0) =
      if a.val ≤ k then x0 else 0 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [Pi.single_apply, hx]
  · simp

include hirr in
theorem minusShort_mem_radical (j : Fin (n - 1)) {a : Fin (n - 1)} (ha : a.val ≤ j.val)
    (p : Fin 2 → K) :
    twShortRoot n hirr a true (Multiplicative.ofAdd p) ∈
      CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j := by
  set e : Fin (n - 1) → ℤ := Pi.single a (boolSign true) with he
  have h : toStdB (n - 1) (ofStdB (n - 1) e) = e := toStdB_ofStdB (n - 1) e
  have hγ := mem_roots_of_toStdB_eq_short n a true (γ := ofStdB (n - 1) e) h
  have hpos : 0 < ofStdB (n - 1) e j := by
    rw [gamma_coord_eq (n := n) (ofStdB (n - 1) e) e h j, he, sum_partial_single]
    simp [ha]
  exact CFSG.AGLEmbedding.LieOut.rootGroup_le_radical (D := minusDatum n hirr) hγ hpos
    (twShortRoot_mem_minusRootGroup n hirr a true h p)

end CFSG.HardMathSupport.Cooperstein.StructureLie
