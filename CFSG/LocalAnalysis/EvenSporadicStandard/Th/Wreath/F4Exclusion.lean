module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.PhiMap
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.CentralTransvectionComm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.UnitriangularCoord

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix SylowEnd CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D Q : Subgroup G} {z b : G}

theorem sl2F4_word_eq {R : Type*} [Ring R] (h2 : ∀ x : R, x + x = 0) {w e f : R}
    (hwe : w * e = e * w) (hwf : w * f = f * w) (hw2 : w * w = w + 1)
    (hee : e * e = 0) (hff : f * f = 0) (hefe : e * f * e = e)
    (hfef : f * e * f = f) :
    (1 + f) * (1 + e) * (1 + w * e) * (1 + f) * (1 + w * e) * (1 + f) =
      1 + (w + 1) * (e * f) + w * (f * e) := by
  have htwo : ∀ x : R, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul, h2 x]
  have hthree : ∀ x : R, (3 : ℕ) • x = x := by
    intro x
    rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, htwo, zero_add, one_nsmul]
  have hw3 : w * w * w = 1 := by
    calc w * w * w = (w + 1) * w := by rw [hw2]
      _ = w * w + w := by noncomm_ring
      _ = (w + 1) + w := by rw [hw2]
      _ = 1 := by rw [show (w + 1) + w = w + w + 1 by abel, h2 w, zero_add]
  have hw_w1 : w * (w + 1) = 1 := by
    calc w * (w + 1) = w * w + w := by noncomm_ring
      _ = (w + 1) + w := by rw [hw2]
      _ = 1 := by rw [show (w + 1) + w = w + w + 1 by abel, h2 w, zero_add]
  have hw1_w : (w + 1) * w = 1 := by
    calc (w + 1) * w = w * w + w := by noncomm_ring
      _ = (w + 1) + w := by rw [hw2]
      _ = 1 := by rw [show (w + 1) + w = w + w + 1 by abel, h2 w, zero_add]
  have hw1_sq : (w + 1) * (w + 1) = w := by
    calc (w + 1) * (w + 1) = w * w + w + w + 1 := by noncomm_ring
      _ = (w + 1) + (w + w) + 1 := by rw [hw2]; abel
      _ = (w + 1) + 0 + 1 := by rw [h2 w]
      _ = w + 1 + 1 := by abel
      _ = w := by rw [add_assoc, h2 1, add_zero]
  have h_e_we : e * (w * e) = w * (e * e) := by
    rw [← mul_assoc, ← hwe, mul_assoc]
  have h_f_we : f * (w * e) = w * (f * e) := by
    rw [← mul_assoc, ← hwf, mul_assoc]
  have h_fe_we : (f * e) * (w * e) = w * ((f * e) * e) := by
    calc (f * e) * (w * e) = f * (e * (w * e)) := by rw [mul_assoc]
      _ = f * (w * (e * e)) := by rw [h_e_we]
      _ = (f * w) * (e * e) := by rw [← mul_assoc]
      _ = (w * f) * (e * e) := by rw [← hwf]
      _ = w * (f * (e * e)) := by rw [mul_assoc]
      _ = w * ((f * e) * e) := by rw [mul_assoc]
  have h_fe_e : (f * e) * e = 0 := by
    rw [mul_assoc, hee, mul_zero]
  have h_ab : (1 + f) * (1 + e) = 1 + e + f + f * e := by noncomm_ring
  have h_abc : (1 + e + f + f * e) * (1 + w * e) =
      1 + (w + 1) * e + f + (w + 1) * (f * e) := by
    calc (1 + e + f + f * e) * (1 + w * e)
        = 1 + w * e + e + e * (w * e) + f + f * (w * e) + f * e +
            (f * e) * (w * e) := by noncomm_ring
      _ = 1 + w * e + e + w * (e * e) + f + w * (f * e) + f * e +
            w * ((f * e) * e) := by rw [h_e_we, h_f_we, h_fe_we]
      _ = 1 + w * e + e + f + w * (f * e) + f * e := by
            simp only [hee, h_fe_e, mul_zero, add_zero, zero_add]
      _ = 1 + (w + 1) * e + f + (w + 1) * (f * e) := by noncomm_ring
  have h_abca : (1 + (w + 1) * e + f + (w + 1) * (f * e)) * (1 + f) =
      1 + (w + 1) * (e + f + e * f + f * e) := by
    calc (1 + (w + 1) * e + f + (w + 1) * (f * e)) * (1 + f)
        = 1 + (w + 1) * e + f + (w + 1) * (f * e) + f + (w + 1) * (e * f) +
            f * f + (w + 1) * ((f * e) * f) := by noncomm_ring
      _ = 1 + (w + 1) * e + f + (w + 1) * (f * e) + f + (w + 1) * (e * f) +
            (w + 1) * f := by
            simp only [hff, hfef, htwo, hthree, mul_zero, add_zero, zero_add]
      _ = 1 + (w + 1) * (e + f + e * f + f * e) := by
            calc 1 + (w + 1) * e + f + (w + 1) * (f * e) + f + (w + 1) * (e * f) +
                  (w + 1) * f
                = 1 + (w + 1) * e + (w + 1) * f + (w + 1) * (e * f) +
                    (w + 1) * (f * e) + (f + f) := by noncomm_ring
              _ = 1 + (w + 1) * (e + f + e * f + f * e) := by
                    rw [h2 f, add_zero]
                    noncomm_ring
  have h_E : ((w + 1) * e) * (w * e) = 0 := by
    calc ((w + 1) * e) * (w * e) = (w + 1) * (e * (w * e)) := by rw [mul_assoc]
      _ = (w + 1) * (w * (e * e)) := by rw [h_e_we]
      _ = ((w + 1) * w) * (e * e) := by rw [← mul_assoc]
      _ = e * e := by rw [hw1_w, one_mul]
      _ = 0 := hee
  have h_F : ((w + 1) * f) * (w * e) = f * e := by
    calc ((w + 1) * f) * (w * e) = (w + 1) * (f * (w * e)) := by rw [mul_assoc]
      _ = (w + 1) * (w * (f * e)) := by rw [h_f_we]
      _ = ((w + 1) * w) * (f * e) := by rw [← mul_assoc]
      _ = f * e := by rw [hw1_w, one_mul]
  have h_ef_we : (e * f) * (w * e) = w * e := by
    calc (e * f) * (w * e) = e * (f * (w * e)) := by rw [mul_assoc]
      _ = e * (w * (f * e)) := by rw [h_f_we]
      _ = (e * w) * (f * e) := by rw [← mul_assoc]
      _ = (w * e) * (f * e) := by rw [← hwe]
      _ = w * (e * (f * e)) := by rw [mul_assoc]
      _ = w * ((e * f) * e) := by rw [mul_assoc]
      _ = w * e := by rw [hefe]
  have h_G : ((w + 1) * (e * f)) * (w * e) = e := by
    calc ((w + 1) * (e * f)) * (w * e) = (w + 1) * ((e * f) * (w * e)) := by
          rw [mul_assoc]
      _ = (w + 1) * (w * e) := by rw [h_ef_we]
      _ = ((w + 1) * w) * e := by rw [← mul_assoc]
      _ = e := by rw [hw1_w, one_mul]
  have h_H : ((w + 1) * (f * e)) * (w * e) = 0 := by
    calc ((w + 1) * (f * e)) * (w * e) = (w + 1) * ((f * e) * (w * e)) := by
          rw [mul_assoc]
      _ = (w + 1) * (w * ((f * e) * e)) := by rw [h_fe_we]
      _ = (w + 1) * (w * 0) := by rw [h_fe_e]
      _ = 0 := by rw [mul_zero, mul_zero]
  have h_abcac : (1 + (w + 1) * (e + f + e * f + f * e)) * (1 + w * e) =
      1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e) := by
    calc (1 + (w + 1) * (e + f + e * f + f * e)) * (1 + w * e)
        = (1 + (w + 1) * (e + f + e * f + f * e)) +
            (1 + (w + 1) * (e + f + e * f + f * e)) * (w * e) := by
            rw [mul_add, mul_one]
      _ = (1 + (w + 1) * (e + f + e * f + f * e)) +
            (w * e + ((w + 1) * e) * (w * e) + ((w + 1) * f) * (w * e) +
              ((w + 1) * (e * f)) * (w * e) + ((w + 1) * (f * e)) * (w * e)) := by
            congr 1
            noncomm_ring
      _ = (1 + (w + 1) * (e + f + e * f + f * e)) +
            (w * e + 0 + f * e + e + 0) := by rw [h_E, h_F, h_G, h_H]
      _ = 1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e) := by
            calc 1 + (w + 1) * (e + f + e * f + f * e) +
                  (w * e + 0 + f * e + e + 0)
                = 1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e) +
                    ((w * e + w * e) + (e + e) + (f * e + f * e)) := by noncomm_ring
              _ = 1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e) := by
                    rw [h2 (w * e), h2 e, h2 (f * e)]
                    abel
  have h_ef_f : (e * f) * f = 0 := by
    rw [mul_assoc, hff, mul_zero]
  have h_abcaca : (1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e)) * (1 + f) =
      1 + (w + 1) * (e * f) + w * (f * e) := by
    calc (1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e)) * (1 + f)
        = 1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e) + f +
            (w + 1) * (f * f) + (w + 1) * ((e * f) * f) + w * ((f * e) * f) := by
            noncomm_ring
      _ = 1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e) + f + w * f := by
            simp only [hff, h_ef_f, hfef, htwo, hthree, mul_zero, add_zero, zero_add]
      _ = 1 + (w + 1) * (e * f) + w * (f * e) := by
            calc 1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e) + f + w * f
                = 1 + (w + 1) * (e * f) + w * (f * e) + ((w * f + w * f) + (f + f)) := by
                    noncomm_ring
              _ = 1 + (w + 1) * (e * f) + w * (f * e) := by
                    rw [h2 (w * f), h2 f]
                    abel
  calc (1 + f) * (1 + e) * (1 + w * e) * (1 + f) * (1 + w * e) * (1 + f)
      = ((1 + f) * (1 + e)) * (1 + w * e) * (1 + f) * (1 + w * e) * (1 + f) := rfl
    _ = (1 + (w + 1) * e + f + (w + 1) * (f * e)) * (1 + f) * (1 + w * e) *
          (1 + f) := by rw [h_ab, h_abc]
    _ = (1 + (w + 1) * (e + f + e * f + f * e)) * (1 + w * e) * (1 + f) := by
          rw [h_abca]
    _ = (1 + (w + 1) * f + (w + 1) * (e * f) + w * (f * e)) * (1 + f) := by
          rw [h_abcac]
    _ = 1 + (w + 1) * (e * f) + w * (f * e) := h_abcaca

theorem sl2F4_conj_eq {R : Type*} [Ring R] (h2 : ∀ x : R, x + x = 0) {w e f : R}
    (hwe : w * e = e * w) (hwf : w * f = f * w) (hw2 : w * w = w + 1)
    (hee : e * e = 0) (hefe : e * f * e = e) :
    (1 + (w + 1) * (e * f) + w * (f * e)) * (1 + (w + 1) * e) =
      (1 + w * e) * (1 + (w + 1) * (e * f) + w * (f * e)) := by
  have htwo : ∀ x : R, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul, h2 x]
  have hthree : ∀ x : R, (3 : ℕ) • x = x := by
    intro x
    rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, htwo, zero_add, one_nsmul]
  have hw_w1 : w * (w + 1) = 1 := by
    calc w * (w + 1) = w * w + w := by noncomm_ring
      _ = (w + 1) + w := by rw [hw2]
      _ = 1 := by rw [show (w + 1) + w = w + w + 1 by abel, h2 w, zero_add]
  have hw1_w : (w + 1) * w = 1 := by
    calc (w + 1) * w = w * w + w := by noncomm_ring
      _ = (w + 1) + w := by rw [hw2]
      _ = 1 := by rw [show (w + 1) + w = w + w + 1 by abel, h2 w, zero_add]
  have hw1_sq : (w + 1) * (w + 1) = w := by
    calc (w + 1) * (w + 1) = w * w + w + w + 1 := by noncomm_ring
      _ = (w + 1) + (w + w) + 1 := by rw [hw2]; abel
      _ = (w + 1) + 0 + 1 := by rw [h2 w]
      _ = w + 1 + 1 := by abel
      _ = w := by rw [add_assoc, h2 1, add_zero]
  have h_e_w1 : e * (w + 1) = (w + 1) * e := by
    calc e * (w + 1) = e * w + e := by noncomm_ring
      _ = w * e + e := by rw [← hwe]
      _ = (w + 1) * e := by noncomm_ring
  have h_f_w1 : f * (w + 1) = (w + 1) * f := by
    calc f * (w + 1) = f * w + f := by noncomm_ring
      _ = w * f + f := by rw [← hwf]
      _ = (w + 1) * f := by noncomm_ring
  have h_ef_w1 : (e * f) * (w + 1) = (w + 1) * (e * f) := by
    calc (e * f) * (w + 1) = e * (f * (w + 1)) := by rw [mul_assoc]
      _ = e * ((w + 1) * f) := by rw [h_f_w1]
      _ = (e * (w + 1)) * f := by rw [mul_assoc]
      _ = ((w + 1) * e) * f := by rw [h_e_w1]
      _ = (w + 1) * (e * f) := by rw [mul_assoc]
  have h_fe_w1 : (f * e) * (w + 1) = (w + 1) * (f * e) := by
    calc (f * e) * (w + 1) = f * (e * (w + 1)) := by rw [mul_assoc]
      _ = f * ((w + 1) * e) := by rw [h_e_w1]
      _ = (f * (w + 1)) * e := by rw [mul_assoc]
      _ = ((w + 1) * f) * e := by rw [h_f_w1]
      _ = (w + 1) * (f * e) := by rw [mul_assoc]
  have h_fe_e : (f * e) * e = 0 := by
    rw [mul_assoc, hee, mul_zero]
  have h_e_sum : (w + 1) * e + w * e = e := by
    calc (w + 1) * e + w * e = (w + 1 + w) * e := by noncomm_ring
      _ = e := by
          rw [show w + 1 + w = 1 by
            calc w + 1 + w = (w + w) + 1 := by abel
              _ = 0 + 1 := by rw [h2 w]
              _ = 1 := zero_add 1,
            one_mul]
  have h_we_sum : w * e + (w + 1) * e = e := by
    rw [add_comm, h_e_sum]
  have hL1 : ((w + 1) * (e * f)) * ((w + 1) * e) = w * e := by
    calc ((w + 1) * (e * f)) * ((w + 1) * e)
        = (w + 1) * ((e * f) * ((w + 1) * e)) := by rw [mul_assoc]
      _ = (w + 1) * (((e * f) * (w + 1)) * e) := by noncomm_ring
      _ = (w + 1) * (((w + 1) * (e * f)) * e) := by rw [h_ef_w1]
      _ = ((w + 1) * (w + 1)) * ((e * f) * e) := by noncomm_ring
      _ = w * e := by rw [hw1_sq, hefe]
  have hL2 : (w * (f * e)) * ((w + 1) * e) = 0 := by
    calc (w * (f * e)) * ((w + 1) * e)
        = w * ((f * e) * ((w + 1) * e)) := by rw [mul_assoc]
      _ = w * (((f * e) * (w + 1)) * e) := by noncomm_ring
      _ = w * (((w + 1) * (f * e)) * e) := by rw [h_fe_w1]
      _ = (w * (w + 1)) * ((f * e) * e) := by noncomm_ring
      _ = 0 := by rw [hw_w1, h_fe_e, mul_zero]
  have hL : (1 + (w + 1) * (e * f) + w * (f * e)) * (1 + (w + 1) * e) =
      1 + (w + 1) * (e * f) + w * (f * e) + e := by
    calc (1 + (w + 1) * (e * f) + w * (f * e)) * (1 + (w + 1) * e)
        = 1 + (w + 1) * (e * f) + w * (f * e) + (w + 1) * e +
            ((w + 1) * (e * f)) * ((w + 1) * e) +
            (w * (f * e)) * ((w + 1) * e) := by noncomm_ring
      _ = 1 + (w + 1) * (e * f) + w * (f * e) + (w + 1) * e + w * e + 0 := by
          rw [hL1, hL2]
      _ = 1 + (w + 1) * (e * f) + w * (f * e) + e := by
          rw [add_zero, show 1 + (w + 1) * (e * f) + w * (f * e) + (w + 1) * e +
              w * e = 1 + (w + 1) * (e * f) + w * (f * e) + ((w + 1) * e + w * e) by
            abel,
            h_e_sum]
  have hR1 : (w * e) * ((w + 1) * (e * f)) = 0 := by
    calc (w * e) * ((w + 1) * (e * f))
        = w * (e * ((w + 1) * (e * f))) := by rw [mul_assoc]
      _ = w * ((e * (w + 1)) * (e * f)) := by rw [mul_assoc]
      _ = w * (((w + 1) * e) * (e * f)) := by rw [h_e_w1]
      _ = (w * (w + 1)) * ((e * e) * f) := by noncomm_ring
      _ = 0 := by rw [hw_w1, hee, zero_mul, mul_zero]
  have hR2 : (w * e) * (w * (f * e)) = (w + 1) * e := by
    calc (w * e) * (w * (f * e))
        = ((w * e) * w) * (f * e) := by noncomm_ring
      _ = (w * (e * w)) * (f * e) := by noncomm_ring
      _ = (w * (w * e)) * (f * e) := by rw [← hwe]
      _ = ((w * w) * e) * (f * e) := by noncomm_ring
      _ = (w * w) * (e * (f * e)) := by noncomm_ring
      _ = (w + 1) * ((e * f) * e) := by rw [hw2]; noncomm_ring
      _ = (w + 1) * e := by rw [hefe]
  have hR : (1 + w * e) * (1 + (w + 1) * (e * f) + w * (f * e)) =
      1 + (w + 1) * (e * f) + w * (f * e) + e := by
    calc (1 + w * e) * (1 + (w + 1) * (e * f) + w * (f * e))
        = 1 + (w + 1) * (e * f) + w * (f * e) + w * e +
            (w * e) * ((w + 1) * (e * f)) + (w * e) * (w * (f * e)) := by
            noncomm_ring
      _ = 1 + (w + 1) * (e * f) + w * (f * e) + w * e + 0 + (w + 1) * e := by
          rw [hR1, hR2]
      _ = 1 + (w + 1) * (e * f) + w * (f * e) + e := by
          rw [show 1 + (w + 1) * (e * f) + w * (f * e) + w * e + 0 + (w + 1) * e =
              1 + (w + 1) * (e * f) + w * (f * e) + (w * e + (w + 1) * e) by
            abel,
            h_we_sum]
  rw [hL, hR]

private abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

private abbrev E03 : M4 := Matrix.single 0 3 1

private abbrev E30 : M4 := Matrix.single 3 0 1

private abbrev M03 : M4 := 1 + E03

private abbrev M30 : M4 := 1 + E30

private def IsEndRep (hD : DHyp A Aa t D) (c : G → (Fin 4 → ZMod 2))
    (F : AddMonoid.End (VSub hD)) (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ x : VSub hD, x.val ∈ A → (F x).val ∈ A ∧ c (F x).val = M *ᵥ c x.val

private theorem isEndRep_one (hD : DHyp A Aa t D) (c : G → (Fin 4 → ZMod 2)) :
    IsEndRep hD c (1 : AddMonoid.End (VSub hD)) 1 := by
  rw [IsEndRep]
  intro x hx
  exact ⟨hx, by simp⟩

private theorem isEndRep_add (hD : DHyp A Aa t D) {c : G → (Fin 4 → ZMod 2)}
    (hc : IsCoord A c) {F G : AddMonoid.End (VSub hD)}
    {M N : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hF : IsEndRep hD c F M) (hG : IsEndRep hD c G N) :
    IsEndRep hD c (F + G) (M + N) := by
  rw [IsEndRep]
  intro x hx
  have hFx := hF x hx
  have hGx := hG x hx
  refine ⟨?_, ?_⟩
  · change ((F x + G x).val) ∈ A
    rw [AbelianSub.val_add]
    exact A.mul_mem hFx.1 hGx.1
  · change c ((F x + G x).val) = (M + N) *ᵥ c x.val
    rw [AbelianSub.val_add, hc.mul _ hFx.1 _ hGx.1, hFx.2, hGx.2, Matrix.add_mulVec]

private theorem isEndRep_mul (hD : DHyp A Aa t D) {c : G → (Fin 4 → ZMod 2)}
    {F G : AddMonoid.End (VSub hD)} {M N : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hF : IsEndRep hD c F M) (hG : IsEndRep hD c G N) :
    IsEndRep hD c (F * G) (M * N) := by
  rw [IsEndRep]
  intro x hx
  have hGx := hG x hx
  have hFGx := hF (G x) hGx.1
  refine ⟨?_, ?_⟩
  · change ((F (G x)).val) ∈ A
    exact hFGx.1
  · change c ((F (G x)).val) = (M * N) *ᵥ c x.val
    rw [hFGx.2, hGx.2, Matrix.mulVec_mulVec]

private theorem isEndRep_vConj (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {c : G → (Fin 4 → ZMod 2)}
    {n : G} (hn : n ∈ L ⊓ normalizer (A : Set G))
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : IsRep A c n M) :
    IsEndRep hD c (vConj hD n) M := by
  rw [IsEndRep]
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) := by
    have hnNL : n ∈ normInL L A :=
      mem_normInL.2 ⟨hn.1, fun x hx => (mem_normalizer_iff.1 hn.2 x).1 hx⟩
    exact H.normalizer_le_normalizer_omega1 W W2 hD
      (H.mem_normalizer_W5_of_mem_normInL W W2 hD hnNL)
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [val_vConj_apply hD hnV x]
    exact (mem_normalizer_iff.1 hn.2 x.val).1 hx
  · rw [val_vConj_apply hD hnV x]
    exact hM x.val hx

private theorem end_eq_of_isEndRep (hD : DHyp A Aa t D) {c : G → (Fin 4 → ZMod 2)}
    (hc : IsCoord A c) {w : AddMonoid.End (VSub hD)}
    (hlin : ∀ f f' : AddMonoid.End (VSub hD), f * w = w * f → f' * w = w * f' →
      (∀ x : VSub hD, x.val ∈ A → f x = f' x) → f = f')
    {F G : AddMonoid.End (VSub hD)} {M : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hF : IsEndRep hD c F M) (hG : IsEndRep hD c G M)
    (hFw : F * w = w * F) (hGw : G * w = w * G) : F = G := by
  refine hlin F G hFw hGw fun x hx => ?_
  have h1 := hF x hx
  have h2 := hG x hx
  exact AbelianSub.ext (hc.inj _ h1.1 _ h2.1 (by rw [h1.2, h2.2]))

private theorem commute_w_mul {X : Type*} [AddCommMonoid X] {w F G : AddMonoid.End X}
    (hF : F * w = w * F) (hG : G * w = w * G) : (F * G) * w = w * (F * G) := by
  rw [mul_assoc, hG, ← mul_assoc, hF, mul_assoc]

private theorem commute_w_one {X : Type*} [AddCommMonoid X] {w : AddMonoid.End X} :
    (1 : AddMonoid.End X) * w = w * 1 := by rw [mul_one, one_mul]

private theorem mem_normalizer_of_conj_mem {n : G}
    (h : ∀ a ∈ A, n * a * n⁻¹ ∈ A) : n ∈ normalizer (A : Set G) := by
  have hmaple : A.map (MulAut.conj n).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using h a ha
  have hcard : Nat.card (A.map (MulAut.conj n).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2
    (Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm))

private theorem Hn_le_normalizer_Q (hQ : QHyp L A D t Q) :
    L ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G) := by
  intro n hn
  refine mem_normalizer_iff.2 fun q => ⟨fun hq => hQ.conj_mem n hn q hq, fun hq => ?_⟩
  have := hQ.conj_mem n⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hn) (n * q * n⁻¹) hq
  simpa [mul_assoc] using this

private theorem Hn_le_normalizer_omega1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ L ⊓ normalizer (A : Set G)) :
    n ∈ normalizer (omega1 D hD.comm : Set G) := by
  have hnNL : n ∈ normInL L A :=
    mem_normInL.2 ⟨hn.1, fun x hx => (mem_normalizer_iff.1 hn.2 x).1 hx⟩
  exact H.normalizer_le_normalizer_omega1 W W2 hD
    (H.mem_normalizer_W5_of_mem_normInL W W2 hD hnNL)

private def f4N (hD : DHyp A Aa t D) (Q : Subgroup G)
    (w Y : AddMonoid.End (VSub hD)) : Subgroup G where
  carrier := {n | n ∈ normalizer (Q : Set G) ⊓ wComm hD w ∧
    vConj hD n * Y = Y * vConj hD n}
  one_mem' := by
    refine ⟨(normalizer (Q : Set G) ⊓ wComm hD w).one_mem, ?_⟩
    rw [vConj_one, one_mul, mul_one]
  mul_mem' := by
    rintro n m ⟨hn, hYn⟩ ⟨hm, hYm⟩
    refine ⟨(normalizer (Q : Set G) ⊓ wComm hD w).mul_mem hn hm, ?_⟩
    have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) := hn.2.1
    have hmV : m ∈ normalizer (omega1 D hD.comm : Set G) := hm.2.1
    rw [vConj_mul hD hnV hmV]
    calc (vConj hD n * vConj hD m) * Y
        = vConj hD n * (vConj hD m * Y) := by rw [mul_assoc]
      _ = vConj hD n * (Y * vConj hD m) := by rw [hYm]
      _ = (vConj hD n * Y) * vConj hD m := by rw [mul_assoc]
      _ = (Y * vConj hD n) * vConj hD m := by rw [hYn]
      _ = Y * (vConj hD n * vConj hD m) := by rw [mul_assoc]
  inv_mem' := by
    rintro n ⟨hn, hYn⟩
    refine ⟨(normalizer (Q : Set G) ⊓ wComm hD w).inv_mem hn, ?_⟩
    have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) := hn.2.1
    have hleft : vConj hD n⁻¹ * vConj hD n = 1 := vConj_inv_mul hD hnV
    have hright : vConj hD n * vConj hD n⁻¹ = 1 := vConj_mul_inv hD hnV
    calc vConj hD n⁻¹ * Y
        = vConj hD n⁻¹ * Y * (vConj hD n * vConj hD n⁻¹) := by rw [hright, mul_one]
      _ = vConj hD n⁻¹ * (Y * vConj hD n) * vConj hD n⁻¹ := by noncomm_ring
      _ = vConj hD n⁻¹ * (vConj hD n * Y) * vConj hD n⁻¹ := by rw [← hYn]
      _ = (vConj hD n⁻¹ * vConj hD n) * Y * vConj hD n⁻¹ := by noncomm_ring
      _ = Y * vConj hD n⁻¹ := by rw [hleft, one_mul]

private theorem f4N_le_normalizer_Q (hD : DHyp A Aa t D) (Q : Subgroup G)
    {w Y : AddMonoid.End (VSub hD)} :
    f4N hD Q w Y ≤ normalizer (Q : Set G) :=
  fun _ hn => hn.1.1

private theorem f4N_le_wComm (hD : DHyp A Aa t D) (Q : Subgroup G)
    {w Y : AddMonoid.End (VSub hD)} :
    f4N hD Q w Y ≤ wComm hD w :=
  fun _ hn => hn.1.2

private theorem phiQ_conj_eq_of_mem_wComm (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {w : AddMonoid.End (VSub hD)}
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {n c : G} (hnQ : n ∈ normalizer (Q : Set G)) (hnw : n ∈ wComm hD w)
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    phiQ hD Q (n * c * n⁻¹) = phiQ hD Q c := by
  have hcommPhi : vConj hD n * phiQ hD Q c = phiQ hD Q c * vConj hD n := by
    rcases hΦ c hc with h | h | h | h
    · rw [h, mul_zero, zero_mul]
    · rw [h, mul_one, one_mul]
    · rw [h]; exact hnw.2
    · rw [h, mul_add, mul_one, add_mul, one_mul, hnw.2]
  have hconj := QHyp.phiQ_conj hD hQ hq4 hsq hnQ hc
  calc phiQ hD Q (n * c * n⁻¹)
      = phiQ hD Q (n * c * n⁻¹) * 1 := (mul_one _).symm
    _ = phiQ hD Q (n * c * n⁻¹) * (vConj hD n * vConj hD n⁻¹) := by
          rw [vConj_mul_inv hD hnw.1]
    _ = (phiQ hD Q (n * c * n⁻¹) * vConj hD n) * vConj hD n⁻¹ := by noncomm_ring
    _ = (vConj hD n * phiQ hD Q c) * vConj hD n⁻¹ := by rw [hconj]
    _ = (phiQ hD Q c * vConj hD n) * vConj hD n⁻¹ := by rw [hcommPhi]
    _ = phiQ hD Q c * (vConj hD n * vConj hD n⁻¹) := by rw [mul_assoc]
    _ = phiQ hD Q c := by rw [vConj_mul_inv hD hnw.1, mul_one]

private theorem phiQ_one_eq_zero (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v) :
    phiQ hD Q (1 : G) = 0 :=
  (QHyp.phiQ_eq_zero_iff hD hQ hq4 hsq
    (show (1 : G) ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G) from
      ⟨one_mem _, one_mem _⟩)).2 (by simp)

private noncomputable def f4Kappa (hD : DHyp A Aa t D) (Q : Subgroup G) (y n : G) :
    AddMonoid.End (VSub hD) :=
  phiQ hD Q (n * y * n⁻¹ * y⁻¹)

private theorem commutator_mem_NV_of_mem_f4N (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (hQ : QHyp L A D t Q) {w Y : AddMonoid.End (VSub hD)} {y : G}
    (hyHn : y ∈ L ⊓ normalizer (A : Set G)) (hY : Y = vConj hD y) {n : G}
    (hn : n ∈ f4N hD Q w Y) :
    n * y * n⁻¹ * y⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) := by
  have hnQ : n ∈ normalizer (Q : Set G) := hn.1.1
  have hnw : n ∈ wComm hD w := hn.1.2
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) := hnw.1
  have hyQ : y ∈ normalizer (Q : Set G) := Hn_le_normalizer_Q hQ hyHn
  have hyV : y ∈ normalizer (omega1 D hD.comm : Set G) :=
    Hn_le_normalizer_omega1 H W W2 hD hyHn
  have hcommQ : n * y * n⁻¹ * y⁻¹ ∈ normalizer (Q : Set G) :=
    (normalizer (Q : Set G)).mul_mem
      ((normalizer (Q : Set G)).mul_mem
        ((normalizer (Q : Set G)).mul_mem hnQ hyQ)
        ((normalizer (Q : Set G)).inv_mem hnQ))
      ((normalizer (Q : Set G)).inv_mem hyQ)
  have hcommV : n * y * n⁻¹ * y⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).mul_mem
      ((normalizer (omega1 D hD.comm : Set G)).mul_mem
        ((normalizer (omega1 D hD.comm : Set G)).mul_mem hnV hyV)
        ((normalizer (omega1 D hD.comm : Set G)).inv_mem hnV))
      ((normalizer (omega1 D hD.comm : Set G)).inv_mem hyV)
  have hnV' : n⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem hnV
  have hyV' : y⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem hyV
  have hcommV' : n⁻¹ * y⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).mul_mem hnV' hyV'
  have hvconj : vConj hD (n * y * n⁻¹ * y⁻¹) = 1 := by
    have hprod : n * y * n⁻¹ * y⁻¹ = (n * y) * (n⁻¹ * y⁻¹) := by group
    rw [hprod, vConj_mul hD ((normalizer _).mul_mem hnV hyV) hcommV',
      vConj_mul hD hnV hyV, vConj_mul hD hnV' hyV']
    have hAB : vConj hD n * vConj hD y = vConj hD y * vConj hD n := by
      rw [← hY]
      exact hn.2
    have hAC : vConj hD n * vConj hD n⁻¹ = 1 := vConj_mul_inv hD hnV
    have hBD : vConj hD y * vConj hD y⁻¹ = 1 := vConj_mul_inv hD hyV
    calc vConj hD n * vConj hD y * vConj hD n⁻¹ * vConj hD y⁻¹
        = vConj hD y * (vConj hD n * vConj hD n⁻¹) * vConj hD y⁻¹ := by
            rw [hAB]; noncomm_ring
      _ = vConj hD y * 1 * vConj hD y⁻¹ := by rw [hAC]
      _ = 1 := by rw [mul_one, hBD]
  refine ⟨hcommQ, mem_centralizer_iff.2 fun v hv => ?_⟩
  have hval := val_vConj_apply hD hcommV (AbelianSub.mk v hv)
  rw [hvconj] at hval
  simp only [AbelianSub.val_mk] at hval
  change v = (n * y * n⁻¹ * y⁻¹) * v * (n * y * n⁻¹ * y⁻¹)⁻¹ at hval
  calc v * (n * y * n⁻¹ * y⁻¹)
      = ((n * y * n⁻¹ * y⁻¹) * v * (n * y * n⁻¹ * y⁻¹)⁻¹) *
          (n * y * n⁻¹ * y⁻¹) := by rw [hval.symm]
    _ = (n * y * n⁻¹ * y⁻¹) * v := by group

private theorem conj_mem_NV_of_mem_f4N (hD : DHyp A Aa t D)
    {w Y : AddMonoid.End (VSub hD)} {n c : G} (hn : n ∈ f4N hD Q w Y)
    (hc : c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    n * c * n⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) := by
  have hnQ : n ∈ normalizer (Q : Set G) := hn.1.1
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) := hn.1.2.1
  refine ⟨?_, ?_⟩
  · exact (normalizer (Q : Set G)).mul_mem
      ((normalizer (Q : Set G)).mul_mem hnQ hc.1)
      ((normalizer (Q : Set G)).inv_mem hnQ)
  · refine mem_centralizer_iff.2 fun v hv => ?_
    have hv' : n⁻¹ * v * n ∈ omega1 D hD.comm := by
      simpa using (mem_normalizer_iff.1 ((normalizer _).inv_mem hnV) v).1 hv
    have hcv : (n⁻¹ * v * n) * c = c * (n⁻¹ * v * n) :=
      mem_centralizer_iff.1 hc.2 _ hv'
    calc v * (n * c * n⁻¹) = n * ((n⁻¹ * v * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * v * n)) * n⁻¹ := by rw [hcv]
      _ = (n * c * n⁻¹) * v := by group

private theorem f4Kappa_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {w Y : AddMonoid.End (VSub hD)}
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {y : G} (hyHn : y ∈ L ⊓ normalizer (A : Set G)) (hY : Y = vConj hD y)
    {n m : G} (hn : n ∈ f4N hD Q w Y) (hm : m ∈ f4N hD Q w Y) :
    f4Kappa hD Q y (n * m) = f4Kappa hD Q y n + f4Kappa hD Q y m := by
  have hcn : n * y * n⁻¹ * y⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) :=
    commutator_mem_NV_of_mem_f4N H W W2 hD hQ hyHn hY hn
  have hcm : m * y * m⁻¹ * y⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) :=
    commutator_mem_NV_of_mem_f4N H W W2 hD hQ hyHn hY hm
  have hconjNV : n * (m * y * m⁻¹ * y⁻¹) * n⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) :=
    conj_mem_NV_of_mem_f4N hD hn hcm
  have hgroup : (n * m) * y * (n * m)⁻¹ * y⁻¹ =
      (n * (m * y * m⁻¹ * y⁻¹) * n⁻¹) * (n * y * n⁻¹ * y⁻¹) := by group
  unfold f4Kappa
  rw [hgroup, QHyp.phiQ_mul hD hQ hq4 hsq hconjNV hcn,
    phiQ_conj_eq_of_mem_wComm hD hQ hq4 hsq hΦ hn.1.1 hn.1.2 hcm]
  exact add_comm _ _

private theorem f4Kappa_one (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    (y : G) : f4Kappa hD Q y 1 = 0 := by
  unfold f4Kappa
  simpa using phiQ_one_eq_zero hD hQ hq4 hsq

private theorem f4Kappa_inv (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {w Y : AddMonoid.End (VSub hD)}
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {y : G} (hyHn : y ∈ L ⊓ normalizer (A : Set G)) (hY : Y = vConj hD y)
    {n : G} (hn : n ∈ f4N hD Q w Y) :
    f4Kappa hD Q y n⁻¹ = f4Kappa hD Q y n := by
  have hinv : n⁻¹ ∈ f4N hD Q w Y := (f4N hD Q w Y).inv_mem hn
  have h := f4Kappa_mul H W W2 hD hQ hq4 hsq hΦ hyHn hY hinv hn
  rw [inv_mul_cancel, f4Kappa_one hD hQ hq4 hsq y] at h
  calc f4Kappa hD Q y n⁻¹ = -(f4Kappa hD Q y n) := eq_neg_of_add_eq_zero_left h.symm
    _ = f4Kappa hD Q y n := neg_eq_of_add_eq_zero_right (VSub.add_self hD (f4Kappa hD Q y n))

private theorem f4Kappa_commutator (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {w Y : AddMonoid.End (VSub hD)}
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {y : G} (hyHn : y ∈ L ⊓ normalizer (A : Set G)) (hY : Y = vConj hD y)
    {n m : G} (hn : n ∈ f4N hD Q w Y) (hm : m ∈ f4N hD Q w Y) :
    f4Kappa hD Q y (n * m * n⁻¹ * m⁻¹) = 0 := by
  have hnm : n * m ∈ f4N hD Q w Y := (f4N hD Q w Y).mul_mem hn hm
  have hinvm : n⁻¹ * m⁻¹ ∈ f4N hD Q w Y :=
    (f4N hD Q w Y).mul_mem ((f4N hD Q w Y).inv_mem hn) ((f4N hD Q w Y).inv_mem hm)
  have h1 := f4Kappa_mul H W W2 hD hQ hq4 hsq hΦ hyHn hY hnm hinvm
  have h2 := f4Kappa_mul H W W2 hD hQ hq4 hsq hΦ hyHn hY hn hm
  have h3 := f4Kappa_inv H W W2 hD hQ hq4 hsq hΦ hyHn hY hn
  have h4 := f4Kappa_inv H W W2 hD hQ hq4 hsq hΦ hyHn hY hm
  have h5 := f4Kappa_mul H W W2 hD hQ hq4 hsq hΦ hyHn hY
    ((f4N hD Q w Y).inv_mem hn) ((f4N hD Q w Y).inv_mem hm)
  rw [show n * m * n⁻¹ * m⁻¹ = (n * m) * (n⁻¹ * m⁻¹) by group, h1, h2, h5, h3, h4]
  rw [show (f4Kappa hD Q y n + f4Kappa hD Q y m) +
      (f4Kappa hD Q y n + f4Kappa hD Q y m) =
      (f4Kappa hD Q y n + f4Kappa hD Q y n) +
        (f4Kappa hD Q y m + f4Kappa hD Q y m) by abel,
    VSub.add_self, VSub.add_self, add_zero]

private theorem f4Kappa_eq_zero_of_mem_NV (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1) (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {w Y : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    {y : G} (hyHn : y ∈ L ⊓ normalizer (A : Set G))
    {n : G} (hn : n ∈ f4N hD Q w Y)
    (hnNV : n ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G)) :
    f4Kappa hD Q y n = 0 := by
  have hnQ : n ∈ normalizer (Q : Set G) := hnNV.1
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) := hn.1.2.1
  have hyQ : y ∈ normalizer (Q : Set G) := Hn_le_normalizer_Q hQ hyHn
  have hyV : y ∈ normalizer (omega1 D hD.comm : Set G) :=
    Hn_le_normalizer_omega1 H W W2 hD hyHn
  have hyw : y ∈ wComm hD w := Hn_le_wComm H W W2 hD hwH hyHn
  have hninvNV : n⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) :=
    ⟨(normalizer (Q : Set G)).inv_mem hnQ,
      (centralizer (omega1 D hD.comm : Set G)).inv_mem hnNV.2⟩
  have hynNV : y * n⁻¹ * y⁻¹ ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) := by
    refine ⟨(normalizer (Q : Set G)).mul_mem
        ((normalizer (Q : Set G)).mul_mem hyQ hninvNV.1)
        ((normalizer (Q : Set G)).inv_mem hyQ), ?_⟩
    refine mem_centralizer_iff.2 fun v hv => ?_
    have hv' : y⁻¹ * v * y ∈ omega1 D hD.comm := by
      simpa using (mem_normalizer_iff.1 ((normalizer _).inv_mem hyV) v).1 hv
    have hcv : (y⁻¹ * v * y) * n⁻¹ = n⁻¹ * (y⁻¹ * v * y) :=
      mem_centralizer_iff.1 hninvNV.2 _ hv'
    calc v * (y * n⁻¹ * y⁻¹) = y * ((y⁻¹ * v * y) * n⁻¹) * y⁻¹ := by group
      _ = y * (n⁻¹ * (y⁻¹ * v * y)) * y⁻¹ := by rw [hcv]
      _ = (y * n⁻¹ * y⁻¹) * v := by group
  have hgroup : n * y * n⁻¹ * y⁻¹ = n * (y * n⁻¹ * y⁻¹) := by group
  have hphi := QHyp.phiQ_mul hD hQ hq4 hsq hnNV hynNV
  have hconj := phiQ_conj_eq_of_mem_wComm hD hQ hq4 hsq hΦ hyQ hyw hninvNV
  have hsum : phiQ hD Q n + phiQ hD Q n⁻¹ = 0 := by
    have h := QHyp.phiQ_mul hD hQ hq4 hsq hnNV hninvNV
    rw [mul_inv_cancel, phiQ_one_eq_zero hD hQ hq4 hsq] at h
    exact h.symm
  unfold f4Kappa
  rw [hgroup, hphi, hconj, hsum]

private theorem vConj_comm_of_isRep_comm (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {c : G → (Fin 4 → ZMod 2)}
    (hc : IsCoord A c) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hlin : ∀ f f' : AddMonoid.End (VSub hD), f * w = w * f → f' * w = w * f' →
      (∀ x : VSub hD, x.val ∈ A → f x = f' x) → f = f')
    {n m : G} (hn : n ∈ L ⊓ normalizer (A : Set G))
    (hm : m ∈ L ⊓ normalizer (A : Set G))
    {M N : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : IsRep A c n M) (hN : IsRep A c m N)
    (hMN : M * N = N * M) :
    vConj hD n * vConj hD m = vConj hD m * vConj hD n := by
  have hFn := isEndRep_vConj H W W2 hD hn hM
  have hFm := isEndRep_vConj H W W2 hD hm hN
  have hF := isEndRep_mul hD hFn hFm
  have hG := isEndRep_mul hD hFm hFn
  rw [hMN] at hF
  exact end_eq_of_isEndRep hD hc hlin hF hG
    (commute_w_mul (hwH n hn) (hwH m hm))
    (commute_w_mul (hwH m hm) (hwH n hn))

private theorem vConj_mul_self_eq_one_of_isRep (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {c : G → (Fin 4 → ZMod 2)}
    (hc : IsCoord A c) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hlin : ∀ f f' : AddMonoid.End (VSub hD), f * w = w * f → f' * w = w * f' →
      (∀ x : VSub hD, x.val ∈ A → f x = f' x) → f = f')
    {n : G} (hn : n ∈ L ⊓ normalizer (A : Set G))
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : IsRep A c n M) (hMM : M * M = 1) :
    vConj hD n * vConj hD n = 1 := by
  have hFn := isEndRep_vConj H W W2 hD hn hM
  have hF := isEndRep_mul hD hFn hFn
  rw [hMM] at hF
  exact end_eq_of_isEndRep hD hc hlin hF (isEndRep_one hD c)
    (commute_w_mul (hwH n hn) (hwH n hn)) commute_w_one

theorem ThCyc.false_of_F4 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (F : SylowFacts L S B Aa) (hD : DHyp A Aa t D)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {Q : Subgroup G} (hQ : QHyp L A D t Q)
    (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v)
    {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hw2 : w * w = w + 1)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    (hβ : phiQ hD Q b = 1) {c : G → (Fin 4 → ZMod 2)} (hc : IsCoord A c)
    (hS : ∀ s ∈ S, ∃ g ∈ CFSG.Quasithin.FFC.UT 4,
      IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : ∀ g ∈ CFSG.Quasithin.FFC.UT 4,
      ∃ s ∈ S, IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hlin : ∀ f f' : AddMonoid.End (VSub hD), f * w = w * f → f' * w = w * f' →
      (∀ x : VSub hD, x.val ∈ A → f x = f' x) → f = f')
    {ζ : G} (hζS : ζ ∈ S) (hζM : IsRep A c ζ (1 + Matrix.single 0 3 1))
    (hx : ∃ x ∈ normalizer (Q : Set G) ⊓ wComm hD w,
      vConj hD x = 1 + w * (vConj hD ζ + 1)) : False := by
  classical
  obtain ⟨y, hyS, hyM⟩ :=
    ThLocalIn.exists_mem_S_isRep_of_unitriangular (A := A) (c := c) (i := 1) (j := 2)
      hsurj (by decide)
  have hM30inj : Function.Injective (M30 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec := by
    intro u v huv
    have h1 : (M30 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          ((M30 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ u) =
        (M30 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          ((M30 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) :=
      congrArg (fun x => (M30 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) huv
    simpa [Matrix.mulVec_mulVec, show (M30 : Matrix (Fin 4) (Fin 4) (ZMod 2)) * M30 = 1 by decide]
      using h1
  obtain ⟨ŷ, hŷL, hŷA, hŷM⟩ := hc.exists_lift (L := L) W.surj (M := M30) hM30inj
  obtain ⟨x, hxmem, hxv⟩ := hx
  have hxQ : x ∈ normalizer (Q : Set G) := hxmem.1
  have hxw : x ∈ wComm hD w := hxmem.2
  have hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A := fun a ha => W.conj_mem_A_of_mem_S hyS ha
  have hζA : ∀ a ∈ A, ζ * a * ζ⁻¹ ∈ A := fun a ha => W.conj_mem_A_of_mem_S hζS ha
  have hyHn : y ∈ L ⊓ normalizer (A : Set G) := ⟨W.S_le hyS, mem_normalizer_of_conj_mem hyA⟩
  have hζHn : ζ ∈ L ⊓ normalizer (A : Set G) :=
    ⟨W.S_le hζS, mem_normalizer_of_conj_mem hζA⟩
  have hŷHn : ŷ ∈ L ⊓ normalizer (A : Set G) := ⟨hŷL, mem_normalizer_of_conj_mem hŷA⟩
  let Y : AddMonoid.End (VSub hD) := vConj hD y
  let e : AddMonoid.End (VSub hD) := vConj hD ζ + 1
  let f : AddMonoid.End (VSub hD) := vConj hD ŷ + 1
  have hY : Y = vConj hD y := rfl
  have hζw : vConj hD ζ * w = w * vConj hD ζ := hwH ζ hζHn
  have hŷw : vConj hD ŷ * w = w * vConj hD ŷ := hwH ŷ hŷHn
  have hyw : vConj hD y * w = w * vConj hD y := hwH y hyHn
  have hew : e * w = w * e := by
    dsimp only [e]
    rw [add_mul, one_mul, mul_add, mul_one, hζw]
  have hfw : f * w = w * f := by
    dsimp only [f]
    rw [add_mul, one_mul, mul_add, mul_one, hŷw]
  have hζsq : vConj hD ζ * vConj hD ζ = 1 :=
    vConj_mul_self_eq_one_of_isRep H W W2 hD hc hwH hlin hζHn hζM (by decide)
  have hŷsq : vConj hD ŷ * vConj hD ŷ = 1 :=
    vConj_mul_self_eq_one_of_isRep H W W2 hD hc hwH hlin hŷHn hŷM (by decide)
  have hee : e * e = 0 := by
    dsimp only [e]
    calc (vConj hD ζ + 1) * (vConj hD ζ + 1)
        = 1 + (vConj hD ζ + vConj hD ζ) + 1 := by
            rw [show (vConj hD ζ + 1) * (vConj hD ζ + 1) =
              vConj hD ζ * vConj hD ζ + vConj hD ζ + vConj hD ζ + 1 by noncomm_ring,
              hζsq]
            abel
      _ = 1 + 0 + 1 := by rw [VSub.add_self]
      _ = 0 := by rw [add_zero, VSub.add_self]
  have hff : f * f = 0 := by
    dsimp only [f]
    calc (vConj hD ŷ + 1) * (vConj hD ŷ + 1)
        = 1 + (vConj hD ŷ + vConj hD ŷ) + 1 := by
            rw [show (vConj hD ŷ + 1) * (vConj hD ŷ + 1) =
              vConj hD ŷ * vConj hD ŷ + vConj hD ŷ + vConj hD ŷ + 1 by noncomm_ring,
              hŷsq]
            abel
      _ = 1 + 0 + 1 := by rw [VSub.add_self]
      _ = 0 := by rw [add_zero, VSub.add_self]
  have heRep : IsEndRep hD c e E03 := by
    dsimp only [e]
    have h := isEndRep_add hD hc (isEndRep_vConj H W W2 hD hζHn hζM)
      (isEndRep_one hD c)
    rwa [show (M03 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + 1 = E03 by decide] at h
  have hfRep : IsEndRep hD c f E30 := by
    dsimp only [f]
    have h := isEndRep_add hD hc (isEndRep_vConj H W W2 hD hŷHn hŷM)
      (isEndRep_one hD c)
    rwa [show (M30 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + 1 = E30 by decide] at h
  have hefe : e * f * e = e := by
    have hEFE : IsEndRep hD c ((e * f) * e) E03 := by
      have h := isEndRep_mul hD (isEndRep_mul hD heRep hfRep) heRep
      rwa [show (E03 * E30) * E03 = E03 by decide] at h
    exact end_eq_of_isEndRep hD hc hlin hEFE heRep
      (commute_w_mul (commute_w_mul hew hfw) hew) hew
  have hfef : f * e * f = f := by
    have hFEF : IsEndRep hD c ((f * e) * f) E30 := by
      have h := isEndRep_mul hD (isEndRep_mul hD hfRep heRep) hfRep
      rwa [show (E30 * E03) * E30 = E30 by decide] at h
    exact end_eq_of_isEndRep hD hc hlin hFEF hfRep
      (commute_w_mul (commute_w_mul hfw hew) hfw) hfw
  have hζY : vConj hD ζ * vConj hD y = vConj hD y * vConj hD ζ :=
    vConj_comm_of_isRep_comm H W W2 hD hc hwH hlin hζHn hyHn hζM hyM (by decide)
  have hŷY : vConj hD ŷ * vConj hD y = vConj hD y * vConj hD ŷ :=
    vConj_comm_of_isRep_comm H W W2 hD hc hwH hlin hŷHn hyHn hŷM hyM (by decide)
  have heY : e * Y = Y * e := by
    dsimp only [e, Y]
    rw [add_mul, one_mul, mul_add, mul_one, hζY]
  have hfY : f * Y = Y * f := by
    dsimp only [f, Y]
    rw [add_mul, one_mul, mul_add, mul_one, hŷY]
  have hζf4 : ζ ∈ f4N hD Q w Y := by
    refine ⟨⟨Hn_le_normalizer_Q hQ hζHn, Hn_le_wComm H W W2 hD hwH hζHn⟩, ?_⟩
    dsimp only [Y]
    exact hζY
  have hŷf4 : ŷ ∈ f4N hD Q w Y := by
    refine ⟨⟨Hn_le_normalizer_Q hQ hŷHn, Hn_le_wComm H W W2 hD hwH hŷHn⟩, ?_⟩
    dsimp only [Y]
    exact hŷY
  have hyf4 : y ∈ f4N hD Q w Y := by
    refine ⟨⟨Hn_le_normalizer_Q hQ hyHn, Hn_le_wComm H W W2 hD hwH hyHn⟩, ?_⟩
    dsimp only [Y]
  have hxf4 : x ∈ f4N hD Q w Y := by
    refine ⟨⟨hxQ, hxw⟩, ?_⟩
    dsimp only [Y]
    rw [hxv]
    have heY' : e * vConj hD y = vConj hD y * e := by simpa only [Y] using heY
    calc (1 + w * e) * vConj hD y = vConj hD y + (w * e) * vConj hD y := by
          rw [add_mul, one_mul]
      _ = vConj hD y + w * (e * vConj hD y) := by rw [mul_assoc]
      _ = vConj hD y + w * (vConj hD y * e) := by rw [heY']
      _ = vConj hD y + (w * vConj hD y) * e := by rw [mul_assoc]
      _ = vConj hD y + (vConj hD y * w) * e := by rw [← hyw]
      _ = vConj hD y * (1 + w * e) := by noncomm_ring
  let hhat : G := ŷ * ζ * x * ŷ * x * ŷ
  let k : G := x * ζ
  have hhhatf4 : hhat ∈ f4N hD Q w Y := by
    dsimp only [hhat]
    exact (f4N hD Q w Y).mul_mem
      ((f4N hD Q w Y).mul_mem
        ((f4N hD Q w Y).mul_mem
          ((f4N hD Q w Y).mul_mem ((f4N hD Q w Y).mul_mem hŷf4 hζf4) hxf4) hŷf4) hxf4) hŷf4
  have hkf4 : k ∈ f4N hD Q w Y := by
    dsimp only [k]
    exact (f4N hD Q w Y).mul_mem hxf4 hζf4
  let VN : Subgroup G := normalizer (omega1 D hD.comm : Set G)
  have hζV : ζ ∈ VN := Hn_le_normalizer_omega1 H W W2 hD hζHn
  have hŷV : ŷ ∈ VN := Hn_le_normalizer_omega1 H W W2 hD hŷHn
  have hyV : y ∈ VN := Hn_le_normalizer_omega1 H W W2 hD hyHn
  have hxV : x ∈ VN := hxw.1
  have h2V : ŷ * ζ ∈ VN := VN.mul_mem hŷV hζV
  have h3V : ŷ * ζ * x ∈ VN := VN.mul_mem h2V hxV
  have h4V : ŷ * ζ * x * ŷ ∈ VN := VN.mul_mem h3V hŷV
  have h5V : ŷ * ζ * x * ŷ * x ∈ VN := VN.mul_mem h4V hxV
  have hvconj_hhat : vConj hD hhat =
      vConj hD ŷ * vConj hD ζ * vConj hD x * vConj hD ŷ * vConj hD x * vConj hD ŷ := by
    dsimp only [hhat]
    calc vConj hD (ŷ * ζ * x * ŷ * x * ŷ)
        = vConj hD (ŷ * ζ * x * ŷ * x) * vConj hD ŷ := by
            rw [vConj_mul hD h5V hŷV]
      _ = (vConj hD (ŷ * ζ * x * ŷ) * vConj hD x) * vConj hD ŷ := by
            rw [vConj_mul hD h4V hxV]
      _ = ((vConj hD (ŷ * ζ * x) * vConj hD ŷ) * vConj hD x) * vConj hD ŷ := by
            rw [vConj_mul hD h3V hŷV]
      _ = (((vConj hD (ŷ * ζ) * vConj hD x) * vConj hD ŷ) * vConj hD x) * vConj hD ŷ := by
            rw [vConj_mul hD h2V hxV]
      _ = ((((vConj hD ŷ * vConj hD ζ) * vConj hD x) * vConj hD ŷ) * vConj hD x) *
            vConj hD ŷ := by
            rw [vConj_mul hD hŷV hζV]
  have hone_e : (1 : AddMonoid.End (VSub hD)) + e = vConj hD ζ := by
    dsimp only [e]
    rw [show (1 : AddMonoid.End (VSub hD)) + (vConj hD ζ + 1) =
      vConj hD ζ + ((1 : AddMonoid.End (VSub hD)) + 1) by abel,
      VSub.add_self, add_zero]
  have hone_f : (1 : AddMonoid.End (VSub hD)) + f = vConj hD ŷ := by
    dsimp only [f]
    rw [show (1 : AddMonoid.End (VSub hD)) + (vConj hD ŷ + 1) =
      vConj hD ŷ + ((1 : AddMonoid.End (VSub hD)) + 1) by abel,
      VSub.add_self, add_zero]
  have hvconj_hhat' : vConj hD hhat =
      (1 + f) * (1 + e) * (1 + w * e) * (1 + f) * (1 + w * e) * (1 + f) := by
    rw [hvconj_hhat, ← hone_f, ← hone_e, hxv]
  have hX : vConj hD hhat = 1 + (w + 1) * (e * f) + w * (f * e) := by
    rw [hvconj_hhat']
    exact sl2F4_word_eq (R := AddMonoid.End (VSub hD)) (VSub.add_self hD) hew.symm hfw.symm hw2
      hee hff hefe hfef
  have hvconj_k : vConj hD k = 1 + (w + 1) * e := by
    dsimp only [k]
    rw [vConj_mul hD hxV hζV]
    have hxv' : vConj hD x = 1 + w * e := by
      rw [hxv]
    rw [hxv']
    have hζv : vConj hD ζ = 1 + e := hone_e.symm
    rw [hζv]
    calc (1 + w * e) * (1 + e)
        = 1 + e + w * e + w * (e * e) := by noncomm_ring
      _ = 1 + e + w * e := by rw [hee, mul_zero, add_zero]
      _ = 1 + (w + 1) * e := by noncomm_ring
  have hw1sq : (w + 1) * (w + 1) = w := by
    calc (w + 1) * (w + 1) = w * w + w + w + 1 := by noncomm_ring
      _ = (w + 1) + (w + w) + 1 := by rw [hw2]; abel
      _ = (w + 1) + 0 + 1 := by rw [VSub.add_self]
      _ = w + 1 + 1 := by abel
      _ = w := by rw [add_assoc, VSub.add_self, add_zero]
  have hew1 : e * (w + 1) = (w + 1) * e := by
    calc e * (w + 1) = e * w + e := by rw [mul_add, mul_one]
      _ = w * e + e := by rw [hew]
      _ = (w + 1) * e := by rw [add_mul, one_mul]
  have hk0sq : (1 + (w + 1) * e) * (1 + (w + 1) * e) = 1 := by
    calc (1 + (w + 1) * e) * (1 + (w + 1) * e)
        = 1 + ((w + 1) * e + (w + 1) * e) + ((w + 1) * e) * ((w + 1) * e) := by
            noncomm_ring
      _ = 1 + 0 + ((w + 1) * e) * ((w + 1) * e) := by rw [VSub.add_self]
      _ = 1 + 0 + ((w + 1) * (w + 1)) * (e * e) := by
            rw [show ((w + 1) * e) * ((w + 1) * e) = ((w + 1) * (w + 1)) * (e * e) by
              calc ((w + 1) * e) * ((w + 1) * e)
                  = (w + 1) * (e * ((w + 1) * e)) := by noncomm_ring
                _ = (w + 1) * (((w + 1) * e) * e) := by
                    rw [← mul_assoc e (w + 1) e, hew1]
                _ = ((w + 1) * (w + 1)) * (e * e) := by noncomm_ring]
      _ = 1 := by
            rw [hw1sq, hee, mul_zero]
            simp
  have hfinish : (1 + w * e) * (1 + (w + 1) * e) = 1 + e := by
    calc (1 + w * e) * (1 + (w + 1) * e)
        = 1 + (w + 1) * e + w * e + (w * e) * ((w + 1) * e) := by noncomm_ring
      _ = 1 + (w + 1) * e + w * e := by
            rw [show (w * e) * ((w + 1) * e) = 0 by
              calc (w * e) * ((w + 1) * e) = w * ((e * (w + 1)) * e) := by noncomm_ring
                _ = w * (((w + 1) * e) * e) := by rw [hew1]
                _ = (w * (w + 1)) * (e * e) := by noncomm_ring
                _ = 0 := by
                    rw [show w * (w + 1) = 1 by
                      calc w * (w + 1) = w * w + w := by noncomm_ring
                        _ = (w + 1) + w := by rw [hw2]
                        _ = 1 := by
                            rw [show (w + 1) + w = (w + w) + 1 by abel,
                              VSub.add_self, zero_add],
                      hee, mul_zero],
              add_zero]
      _ = 1 + e := by
            rw [show 1 + (w + 1) * e + w * e = 1 + (((w + 1) + w) * e) by noncomm_ring,
              show (w + 1) + w = 1 by
                rw [show (w + 1) + w = (w + w) + 1 by abel, VSub.add_self, zero_add],
              one_mul]
  have hXk : vConj hD hhat * (1 + (w + 1) * e) = (1 + w * e) * vConj hD hhat := by
    rw [hX]
    exact sl2F4_conj_eq (R := AddMonoid.End (VSub hD)) (VSub.add_self hD) hew.symm hfw.symm hw2
      hee hefe
  let commElt : G := hhat * k * hhat⁻¹ * k⁻¹
  have hcommf4 : commElt ∈ f4N hD Q w Y := by
    dsimp only [commElt]
    exact (f4N hD Q w Y).mul_mem
      ((f4N hD Q w Y).mul_mem
        ((f4N hD Q w Y).mul_mem hhhatf4 hkf4)
        ((f4N hD Q w Y).inv_mem hhhatf4))
      ((f4N hD Q w Y).inv_mem hkf4)
  have hhhatInvV : hhat⁻¹ ∈ VN := VN.inv_mem ((f4N_le_wComm hD Q hhhatf4).1)
  have hkInvV : k⁻¹ ∈ VN := VN.inv_mem ((f4N_le_wComm hD Q hkf4).1)
  have hcommV : commElt ∈ VN := by
    dsimp only [commElt]
    exact VN.mul_mem (VN.mul_mem (VN.mul_mem ((f4N_le_wComm hD Q hhhatf4).1)
      ((f4N_le_wComm hD Q hkf4).1)) hhhatInvV) hkInvV
  have hvconj_commElt : vConj hD commElt =
      vConj hD hhat * vConj hD k * vConj hD hhat⁻¹ * vConj hD k⁻¹ := by
    dsimp only [commElt]
    calc vConj hD (hhat * k * hhat⁻¹ * k⁻¹)
        = vConj hD (hhat * k) * vConj hD (hhat⁻¹ * k⁻¹) := by
            rw [show hhat * k * hhat⁻¹ * k⁻¹ = (hhat * k) * (hhat⁻¹ * k⁻¹) by group,
              vConj_mul hD (VN.mul_mem ((f4N_le_wComm hD Q hhhatf4).1)
                ((f4N_le_wComm hD Q hkf4).1)) (VN.mul_mem hhhatInvV hkInvV)]
      _ = (vConj hD hhat * vConj hD k) * (vConj hD hhat⁻¹ * vConj hD k⁻¹) := by
            rw [vConj_mul hD ((f4N_le_wComm hD Q hhhatf4).1) ((f4N_le_wComm hD Q hkf4).1),
              vConj_mul hD hhhatInvV hkInvV]
      _ = vConj hD hhat * vConj hD k * vConj hD hhat⁻¹ * vConj hD k⁻¹ := by
            noncomm_ring
  have hk0inv_eq : vConj hD k⁻¹ = 1 + (w + 1) * e := by
    have h1 : (1 + (w + 1) * e) * (1 + (w + 1) * e) = 1 := hk0sq
    have h2 : vConj hD k⁻¹ * (1 + (w + 1) * e) = 1 := by
      have h := vConj_inv_mul hD ((f4N_le_wComm hD Q hkf4).1)
      rwa [hvconj_k] at h
    calc vConj hD k⁻¹ = vConj hD k⁻¹ * 1 := (mul_one _).symm
      _ = vConj hD k⁻¹ * ((1 + (w + 1) * e) * (1 + (w + 1) * e)) := by rw [h1]
      _ = (vConj hD k⁻¹ * (1 + (w + 1) * e)) * (1 + (w + 1) * e) := by rw [mul_assoc]
      _ = 1 * (1 + (w + 1) * e) := by rw [h2]
      _ = 1 + (w + 1) * e := one_mul _
  have hcomm_eq : vConj hD commElt = 1 + e := by
    rw [hvconj_commElt, hvconj_k, hXk]
    have hXXinv : vConj hD hhat * vConj hD hhat⁻¹ = 1 :=
      vConj_mul_inv hD ((f4N_le_wComm hD Q hhhatf4).1)
    calc (1 + w * e) * vConj hD hhat * vConj hD hhat⁻¹ * vConj hD k⁻¹
        = (1 + w * e) * (vConj hD hhat * vConj hD hhat⁻¹) * vConj hD k⁻¹ := by
            noncomm_ring
      _ = (1 + w * e) * 1 * vConj hD k⁻¹ := by rw [hXXinv]
      _ = (1 + w * e) * (1 + (w + 1) * e) := by rw [hk0inv_eq, mul_one]
      _ = 1 + e := hfinish
  let k' : G := commElt⁻¹ * ζ
  have hk'f4 : k' ∈ f4N hD Q w Y := by
    dsimp only [k']
    exact (f4N hD Q w Y).mul_mem ((f4N hD Q w Y).inv_mem hcommf4) hζf4
  have hk'Q : k' ∈ normalizer (Q : Set G) := (f4N_le_normalizer_Q hD Q hk'f4)
  have hk'V : k' ∈ VN := (f4N_le_wComm hD Q hk'f4).1
  have hk'conj : vConj hD k' = 1 := by
    dsimp only [k']
    rw [vConj_mul hD (VN.inv_mem hcommV) hζV]
    have hζeq : vConj hD ζ = 1 + e := hone_e.symm
    rw [hζeq]
    have hinv : vConj hD commElt⁻¹ * vConj hD commElt = 1 :=
      vConj_inv_mul hD hcommV
    rwa [hcomm_eq] at hinv
  have hk'NV : k' ∈ normalizer (Q : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G) := by
    refine ⟨hk'Q, mem_centralizer_iff.2 fun v hv => ?_⟩
    have hval := val_vConj_apply hD hk'V (AbelianSub.mk v hv)
    rw [hk'conj] at hval
    simp only [AbelianSub.val_mk] at hval
    change v = k' * v * k'⁻¹ at hval
    calc v * k' = (k' * v * k'⁻¹) * k' := by
          conv_lhs => rw [hval]
      _ = k' * v := by group
  have hzeta_eq : ζ = commElt * k' := by
    dsimp only [k']
    group
  have hkappa_zero : f4Kappa hD Q y ζ = 0 := by
    rw [hzeta_eq,
      f4Kappa_mul H W W2 hD hQ hq4 hsq hΦ hyHn hY hcommf4 hk'f4,
      f4Kappa_commutator H W W2 hD hQ hq4 hsq hΦ hyHn hY hhhatf4 hkf4,
      f4Kappa_eq_zero_of_mem_NV H W W2 hD hQ hq4 hsq hwH hΦ hyHn hk'f4 hk'NV,
      zero_add]
  have hw0 := ThLocalIn2.comm_mem_B_not_mem_Aa W W2 F hc hS hζS hyS hζM hyM
  obtain ⟨hw0B, hw0notAa⟩ := hw0
  have hkappa_one : f4Kappa hD Q y ζ = 1 := by
    rcases W2.mem_Aa_or_mul_b W hw0B with h | h
    · exact absurd h hw0notAa
    · let a1 : G := ζ * y * ζ⁻¹ * y⁻¹ * b
      have ha1Aa : a1 ∈ Aa := h
      have hw0_eq : ζ * y * ζ⁻¹ * y⁻¹ = a1 * b⁻¹ := by
        dsimp only [a1]
        group
      have ha1D : a1 ∈ D := hD.Aa_le ha1Aa
      have ha1Q : a1 ∈ Q := hQ.D_le ha1D
      have ha1NQ : a1 ∈ normalizer (Q : Set G) := by
        have hcomm : ∀ q ∈ Q, a1 * q = q * a1 := fun q hq => hQ.comm a1 ha1Q q hq
        refine mem_normalizer_iff.2 fun q => ⟨fun hq => ?_, fun hq => ?_⟩
        · rw [show a1 * q * a1⁻¹ = q by rw [hcomm q hq]; group]
          exact hq
        · have hq' : q ∈ Q := by
            have h1 : a1⁻¹ * (a1 * q * a1⁻¹) * a1 ∈ Q :=
              Q.mul_mem (Q.mul_mem (Q.inv_mem ha1Q) hq) ha1Q
            rw [show a1⁻¹ * (a1 * q * a1⁻¹) * a1 = q by group] at h1
            exact h1
          exact hq'
      have ha1CV : a1 ∈ centralizer (omega1 D hD.comm : Set G) :=
        mem_centralizer_iff.2 fun v hv => (hD.comm a1 ha1D v hv.1).symm
      have ha1C : a1 ∈ centralizer (D : Set G) :=
        mem_centralizer_iff.2 fun d hd => (hD.comm a1 ha1D d hd).symm
      have ha1NV : a1 ∈ normalizer (Q : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G) := ⟨ha1NQ, ha1CV⟩
      have hphi_a1 : phiQ hD Q a1 = 0 :=
        QHyp.phiQ_eq_zero_of_mem_centralizer_D hD hQ hq4 hsq ha1NV ha1C
      have hbNV : b ∈ normalizer (Q : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G) := ThCyc.b_mem_NV W W2 hD hb hQ
      have hbinvNV : b⁻¹ ∈ normalizer (Q : Set G) ⊓
          centralizer (omega1 D hD.comm : Set G) :=
        ⟨(normalizer (Q : Set G)).inv_mem hbNV.1,
          (centralizer (omega1 D hD.comm : Set G)).inv_mem hbNV.2⟩
      have hphi_binv : phiQ hD Q b⁻¹ = 1 := by
        have hsum : phiQ hD Q b + phiQ hD Q b⁻¹ = 0 := by
          have h := QHyp.phiQ_mul hD hQ hq4 hsq hbNV hbinvNV
          rw [mul_inv_cancel, phiQ_one_eq_zero hD hQ hq4 hsq] at h
          exact h.symm
        have hneg : phiQ hD Q b⁻¹ = -(phiQ hD Q b) :=
          eq_neg_of_add_eq_zero_right hsum
        rw [hβ] at hneg
        calc phiQ hD Q b⁻¹ = -(1 : AddMonoid.End (VSub hD)) := hneg
          _ = 1 := neg_eq_of_add_eq_zero_right (VSub.add_self hD 1)
      calc f4Kappa hD Q y ζ
          = phiQ hD Q (a1 * b⁻¹) := by
              dsimp only [f4Kappa]
              rw [hw0_eq]
        _ = phiQ hD Q a1 + phiQ hD Q b⁻¹ :=
              QHyp.phiQ_mul hD hQ hq4 hsq ha1NV hbinvNV
        _ = 1 := by rw [hphi_a1, hphi_binv, zero_add]
  have hcontra : (0 : AddMonoid.End (VSub hD)) = 1 := hkappa_zero.symm.trans hkappa_one
  have hzV : z ∈ omega1 D hD.comm := H.A_le_omega1 W W2 hD W.z_mem_A
  let zz : VSub hD := AbelianSub.mk z hzV
  have hz_ne : zz ≠ 0 := by
    intro h
    apply W.z_ne_one
    have := congrArg AbelianSub.val h
    simpa [zz] using this
  have h01 : (0 : AddMonoid.End (VSub hD)) ≠ 1 := by
    intro h
    apply hz_ne
    have hz0 : zz = 0 := by
      have := congrArg (fun f => f zz) h
      simpa using this.symm
    exact hz0
  exact h01 hcontra

end CFSG.EvenSporadicStandard.ThStd
