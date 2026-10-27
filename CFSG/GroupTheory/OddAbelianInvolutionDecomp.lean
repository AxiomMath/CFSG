module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG

theorem exists_fixed_add_antiFixed {A : Type*} [AddCommGroup A] [Finite A]
    (hodd : Odd (Nat.card A)) (t : A ≃+ A) (ht2 : t + t = 0) (y : A) :
    ∃ b a : A, t b = b ∧ t a = -a ∧ y = b + a := by
  haveI : Nonempty A := ⟨0⟩
  have hcop : (Nat.card A).Coprime 2 := Nat.coprime_two_right.mpr hodd
  have hbij : Function.Bijective (fun a : A => 2 • a) := hcop.nsmul_right_bijective
  let half : A → A := Function.invFun (fun a : A => 2 • a)
  have hhalf : ∀ a : A, 2 • half a = a := fun a => Function.invFun_eq (hbij.2 a)
  have hhalf_add : ∀ a b : A, half (a + b) = half a + half b := by
    intro a b
    apply hbij.1
    change 2 • half (a + b) = 2 • (half a + half b)
    rw [hhalf, nsmul_add, hhalf, hhalf]
  have htty : ∀ z : A, t (t z) = z := by
    intro z
    simpa using DFunLike.congr_fun ht2 z
  have hhalf_yy : half (y + y) = y := by
    apply hbij.1
    change 2 • half (y + y) = 2 • y
    rw [hhalf, two_nsmul]
  refine ⟨half (y + t y), half (y - t y), ?_, ?_, ?_⟩
  ·
    apply hbij.1
    change 2 • t (half (y + t y)) = 2 • half (y + t y)
    calc
      2 • t (half (y + t y)) = t (half (y + t y)) + t (half (y + t y)) :=
        two_nsmul (t (half (y + t y)))
      _ = t (half (y + t y) + half (y + t y)) := (map_add t _ _).symm
      _ = t (2 • half (y + t y)) := by rw [two_nsmul]
      _ = t (y + t y) := by rw [hhalf]
      _ = t y + t (t y) := map_add t y (t y)
      _ = t y + y := by rw [htty]
      _ = y + t y := add_comm _ _
      _ = 2 • half (y + t y) := (hhalf (y + t y)).symm
  ·
    apply hbij.1
    change 2 • t (half (y - t y)) = 2 • (-(half (y - t y)))
    calc
      2 • t (half (y - t y)) = t (half (y - t y)) + t (half (y - t y)) :=
        two_nsmul (t (half (y - t y)))
      _ = t (half (y - t y) + half (y - t y)) := (map_add t _ _).symm
      _ = t (2 • half (y - t y)) := by rw [two_nsmul]
      _ = t (y - t y) := by rw [hhalf]
      _ = t y - t (t y) := map_sub t y (t y)
      _ = t y - y := by rw [htty]
      _ = -(y - t y) := by
        simp only [sub_eq_add_neg]
        rw [neg_add_rev, neg_neg]
      _ = -(2 • half (y - t y)) := by rw [hhalf]
      _ = 2 • (-(half (y - t y))) := by
        rw [two_nsmul (-(half (y - t y))), two_nsmul (half (y - t y)), neg_add_rev]
  ·
    calc
      y = half (y + y) := hhalf_yy.symm
      _ = half ((y + t y) + (y - t y)) := by
        congr 1
        rw [sub_eq_add_neg]
        symm
        calc
          (y + t y) + (y + -t y) = (y + y) + (t y + -t y) := by ac_rfl
          _ = (y + y) + 0 := by rw [add_neg_cancel]
          _ = y + y := by rw [add_zero]
      _ = half (y + t y) + half (y - t y) := hhalf_add _ _

theorem exists_fixed_mul_fixed_of_fixedPointFree {A : Type*} [AddCommGroup A] [Finite A]
    (hodd : Odd (Nat.card A)) (τ t : A ≃+ A) (hτ2 : τ + τ = 0) (ht2 : t + t = 0)
    (hcomm : τ + t = t + τ) (hτfree : ∀ y : A, τ y = y → y = 0) (y : A) :
    ∃ a b : A, (τ + t) a = a ∧ t b = b ∧ y = a + b := by
  obtain ⟨b, a, htb, hta, hba⟩ := exists_fixed_add_antiFixed hodd t ht2 y
  have hττ : ∀ z : A, τ (τ z) = z := by
    intro z
    simpa using DFunLike.congr_fun hτ2 z
  have hτa : τ a = -a := by
    have hfix : τ (a + τ a) = a + τ a := by
      rw [map_add, hττ, add_comm]
    have hzero : a + τ a = 0 := hτfree (a + τ a) hfix
    exact eq_neg_of_add_eq_zero_right hzero
  refine ⟨a, b, ?_, htb, ?_⟩
  · rw [AddAut.add_apply, hta, map_neg, hτa, neg_neg]
  · exact hba.trans (add_comm b a)

end CFSG
