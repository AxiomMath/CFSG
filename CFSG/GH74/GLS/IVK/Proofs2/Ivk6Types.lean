module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.IVK.L2.FieldProj
public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Types

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem card_fieldAut_eq (hF : L2Field F) (e : K ≃* L2 F) {p n : ℕ} (hp : p.Prime)
    (h : Nat.card F = p ^ n) : Nat.card (F ≃+* F) = n := by
  obtain ⟨-, ⟨ε⟩, hn⟩ := ivk_1_2e F hF K e
  rw [← Nat.card_congr ε.toEquiv]
  exact hn p n hp h

theorem fieldProj_eq_one_of_prime (hF : L2Field F) (e : K ≃* L2 F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7) (x : MulAut K) : fieldProj e x = 1 := by
  have h1 : Nat.card (F ≃+* F) = 1 := by
    rcases hq with h | h
    · exact card_fieldAut_eq hF e (p := 5) (n := 1) (by norm_num) (by rw [h]; norm_num)
    · exact card_fieldAut_eq hF e (p := 7) (n := 1) (by norm_num) (by rw [h]; norm_num)
  have hsub : Subsingleton (F ≃+* F) := (Nat.card_eq_one_iff_unique.1 h1).1
  exact Subsingleton.elim _ _

theorem mem_innDiagSub_of_prime (hF : L2Field F) (e : K ≃* L2 F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7) (x : MulAut K) : x ∈ innDiagSub e :=
  (mem_innDiagSub_iff e x).2 (fieldProj_eq_one_of_prime hF e hq x)

theorem card_eq_nine_of_not_mem_innDiagSub (hF : L2Field F) (e : K ≃* L2 F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) {x : MulAut K}
    (hx : x ∉ innDiagSub e) : Nat.card F = 9 := by
  rcases hq with h | h | h
  · exact absurd (mem_innDiagSub_of_prime hF e (Or.inl h) x) hx
  · exact absurd (mem_innDiagSub_of_prime hF e (Or.inr h) x) hx
  · exact h

end Types

section Comm

variable {G : Type} [Group G]

theorem comm_of_sq_eq_one {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) :
    a * b = b * a := by
  have ha' : a * a = 1 := by rwa [← pow_two]
  have hb' : b * b = 1 := by rwa [← pow_two]
  have hab' : a * b * (a * b) = 1 := by rwa [← pow_two]
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha'
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb'
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab'
  calc a * b = (a * b)⁻¹ := h3.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h1, h2]

theorem orderOf_eq_two_of_sq {a : G} (ha : a ^ 2 = 1) (ha1 : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime ha ha1

end Comm

end CFSG.GH74.GLS.IVK.Proofs2
