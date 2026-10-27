module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.GF2Thm1311.FixedSpaceMono
public import CFSG.HardMathSupport.RichardWeiss.Proving.InvolutionPairEngine

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.GF2Thm1311

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

variable {V : Type} [CommGroup V] [Finite V]

theorem index_fixV_le_four_iff (A : Subgroup (MulAut V)) :
    (fixV A).index ≤ 4 ↔ Nat.card V ≤ 4 * Nat.card {v : V | ∀ b ∈ A, b v = v} := by
  have h := Subgroup.card_mul_index (fixV A)
  have hc : Nat.card (fixV A) = Nat.card {v : V | ∀ b ∈ A, b v = v} := rfl
  rw [hc] at h
  have hpos : 0 < Nat.card {v : V | ∀ b ∈ A, b v = v} := by
    rw [← hc]; exact Nat.card_pos
  rw [← h]
  constructor
  · intro hi; rw [mul_comm]; exact Nat.mul_le_mul_right _ hi
  · intro hi
    nlinarith

theorem index_fixV_zpowers_le_four {A : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ A)
    (h : Nat.card V ≤ 4 * Nat.card {v : V | ∀ b ∈ A, b v = v}) :
    (fixV (Subgroup.zpowers a)).index ≤ 4 := by
  rw [index_fixV_le_four_iff]
  have := card_le_four_mul_fixed_of_mem ha h
  have e : {v : V | ∀ b ∈ Subgroup.zpowers a, b v = v} = {v : V | a v = v} := by
    ext v
    exact mem_fixV_zpowers
  rwa [e]

theorem orderOf_two_le_four_of_conj_pair (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (h : Nat.card V ≤ 4 * Nat.card {v : V | ∀ b ∈ A, b v = v}) {a : MulAut V} (ha : a ∈ A)
    (g : MulAut V) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hab : orderOf (a * (g * a * g⁻¹)) = p) :
    orderOf (2 : ZMod p) ≤ 4 := by
  have hP := CFSG.HardMathSupport.RichardWeiss.Proving.two_pow_orderOf_two_le_index_fixV_mul_index_fixV
    hV a (g * a * g⁻¹) hp2 hab
  rw [index_fixV_conj] at hP
  have h4 := index_fixV_zpowers_le_four ha h
  have h16 : 2 ^ orderOf (2 : ZMod p) ≤ 16 :=
    hP.trans (by calc _ ≤ 4 * 4 := Nat.mul_le_mul h4 h4
                    _ = 16 := rfl)
  by_contra hlt
  push_neg at hlt
  have : 2 ^ 5 ≤ 2 ^ orderOf (2 : ZMod p) := Nat.pow_le_pow_right (by norm_num) hlt
  omega

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.GF2Thm1311
