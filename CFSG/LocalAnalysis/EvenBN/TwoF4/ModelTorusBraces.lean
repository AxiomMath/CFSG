module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelTorus
public import CFSG.LocalAnalysis.EvenBN.TwoF4.TwistedAdditive

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair torusWeight torusWeight_apply torusExp0 torusExp1)

namespace Idx

@[expose] def col : Idx → Fin 8
  | .i1 | .i2 => 0
  | .i3 => 1
  | .i4 | .i8 => 2
  | .i5 | .i12 => 3
  | .i6 | .i11 => 4
  | .i7 => 5
  | .i9 => 6
  | .i10 => 7

@[expose] def miyamotoExp (θ : ℤ) (i j : Idx) : ℤ :=
  (match j with
  | .i1 => ![0, 2 * θ - 2, 2 * θ - 2, -4 * θ + 2, -2 * θ + 2, -2 * θ + 2, -2 * θ, 2 * θ]
  | .i2 => ![0, -2 * θ, -2 * θ, -2, 2 * θ, 2 * θ, -2 * θ - 2, 2 * θ + 2]
  | .i3 => ![2 * θ - 2, 0, -2 * θ + 2, 2 * θ, -2 * θ, -2, 2, -4 * θ]
  | .i4 => ![2 * θ - 2, 2 * θ - 2, 0, -2 * θ + 2, -4 * θ + 2, -2 * θ, -2 * θ + 2, -2 * θ]
  | .i5 => ![-4 * θ + 2, -2 * θ, 2 * θ - 2, 0, 2 * θ - 2, -2 * θ, 2 * θ - 2, 2 * θ - 2]
  | .i6 => ![2 * θ - 2, -2 * θ, -4 * θ + 2, 2 * θ - 2, 0, 2 * θ - 2, -2 * θ, -2 * θ + 2]
  | .i7 => ![2 * θ - 2, -2, -2 * θ, -2 * θ, -2 * θ + 2, 0, -4 * θ, 2]
  | .i8 => ![-2 * θ, -2 * θ, 0, 2 * θ, -2, -2 * θ - 2, 2 * θ, -2 * θ - 2]
  | .i9 => ![-2 * θ, -2, 2 * θ - 2, -2 * θ + 2, -2 * θ, -4 * θ, 0, -2]
  | .i10 => ![-2 * θ, -4 * θ, -2 * θ, 2 * θ - 2, 2 * θ - 2, -2, -2, 0]
  | .i11 => ![-2 * θ, -2 * θ - 2, -2, -2 * θ, 0, -2 * θ, -2 * θ - 2, 2 * θ]
  | .i12 => ![-2, -2 * θ - 2, -2 * θ, 0, -2 * θ, -2 * θ - 2, -2 * θ, -2 * θ]) i.col

@[expose] def brace (i j : Idx) : Fin 3 :=
  (match j with
  | .i1 => ![0, 1, 1, 1, 1, 1, 1, 1]
  | .i2 => ![0, 2, 2, 2, 2, 2, 2, 2]
  | .i3 => ![1, 0, 2, 1, 1, 1, 2, 2]
  | .i4 => ![1, 1, 0, 2, 2, 1, 1, 2]
  | .i5 => ![1, 2, 1, 0, 2, 1, 2, 1]
  | .i6 => ![1, 2, 1, 1, 0, 2, 1, 2]
  | .i7 => ![1, 2, 2, 2, 1, 0, 1, 1]
  | .i8 => ![2, 2, 0, 1, 1, 2, 2, 1]
  | .i9 => ![2, 2, 1, 2, 1, 1, 0, 2]
  | .i10 => ![2, 2, 2, 1, 2, 1, 1, 0]
  | .i11 => ![2, 1, 2, 2, 0, 1, 2, 1]
  | .i12 => ![2, 1, 2, 0, 1, 2, 1, 2] : Fin 8 → Fin 3) i.col

@[expose] def braceTwo (i : Idx) : Fin 3 :=
  (![1, 1, 1, 1, 2, 2, 2, 1] : Fin 8 → Fin 3) i.col

@[expose] def braceNegTwo (i : Idx) : Fin 3 :=
  (![2, 2, 2, 2, 1, 1, 1, 2] : Fin 8 → Fin 3) i.col

@[expose] def miyamotoScale (θ : ℤ) (i : Idx) : ℤ :=
  ![-(4 + 4 * θ), 4 + 4 * θ, 4 + 4 * θ, 4 + 4 * θ, -(4 + 4 * θ), -(4 + 4 * θ), 4 + 4 * θ,
    -(4 + 4 * θ)] i.col

@[expose] def torusHiExp (θ : ℤ) (i j : Idx) : ℤ :=
  torusExp0 θ j.leadRoot * torusExp1 θ i.leadRoot - torusExp1 θ j.leadRoot * torusExp0 θ i.leadRoot

end Idx

section Arithmetic

variable {K : Type} [Field K] [Finite K] {a : ℕ}

theorem units_zpow_eq_of_intCast_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) (u : Kˣ) {e e' : ℤ}
    (h : (e : ZMod (2 ^ (2 * a + 1) - 1)) = e') : u ^ e = u ^ e' := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub e e' _).1 h
  refine units_zpow_congr hK u (-k) ?_
  rw [Nat.cast_sub Nat.one_le_two_pow] at hk
  push_cast at hk
  linear_combination -hk

theorem exists_intCast_mul_eq_one {n : ℕ} {x : ℤ} (hx : IsUnit (x : ZMod n)) :
    ∃ d : ℤ, ((x * d : ℤ) : ZMod n) = 1 := by
  obtain ⟨v, hv⟩ := hx
  refine ⟨((v⁻¹ : (ZMod n)ˣ) : ZMod n).cast, ?_⟩
  rw [Int.cast_mul, ZMod.intCast_zmod_cast, ← hv, Units.mul_inv]

theorem exists_zpow_eq_of_isUnit (hK : Nat.card K = 2 ^ (2 * a + 1)) {c : ℤ}
    (hc : IsUnit (c : ZMod (2 ^ (2 * a + 1) - 1))) (w : Kˣ) : ∃ u : Kˣ, u ^ c = w := by
  obtain ⟨d, hd⟩ := exists_intCast_mul_eq_one hc
  refine ⟨w ^ d, ?_⟩
  rw [← zpow_mul]
  conv_rhs => rw [← zpow_one w]
  exact units_zpow_eq_of_intCast_eq hK w (by rw [mul_comm d c]; exact_mod_cast hd)

end Arithmetic

theorem miyamotoScale_mul_torusHiExp (a : ℕ) {i : Idx} (hi : i.isCenter = false) (j : Idx) :
    ((Idx.miyamotoScale (2 ^ a) i * Idx.torusHiExp (2 ^ a) i j : ℤ) :
        ZMod (2 ^ (2 * a + 1) - 1)) = Idx.miyamotoExp (2 ^ a) i j := by
  obtain ⟨t, ht⟩ : ∃ t : ZMod (2 ^ (2 * a + 1) - 1), t = 2 ^ a := ⟨_, rfl⟩
  have hθ : 2 * t ^ 2 = 1 := by rw [ht]; exact two_mul_thetaExp_sq a
  have he := torusExp_leadRoot ((2 : ℤ) ^ a)
  have key : ∀ j : Idx, ∀ i ∈ [Idx.i1, .i3, .i4, .i5, .i6, .i7, .i9, .i10],
      ((Idx.miyamotoScale (2 ^ a) i * Idx.torusHiExp (2 ^ a) i j : ℤ) :
        ZMod (2 ^ (2 * a + 1) - 1)) = Idx.miyamotoExp (2 ^ a) i j := by
    intro j
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    cases j <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Idx.miyamotoScale, Idx.torusHiExp, Idx.miyamotoExp, Idx.col, he] <;> push_cast <;>
      rw [← ht]
    · linear_combination
    · linear_combination (-2 - 6 * t) * hθ
    · linear_combination (-2 - 6 * t) * hθ
    · linear_combination (-2 + 4 * t) * hθ
    · linear_combination (-2 + 2 * t) * hθ
    · linear_combination (-2 + 2 * t) * hθ
    · linear_combination (-4 - 2 * t) * hθ
    · linear_combination (-2 * t) * hθ
    · linear_combination (4 + 4 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (-4 - 2 * t) * hθ
    · linear_combination (2) * hθ
    · linear_combination (-2 * t) * hθ
    · linear_combination (4 + 2 * t) * hθ
    · linear_combination (-2 - 2 * t) * hθ
    · linear_combination (-2 - 2 * t) * hθ
    · linear_combination (-2 - 6 * t) * hθ
    · linear_combination
    · linear_combination (2 + 6 * t) * hθ
    · linear_combination (-2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (-2 - 4 * t) * hθ
    · linear_combination (2 + 4 * t) * hθ
    · linear_combination (4 * t) * hθ
    · linear_combination (-2 - 6 * t) * hθ
    · linear_combination (-2 - 6 * t) * hθ
    · linear_combination
    · linear_combination (-2 + 2 * t) * hθ
    · linear_combination (-2 + 4 * t) * hθ
    · linear_combination (-4 - 2 * t) * hθ
    · linear_combination (-2 + 2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (-2 + 4 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (-2 + 4 * t) * hθ
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (-2 + 2 * t) * hθ
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination (-2 - 4 * t) * hθ
    · linear_combination (-4 - 2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (-2 + 2 * t) * hθ
    · linear_combination
    · linear_combination (-4) * hθ
    · linear_combination (-2) * hθ
    · linear_combination (-4 - 2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (4 + 4 * t) * hθ
    · linear_combination (-2 * t) * hθ
    · linear_combination (2) * hθ
    · linear_combination (-2 - 2 * t) * hθ
    · linear_combination (4 + 2 * t) * hθ
    · linear_combination (2 + 2 * t) * hθ
    · linear_combination (-4 - 2 * t) * hθ
    · linear_combination (-2 - 4 * t) * hθ
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination (-2 + 2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (-4) * hθ
    · linear_combination
    · linear_combination (2) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (4 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination (2 - 2 * t) * hθ
    · linear_combination (2) * hθ
    · linear_combination (2) * hθ
    · linear_combination
    · linear_combination (2 * t) * hθ
    · linear_combination (-2 - 2 * t) * hθ
    · linear_combination (-2 - 4 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination
    · linear_combination (2 * t) * hθ
    · linear_combination (-2 - 2 * t) * hθ
    · linear_combination (-2 * t) * hθ
    · linear_combination (-2 - 4 * t) * hθ
    · linear_combination (-2 - 2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination
    · linear_combination (2 * t) * hθ
    · linear_combination (-2 - 2 * t) * hθ
    · linear_combination (2 * t) * hθ
    · linear_combination (2 * t) * hθ
  refine key j i ?_
  cases i <;> simp_all [Idx.isCenter]

theorem miyamotoExp_mem_brace (a : ℕ) {i : Idx} (hi : i.isCenter = false) (j : Idx) :
    (Idx.brace i j = 0 ∧ ((Idx.miyamotoExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1)) = 0) ∨
      (Idx.brace i j = i.braceTwo ∧
        IsBraceTwo a ((Idx.miyamotoExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1))) ∨
      (Idx.brace i j = i.braceNegTwo ∧
        IsBraceNegTwo a ((Idx.miyamotoExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1))) := by
  have key : ∀ j : Idx, ∀ i ∈ [Idx.i1, .i3, .i4, .i5, .i6, .i7, .i9, .i10],
      (Idx.brace i j = 0 ∧
          ((Idx.miyamotoExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1)) = 0) ∨
        (Idx.brace i j = i.braceTwo ∧
          IsBraceTwo a ((Idx.miyamotoExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1))) ∨
        (Idx.brace i j = i.braceNegTwo ∧
          IsBraceNegTwo a ((Idx.miyamotoExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1))) := by
    intro j
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    cases j <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> push_cast [Idx.miyamotoExp, Idx.col]
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_four_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_two_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_four_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_four_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_four_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_four_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp_add_two⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_four_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp_add_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_four_mul_thetaExp⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_four_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inl ⟨by decide, isBraceTwo_neg_two_mul_thetaExp_sub_two⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
    · exact Or.inr (Or.inr ⟨by decide, isBraceNegTwo_neg_two_mul_thetaExp⟩)
  refine key j i ?_
  cases i <;> simp_all [Idx.isCenter]

theorem differentBraces_miyamotoExp {a : ℕ} (ha : 1 ≤ a) {i : Idx} (hi : i.isCenter = false)
    {j k : Idx} (hjk : Idx.brace i j ≠ Idx.brace i k) :
    DifferentBraces a ((Idx.miyamotoExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1))
      ((Idx.miyamotoExp (2 ^ a) i k : ℤ) : ZMod (2 ^ (2 * a + 1) - 1)) := by
  rcases miyamotoExp_mem_brace a hi j with ⟨hj, hx⟩ | ⟨hj, hx⟩ | ⟨hj, hx⟩ <;>
    rcases miyamotoExp_mem_brace a hi k with ⟨hk, hy⟩ | ⟨hk, hy⟩ | ⟨hk, hy⟩
  · exact absurd (hj.trans hk.symm) hjk
  · exact Or.inl ⟨hx, hy.ne_zero ha⟩
  · exact Or.inl ⟨hx, hy.ne_zero ha⟩
  · exact Or.inr (Or.inl ⟨hx.ne_zero ha, hy⟩)
  · exact absurd (hj.trans hk.symm) hjk
  · exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))
  · exact Or.inr (Or.inl ⟨hx.ne_zero ha, hy⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨hx, hy⟩))
  · exact absurd (hj.trans hk.symm) hjk

theorem not_sameTwoOrbit_torusHiExp {a : ℕ} (ha : 1 ≤ a) {i : Idx} (hi : i.isCenter = false)
    {j k : Idx} (hjk : Idx.brace i j ≠ Idx.brace i k) :
    ¬ SameTwoOrbit ((Idx.torusHiExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1))
      ((Idx.torusHiExp (2 ^ a) i k : ℤ) : ZMod (2 ^ (2 * a + 1) - 1)) := by
  intro h
  have h' := h.mul_left ((Idx.miyamotoScale (2 ^ a) i : ℤ) : ZMod (2 ^ (2 * a + 1) - 1))
  rw [← Int.cast_mul, ← Int.cast_mul, miyamotoScale_mul_torusHiExp a hi,
    miyamotoScale_mul_torusHiExp a hi] at h'
  exact (differentBraces_miyamotoExp ha hi hjk).not_sameTwoOrbit ha h'

theorem isUnit_torusHiExp (a : ℕ) {i : Idx} (hi : i.isCenter = false) {j : Idx}
    (hj : Idx.brace i j ≠ 0) :
    IsUnit ((Idx.torusHiExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1)) := by
  have h : IsUnit ((Idx.miyamotoExp (2 ^ a) i j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1)) := by
    rcases miyamotoExp_mem_brace a hi j with ⟨h0, -⟩ | ⟨-, hx⟩ | ⟨-, hx⟩
    · exact absurd h0 hj
    · exact hx.isUnit
    · exact hx.isUnit
  rw [← miyamotoScale_mul_torusHiExp a hi, Int.cast_mul] at h
  exact isUnit_of_mul_isUnit_right h

section Lemma21

variable {K : Type} [Field K] {a : ℕ}

theorem rootSection_eq_zero_of_brace_ne (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {i : Idx} (hi : i.isCenter = false) {j k : Idx} (hjk : Idx.brace i j ≠ Idx.brace i k)
    {φ : K → K} (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hφ : ∀ t : Kˣ × Kˣ, rootChar K a i t = 1 →
      ∀ x, φ ((rootChar K a j t : K) * x) = (rootChar K a k t : K) * φ x) (x : K) :
    φ x = 0 := by
  refine twisted_zpow_eq_zero_of_not_sameTwoOrbit (by omega) hK hadd (fun u y => ?_)
    (not_sameTwoOrbit_torusHiExp ha hi hjk) x
  have h := hφ (torusHiParam K a i u) (rootChar_torusHiParam_self i u) y
  rwa [rootChar_torusHiParam, rootChar_torusHiParam] at h

theorem exists_rootChar_mul_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isCenter = false) {j : Idx} (hj : Idx.brace i j ≠ 0) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) : ∃ t : Kˣ × Kˣ, rootChar K a i t = 1 ∧ (rootChar K a j t : K) * x = y := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨u, hu⟩ := exists_zpow_eq_of_isUnit hK (isUnit_torusHiExp a hi hj)
    (Units.mk0 y hy / Units.mk0 x hx)
  refine ⟨torusHiParam K a i u, rootChar_torusHiParam_self i u, ?_⟩
  rw [rootChar_torusHiParam]
  change ((u ^ Idx.torusHiExp (2 ^ a) i j : Kˣ) : K) * x = y
  rw [hu, Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, div_mul_cancel₀ _ hx]

theorem eq_zero_of_forall_rootChar_mul_eq (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {i : Idx} (hi : i.isCenter = false) {j : Idx} (hj : Idx.brace i j ≠ 0) {x : K}
    (h : ∀ t : Kˣ × Kˣ, rootChar K a i t = 1 → (rootChar K a j t : K) * x = x) : x = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  by_contra hx
  obtain ⟨l, hl⟩ := exists_largeReeSigma_ne ha hK
  have hl0 : l ≠ 0 := fun h0 => hl (by rw [h0, largeReeSigma_zero])
  have hl1 : l ≠ 1 := fun h1 => hl (by rw [h1, largeReeSigma, one_pow])
  obtain ⟨t, ht, htx⟩ := exists_rootChar_mul_eq hK hi hj hx (mul_ne_zero hl0 hx)
  rw [h t ht] at htx
  exact hl1 (mul_right_cancel₀ hx (htx.symm.trans (one_mul x).symm))

variable [Finite K] [CharP K F4.prime]

theorem miyamoto_2_1 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isCenter = false) {j k : Idx} (hjk : Idx.brace i j ≠ Idx.brace i k) {φ : K → K}
    (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hφ : ∀ t : Kˣ × Kˣ, torusPair a t ∈ torusHi K a i →
      ∀ x, φ ((rootChar K a j t : K) * x) = (rootChar K a k t : K) * φ x) (x : K) :
    φ x = 0 :=
  rootSection_eq_zero_of_brace_ne ha hK hi hjk hadd
    (fun t ht => hφ t ((mem_torusHi_iff hK i t).2 ht)) x

theorem miyamoto_2_1_pi (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isCenter = false) {j : Idx} {κ : Type*} {ρ : κ → Idx} {φ : K → κ → K}
    (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hφ : ∀ t : Kˣ × Kˣ, torusPair a t ∈ torusHi K a i →
      ∀ x l, φ ((rootChar K a j t : K) * x) l = (rootChar K a (ρ l) t : K) * φ x l)
    {l : κ} (hl : Idx.brace i j ≠ Idx.brace i (ρ l)) (x : K) : φ x l = 0 :=
  miyamoto_2_1 ha hK hi hl (φ := fun x => φ x l) (fun x y => congrFun (hadd x y) l)
    (fun t ht x => hφ t ht x l) x

theorem exists_torusHi_rootChar_mul_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isCenter = false) {j : Idx} (hj : Idx.brace i j ≠ 0) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    ∃ t : Kˣ × Kˣ, torusPair a t ∈ torusHi K a i ∧ (rootChar K a j t : K) * x = y := by
  obtain ⟨t, ht, htx⟩ := exists_rootChar_mul_eq hK hi hj hx hy
  exact ⟨t, (mem_torusHi_iff hK i t).2 ht, htx⟩

end Lemma21

end CFSG.LocalAnalysis.EvenBN.TwoF4
