module

public import CFSG.LieType.Steinberg.Minuscule.Ops
public import CFSG.LieType.Steinberg.Twist
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.LieType.Steinberg.Twist

@[expose] def entryZ (M i j : ℕ) : ℤ :=
  if 2 ≤ dig M j ∧ dig M j / 2 - 1 = i then (if dig M j % 2 = 1 then -1 else 1) else 0

@[expose] def trCheck (d M N : ℕ) : Bool :=
  (List.range d).all fun i => (List.range d).all fun j => entryZ M i j == entryZ N j i

theorem entryZ_eq_of_trCheck {d M N : ℕ} (h : trCheck d M N = true) {i j : ℕ} (hi : i < d)
    (hj : j < d) : entryZ M i j = entryZ N j i := by
  simp only [trCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi j hj

variable {k : Type*} [Field k] {d : ℕ}

theorem neg_one_pow_eq_ite (c : ℕ) : (-1 : k) ^ c = if c % 2 = 1 then -1 else 1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

theorem toMat_toEnd_apply (M : ℕ) (i j : Fin d) :
    toMat (toEnd k d M) i j = (entryZ M i j : k) := by
  rw [toMat, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr,
    LinearEquiv.refl_apply, toEnd_single, entryZ]
  by_cases hc : 2 ≤ dig M j ∧ dig M j / 2 - 1 < d
  · rw [digVec_of_le hc.1 hc.2, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      neg_one_pow_eq_ite]
    by_cases hi : dig M j / 2 - 1 = (i : ℕ)
    · simp only [↓reduceIte, mul_one, hc.1, hi, and_self]
      split_ifs <;> simp
    · have hji : (⟨dig M j / 2 - 1, hc.2⟩ : Fin d) ≠ i := fun h => hi (congrArg Fin.val h)
      simp [hji, hi]
  · have hc' : ¬ (2 ≤ dig M j ∧ dig M j / 2 - 1 = i) := fun h => hc ⟨h.1, h.2 ▸ i.2⟩
    rw [digVec, dite_eq_right hc]
    simp [hc']

theorem toMat_toEnd_map (θ : k →+* k) (M : ℕ) :
    (toMat (toEnd k d M)).map θ = toMat (toEnd k d M) := by
  ext i j
  rw [Matrix.map_apply, toMat_toEnd_apply, map_intCast]

theorem transpose_toMat_toEnd {M N : ℕ} (h : trCheck d M N = true) :
    (toMat (toEnd k d M)).transpose = toMat (toEnd k d N) := by
  ext i j
  rw [Matrix.transpose_apply, toMat_toEnd_apply, toMat_toEnd_apply,
    entryZ_eq_of_trCheck h j.2 i.2]

theorem frobT_toEnd (θ : k →+* k) {M N : ℕ} (h : trCheck d M N = true) :
    frobT θ (toEnd k d M) = toEnd k d N := by
  rw [frobT, transpose_toMat_toEnd h, toMat_toEnd_map, ofMat_toMat]

end CFSG.LieType.Steinberg.Minuscule
