module

public import CFSG.LieType.Steinberg.Classical.SpinOdd.Short
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Commutator

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinOdd

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame CliffordAlgebra QuadraticMap
  Matrix
open scoped commutatorElement

section Vectors

variable {n : ℕ}

@[expose] def IsRootVec (e : Fin n → ℤ) : Prop := IsLong e ∨ IsShort e

theorem dot_single_single (i j : Fin n) (a b : ℤ) :
    (Pi.single i a : Fin n → ℤ) ⬝ᵥ Pi.single j b = if i = j then a * b else 0 := by
  rw [single_dotProduct]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, ite_eq_left rfl]
  · rw [Pi.single_eq_of_ne h, mul_zero, ite_eq_right h]

theorem dot_self_of_isLong {e : Fin n → ℤ} (he : IsLong e) : e ⬝ᵥ e = 2 := by
  obtain ⟨i, j, hij, s, t, rfl⟩ := he
  simp only [add_dotProduct, dotProduct_add, dot_single_single, ite_eq_right hij,
    ite_eq_right (Ne.symm hij), ite_true, boolSign_mul_self]
  norm_num

theorem dot_self_of_isShort {e : Fin n → ℤ} (he : IsShort e) : e ⬝ᵥ e = 1 := by
  obtain ⟨i, s, rfl⟩ := he
  rw [dot_single_single, ite_eq_left rfl, boolSign_mul_self]

theorem not_isRootVec_of_dot {v : Fin n → ℤ} (h1 : v ⬝ᵥ v ≠ 1) (h2 : v ⬝ᵥ v ≠ 2) :
    ¬IsRootVec v := by
  rintro (h | h)
  · exact h2 (dot_self_of_isLong h)
  · exact h1 (dot_self_of_isShort h)

theorem dot_comb (p q : ℕ) (e f : Fin n → ℤ) :
    (p • e + q • f) ⬝ᵥ (p • e + q • f) =
      (p : ℤ) ^ 2 * (e ⬝ᵥ e) + (q : ℤ) ^ 2 * (f ⬝ᵥ f) + 2 * p * q * (e ⬝ᵥ f) := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul]
  simp only [nsmul_eq_mul, dotProduct_comm f e]
  ring

theorem one_le_dot_self {v : Fin n → ℤ} (hv : v ≠ 0) : 1 ≤ v ⬝ᵥ v := by
  obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have h1 : v m * v m ≤ v ⬝ᵥ v :=
    Finset.single_le_sum (f := fun a => v a * v a) (fun a _ => mul_self_nonneg (v a))
      (Finset.mem_univ m)
  have h2 : 0 < v m * v m := mul_self_pos.2 hm
  omega

theorem sign_mul_sign_eq {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

end Vectors

section PairRep

variable {n : ℕ}

@[ext] structure PairRep (n : ℕ) where
  i : Fin n
  j : Fin n
  s : Bool
  t : Bool

namespace PairRep

variable (p : PairRep n)

@[expose] def IsShortRep (e f : Fin n → ℤ) : Prop :=
  p.i ≠ p.j ∧ e = Pi.single p.i (boolSign p.s) ∧ f = Pi.single p.j (boolSign p.t)

@[expose] def IsMixedRep (e f : Fin n → ℤ) : Prop :=
  p.i ≠ p.j ∧ e = Pi.single p.i (boolSign p.s) + Pi.single p.j (boolSign p.t) ∧
    f = Pi.single p.j (boolSign (!p.t))

@[expose] def shortCoeff : ℤ := -2 * boolSign p.s * boolSign p.t * repSign p.i p.j p.s p.t

@[expose] def mixedCoeff₁ : ℤ := boolSign p.s * boolSign (!p.t) * repSign p.i p.j p.s p.t

@[expose] def mixedCoeff₂ : ℤ := repSign p.i p.j p.s (!p.t) * repSign p.i p.j p.s p.t

theorem natAbs_shortCoeff : p.shortCoeff.natAbs = 2 := by
  unfold shortCoeff
  rcases boolSign_eq_one_or_eq_neg_one p.s with h1 | h1 <;>
    rcases boolSign_eq_one_or_eq_neg_one p.t with h2 | h2 <;>
    rcases repSign_eq_one_or_eq_neg_one p.i p.j p.s p.t with h3 | h3 <;>
    rw [h1, h2, h3] <;> rfl

theorem mixedCoeff₁_eq_one_or_eq_neg_one : p.mixedCoeff₁ = 1 ∨ p.mixedCoeff₁ = -1 :=
  sign_mul_sign_eq (sign_mul_sign_eq (boolSign_eq_one_or_eq_neg_one _)
    (boolSign_eq_one_or_eq_neg_one _)) (repSign_eq_one_or_eq_neg_one _ _ _ _)

theorem mixedCoeff₂_eq_one_or_eq_neg_one : p.mixedCoeff₂ = 1 ∨ p.mixedCoeff₂ = -1 :=
  sign_mul_sign_eq (repSign_eq_one_or_eq_neg_one _ _ _ _) (repSign_eq_one_or_eq_neg_one _ _ _ _)

variable {p}

theorem IsShortRep.unique {q : PairRep n} {e f : Fin n → ℤ} (hp : p.IsShortRep e f)
    (hq : q.IsShortRep e f) : p = q := by
  obtain ⟨-, he, hf⟩ := hp
  obtain ⟨-, he', hf'⟩ := hq
  obtain ⟨h1, h2⟩ := eq_of_single_eq_single (he.symm.trans he')
  obtain ⟨h3, h4⟩ := eq_of_single_eq_single (hf.symm.trans hf')
  exact PairRep.ext h1 h3 h2 h4

theorem IsMixedRep.unique {q : PairRep n} {e f : Fin n → ℤ} (hp : p.IsMixedRep e f)
    (hq : q.IsMixedRep e f) : p = q := by
  obtain ⟨hij, he, hf⟩ := hp
  obtain ⟨hij', he', hf'⟩ := hq
  obtain ⟨h3, h4⟩ := eq_of_single_eq_single (hf.symm.trans hf')
  have h4' : p.t = q.t := by simpa using h4
  rcases (single_add_single_eq_iff hij hij' (boolSign_ne_zero p.s)
    (boolSign_ne_zero p.t)).mp (he.symm.trans he') with ⟨e1, e2, -, -⟩ | ⟨e1, -, -, -⟩
  · exact PairRep.ext e1 h3 (boolSign_injective e2) h4'
  · exact absurd (e1.trans h3.symm) hij

theorem IsShortRep.add_eq {e f : Fin n → ℤ} (hp : p.IsShortRep e f) :
    e + f = Pi.single p.i (boolSign p.s) + Pi.single p.j (boolSign p.t) := by
  rw [hp.2.1, hp.2.2]

theorem IsShortRep.isLong_add {e f : Fin n → ℤ} (hp : p.IsShortRep e f) : IsLong (e + f) := by
  rw [hp.add_eq]
  exact isLong_single_add_single hp.1 _ _

theorem IsMixedRep.add_eq {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) :
    e + f = Pi.single p.i (boolSign p.s) := by
  rw [hp.2.1, hp.2.2, add_assoc, ← Pi.single_add, boolSign_add_boolSign_not, Pi.single_zero,
    add_zero]

theorem IsMixedRep.add_two_nsmul_eq {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) :
    e + 2 • f = Pi.single p.i (boolSign p.s) + Pi.single p.j (boolSign (!p.t)) := by
  have h : boolSign p.t + (boolSign (!p.t) + boolSign (!p.t)) = boolSign (!p.t) := by
    cases p.t <;> rfl
  rw [hp.2.1, hp.2.2, two_nsmul, add_assoc, ← Pi.single_add, ← Pi.single_add, h]

theorem IsMixedRep.isShort_add {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) : IsShort (e + f) := by
  rw [hp.add_eq]
  exact isShort_single _ _

theorem IsMixedRep.isLong_add_two_nsmul {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) :
    IsLong (e + 2 • f) := by
  rw [hp.add_two_nsmul_eq]
  exact isLong_single_add_single hp.1 _ _

theorem IsMixedRep.isLong {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) : IsLong e := by
  rw [hp.2.1]
  exact isLong_single_add_single hp.1 _ _

theorem IsMixedRep.isShort {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) : IsShort f := by
  rw [hp.2.2]
  exact isShort_single _ _

theorem IsMixedRep.dot_eq {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) : e ⬝ᵥ f = -1 := by
  obtain ⟨hij, rfl, rfl⟩ := hp
  rw [add_dotProduct, dot_single_single, dot_single_single, ite_eq_right hij, ite_eq_left rfl,
    zero_add]
  cases p.t <;> rfl

end PairRep

open _root_.Classical in
@[expose] def shortSign (e f : Fin n → ℤ) : ℤ :=
  if h : ∃ p : PairRep n, p.IsShortRep e f then h.choose.shortCoeff else 1

open _root_.Classical in
@[expose] def mixedSign₁ (e f : Fin n → ℤ) : ℤ :=
  if h : ∃ p : PairRep n, p.IsMixedRep e f then h.choose.mixedCoeff₁ else 1

open _root_.Classical in
@[expose] def mixedSign₂ (e f : Fin n → ℤ) : ℤ :=
  if h : ∃ p : PairRep n, p.IsMixedRep e f then h.choose.mixedCoeff₂ else 1

theorem shortSign_eq {p : PairRep n} {e f : Fin n → ℤ} (hp : p.IsShortRep e f) :
    shortSign e f = p.shortCoeff := by
  have h : ∃ p : PairRep n, p.IsShortRep e f := ⟨p, hp⟩
  rw [shortSign, dite_eq_left h, h.choose_spec.unique hp]

theorem mixedSign₁_eq {p : PairRep n} {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) :
    mixedSign₁ e f = p.mixedCoeff₁ := by
  have h : ∃ p : PairRep n, p.IsMixedRep e f := ⟨p, hp⟩
  rw [mixedSign₁, dite_eq_left h, h.choose_spec.unique hp]

theorem mixedSign₂_eq {p : PairRep n} {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) :
    mixedSign₂ e f = p.mixedCoeff₂ := by
  have h : ∃ p : PairRep n, p.IsMixedRep e f := ⟨p, hp⟩
  rw [mixedSign₂, dite_eq_left h, h.choose_spec.unique hp]

theorem natAbs_shortSign (e f : Fin n → ℤ) :
    (shortSign e f).natAbs = 2 ∨ (shortSign e f).natAbs = 1 := by
  unfold shortSign
  split_ifs with h
  · exact Or.inl h.choose.natAbs_shortCoeff
  · exact Or.inr rfl

theorem mixedSign₁_eq_one_or_eq_neg_one (e f : Fin n → ℤ) :
    mixedSign₁ e f = 1 ∨ mixedSign₁ e f = -1 := by
  unfold mixedSign₁
  split_ifs with h
  · exact h.choose.mixedCoeff₁_eq_one_or_eq_neg_one
  · exact Or.inl rfl

theorem mixedSign₂_eq_one_or_eq_neg_one (e f : Fin n → ℤ) :
    mixedSign₂ e f = 1 ∨ mixedSign₂ e f = -1 := by
  unfold mixedSign₂
  split_ifs with h
  · exact h.choose.mixedCoeff₂_eq_one_or_eq_neg_one
  · exact Or.inl rfl

end PairRep

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : OddFrame Q n)

open _root_.Classical in
@[expose] def elt (e : Fin n → ℤ) (c : K) : spinGroup Q :=
  if IsLong e then rootElt F.toHypFrame e c else shortElt F e c

theorem elt_of_isLong {e : Fin n → ℤ} (he : IsLong e) (c : K) :
    elt F e c = rootElt F.toHypFrame e c := by
  rw [elt, ite_eq_left he]

theorem elt_of_isShort {e : Fin n → ℤ} (he : IsShort e) (c : K) :
    elt F e c = shortElt F e c := by
  rw [elt, ite_eq_right he.not_isLong]

theorem elt_of_not {e : Fin n → ℤ} (he : ¬IsRootVec e) (c : K) : elt F e c = 1 := by
  rw [elt, ite_eq_right fun h => he (Or.inl h), shortElt_of_not F fun h => he (Or.inr h)]

theorem elt_zero (e : Fin n → ℤ) : elt F e (0 : K) = 1 := by
  unfold elt
  split_ifs
  · exact rootElt_zero _ e
  · exact shortElt_zero F e

theorem elt_add (e : Fin n → ℤ) (c d : K) : elt F e (c + d) = elt F e c * elt F e d := by
  unfold elt
  split_ifs
  · exact rootElt_add _ e c d
  · exact shortElt_add F e c d

theorem elt_neg (e : Fin n → ℤ) (c : K) : elt F e (-c) = (elt F e c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← elt_add, neg_add_cancel, elt_zero]

theorem elt_injective {e : Fin n → ℤ} (he : IsRootVec e) :
    Function.Injective (elt F e : K → spinGroup Q) := by
  rcases he with he | he
  · intro c d h
    rw [elt_of_isLong F he, elt_of_isLong F he] at h
    exact rootElt_injective _ he h
  · intro c d h
    rw [elt_of_isShort F he, elt_of_isShort F he] at h
    exact shortElt_injective F he h

theorem commute_elt_self (e : Fin n → ℤ) (c d : K) : Commute (elt F e c) (elt F e d) := by
  change _ * _ = _ * _
  rw [← elt_add, ← elt_add, add_comm]

theorem commutator_shortElt_shortElt {p : PairRep n} {e f : Fin n → ℤ} (hp : p.IsShortRep e f)
    (c d : K) :
    ⁅shortElt F e c, shortElt F f d⁆ =
      rootElt F.toHypFrame (e + f) ((shortSign e f : K) * c * d) := by
  rw [shortElt_eq F hp.2.1, shortElt_eq F hp.2.2, F.commutator_shortRoot_shortRoot hp.1,
    rootElt_eq F.toHypFrame hp.1 hp.add_eq, shortSign_eq hp, PairRep.shortCoeff]
  congr 2
  push_cast
  have h := repSign_cast_mul_self (K := K) p.i p.j p.s p.t
  linear_combination (2 * (boolSign p.s : K) * boolSign p.t * c * d) * h

theorem commutator_rootElt_shortElt {p : PairRep n} {e f : Fin n → ℤ} (hp : p.IsMixedRep e f)
    (c d : K) :
    ⁅rootElt F.toHypFrame e c, shortElt F f d⁆ =
      shortElt F (e + f) ((mixedSign₁ e f : K) * c * d) *
        rootElt F.toHypFrame (e + 2 • f) ((mixedSign₂ e f : K) * c * d ^ 2) := by
  rw [rootElt_eq F.toHypFrame hp.1 hp.2.1, shortElt_eq F hp.2.2,
    F.commutator_longRoot_shortRoot hp.1, shortElt_eq F hp.add_eq,
    rootElt_eq F.toHypFrame hp.1 hp.add_two_nsmul_eq, mixedSign₁_eq hp, mixedSign₂_eq hp,
    PairRep.mixedCoeff₁, PairRep.mixedCoeff₂]
  have hs := intCast_mul_self_of_sq (K := K) (boolSign_eq_one_or_eq_neg_one p.s)
  have ht := intCast_mul_self_of_sq (K := K) (boolSign_eq_one_or_eq_neg_one (!p.t))
  have hr := repSign_cast_mul_self (K := K) p.i p.j p.s (!p.t)
  congr 3
  · push_cast
    linear_combination (-(boolSign (!p.t) : K) * repSign p.i p.j p.s p.t * c * d) * hs
  · push_cast
    linear_combination (repSign p.i p.j p.s p.t * c * d ^ 2 : K) * ht -
      (repSign p.i p.j p.s p.t * c * d ^ 2 : K) * hr

theorem commute_shortElt_rootElt_of_isMixedRep {p : PairRep n} {e f : Fin n → ℤ}
    (hp : p.IsMixedRep e f) (c d : K) :
    Commute (shortElt F (e + f) c) (rootElt F.toHypFrame (e + 2 • f) d) := by
  rw [shortElt_eq F hp.add_eq, rootElt_eq F.toHypFrame hp.1 hp.add_two_nsmul_eq]
  exact (F.commute_longRoot_shortRoot_left hp.1 p.s (!p.t) _ _).symm

theorem exists_isShortRep_or_eq {e f : Fin n → ℤ} (he : IsShort e) (hf : IsShort f)
    (hef : e + f ≠ 0) : (∃ p : PairRep n, p.IsShortRep e f) ∨ e = f := by
  obtain ⟨i, s, rfl⟩ := he
  obtain ⟨j, t, rfl⟩ := hf
  by_cases hij : i = j
  · subst hij
    by_cases hst : s = t
    · exact Or.inr (by rw [hst])
    · exfalso
      have ht : t = !s := by cases s <;> cases t <;> simp_all
      apply hef
      rw [ht, ← Pi.single_add, boolSign_add_boolSign_not, Pi.single_zero]
  · exact Or.inl ⟨⟨i, j, s, t⟩, hij, rfl, rfl⟩

theorem exists_isMixedRep_or_commute {e f : Fin n → ℤ} (he : IsLong e) (hf : IsShort f) :
    (∃ p : PairRep n, p.IsMixedRep e f) ∨
      (0 ≤ e ⬝ᵥ f ∧ ∀ c d : K, Commute (rootElt F.toHypFrame e c) (shortElt F f d)) := by
  obtain ⟨k, u, rfl⟩ := hf
  by_cases hk : e k = 0
  ·
    right
    obtain ⟨i, j, hij, s, t, rfl⟩ := he
    have hki : k ≠ i := fun h => by
      subst h
      rw [single_add_single_apply_left hij] at hk
      exact boolSign_ne_zero s hk
    have hkj : k ≠ j := fun h => by
      subst h
      rw [single_add_single_apply_right hij] at hk
      exact boolSign_ne_zero t hk
    refine ⟨?_, fun c d => ?_⟩
    · rw [add_dotProduct, dot_single_single, dot_single_single, ite_eq_right (Ne.symm hki),
        ite_eq_right (Ne.symm hkj), add_zero]
    · rw [rootElt_eq F.toHypFrame hij rfl, shortElt_eq F rfl]
      exact F.commute_longRoot_shortRoot_of_ne hij hki hkj s t u _ _
  · obtain ⟨j, hkj, s, t, he'⟩ := he.exists_eq_of_apply_ne_zero hk
    subst he'
    by_cases hus : u = s
    ·
      subst hus
      right
      refine ⟨?_, fun c d => ?_⟩
      · rw [add_dotProduct, dot_single_single, dot_single_single, ite_eq_left rfl,
          ite_eq_right (Ne.symm hkj), add_zero, boolSign_mul_self]
        norm_num
      · rw [rootElt_eq F.toHypFrame hkj rfl, shortElt_eq F rfl]
        exact F.commute_longRoot_shortRoot_left hkj u t _ _
    ·
      left
      have hu : u = !s := by cases u <;> cases s <;> simp_all
      exact ⟨⟨j, k, t, s⟩, Ne.symm hkj, add_comm _ _, by rw [hu]⟩

theorem neg_one_le_dot_of_isLong {e f : Fin n → ℤ} (he : IsLong e) (hf : IsLong f)
    (hef : e + f ≠ 0) : -1 ≤ e ⬝ᵥ f := by
  have h := one_le_dot_self hef
  have h' := dot_comb 1 1 e f
  simp only [one_smul, Nat.cast_one, one_pow, one_mul, mul_one] at h'
  rw [h', dot_self_of_isLong he, dot_self_of_isLong hf] at h
  omega

theorem classify {e f : Fin n → ℤ} (he : IsRootVec e) (hf : IsRootVec f) (hef : e + f ≠ 0) :
    (IsLong e ∧ IsLong f ∧ IsLong (e + f) ∧ ¬IsRootVec (e + 2 • f) ∧
      ¬IsRootVec (2 • e + f)) ∨
    ((∃ p : PairRep n, p.IsShortRep e f) ∧ ¬IsRootVec (e + 2 • f) ∧
      ¬IsRootVec (2 • e + f)) ∨
    ((∃ p : PairRep n, p.IsMixedRep e f) ∧ ¬IsRootVec (2 • e + f)) ∨
    ((∃ p : PairRep n, p.IsMixedRep f e) ∧ ¬IsRootVec (e + 2 • f)) ∨
    (¬IsRootVec (e + f) ∧ ¬IsRootVec (e + 2 • f) ∧ ¬IsRootVec (2 • e + f) ∧
      ∀ c d : K, Commute (elt F e c) (elt F f d)) := by
  have hc12 := dot_comb 1 2 e f
  have hc21 := dot_comb 2 1 e f
  have hc11 := dot_comb 1 1 e f
  simp only [one_smul, Nat.cast_one, Nat.cast_ofNat, one_pow, one_mul, mul_one] at hc12 hc21 hc11
  rcases he with he | he <;> rcases hf with hf | hf
  ·
    have hC := neg_one_le_dot_of_isLong he hf hef
    have hA := dot_self_of_isLong he
    have hB := dot_self_of_isLong hf
    have h12 : ¬IsRootVec (e + 2 • f) := not_isRootVec_of_dot (by omega) (by omega)
    have h21 : ¬IsRootVec (2 • e + f) := not_isRootVec_of_dot (by omega) (by omega)
    rcases exists_isRep_or_commute F.toHypFrame he hf hef with ⟨p, hp⟩ | ⟨hl, hcomm⟩
    · exact Or.inl ⟨he, hf, hp.isLong_add, h12, h21⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, h12, h21, fun c d => ?_⟩)))
      · rintro (h | h)
        · exact hl h
        · have := dot_self_of_isShort h
          omega
      · rw [elt_of_isLong F he, elt_of_isLong F hf]
        exact hcomm c d
  ·
    have hA := dot_self_of_isLong he
    have hB := dot_self_of_isShort hf
    rcases exists_isMixedRep_or_commute F he hf with ⟨p, hp⟩ | ⟨hC, hcomm⟩
    · have hC := hp.dot_eq
      exact Or.inr (Or.inr (Or.inl ⟨⟨p, hp⟩, not_isRootVec_of_dot (by omega) (by omega)⟩))
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨not_isRootVec_of_dot (by omega) (by omega),
        not_isRootVec_of_dot (by omega) (by omega), not_isRootVec_of_dot (by omega) (by omega),
        fun c d => ?_⟩)))
      rw [elt_of_isLong F he, elt_of_isShort F hf]
      exact hcomm c d
  ·
    have hA := dot_self_of_isShort he
    have hB := dot_self_of_isLong hf
    rcases exists_isMixedRep_or_commute F hf he with ⟨p, hp⟩ | ⟨hC, hcomm⟩
    · have hC := hp.dot_eq
      rw [dotProduct_comm] at hC
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p, hp⟩, not_isRootVec_of_dot (by omega)
        (by omega)⟩)))
    · rw [dotProduct_comm] at hC
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨not_isRootVec_of_dot (by omega) (by omega),
        not_isRootVec_of_dot (by omega) (by omega), not_isRootVec_of_dot (by omega) (by omega),
        fun c d => ?_⟩)))
      rw [elt_of_isShort F he, elt_of_isLong F hf]
      exact (hcomm d c).symm
  ·
    have hA := dot_self_of_isShort he
    have hB := dot_self_of_isShort hf
    rcases exists_isShortRep_or_eq he hf hef with ⟨p, hp⟩ | rfl
    · have hC : e ⬝ᵥ f = 0 := by
        obtain ⟨hij, rfl, rfl⟩ := hp
        rw [dot_single_single, ite_eq_right hij]
      exact Or.inr (Or.inl ⟨⟨p, hp⟩, not_isRootVec_of_dot (by omega) (by omega),
        not_isRootVec_of_dot (by omega) (by omega)⟩)
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨not_isRootVec_of_dot (by omega) (by omega),
        not_isRootVec_of_dot (by omega) (by omega), not_isRootVec_of_dot (by omega) (by omega),
        fun c d => commute_elt_self F e c d⟩)))

end CFSG.LieType.Steinberg.SpinOdd
