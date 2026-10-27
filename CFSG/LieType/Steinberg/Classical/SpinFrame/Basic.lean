module

public import CFSG.LieType.Universal.Spin.Datum

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinFrame

open CFSG.LieType.Universal.Spin CliffordAlgebra QuadraticMap

section Vectors

variable {n : ℕ}

@[expose] def IsLong (e : Fin n → ℤ) : Prop :=
  ∃ (i j : Fin n) (_ : i ≠ j) (s t : Bool), e = Pi.single i (boolSign s) + Pi.single j (boolSign t)

theorem isLong_single_add_single {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    IsLong (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) :=
  ⟨i, j, hij, s, t, rfl⟩

theorem single_add_single_apply_left {i j : Fin n} (hij : i ≠ j) (a b : ℤ) :
    (Pi.single i a + Pi.single j b : Fin n → ℤ) i = a := by
  rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]

theorem single_add_single_apply_right {i j : Fin n} (hij : i ≠ j) (a b : ℤ) :
    (Pi.single i a + Pi.single j b : Fin n → ℤ) j = b := by
  rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), zero_add]

theorem single_add_single_apply_of_ne {i j m : Fin n} (hmi : m ≠ i) (hmj : m ≠ j) (a b : ℤ) :
    (Pi.single i a + Pi.single j b : Fin n → ℤ) m = 0 := by
  rw [Pi.add_apply, Pi.single_eq_of_ne hmi, Pi.single_eq_of_ne hmj, add_zero]

theorem eq_or_eq_of_single_add_single_apply_ne_zero {i j m : Fin n} {a b : ℤ}
    (h : (Pi.single i a + Pi.single j b : Fin n → ℤ) m ≠ 0) : m = i ∨ m = j := by
  by_contra hm
  push Not at hm
  exact h (single_add_single_apply_of_ne hm.1 hm.2 a b)

theorem boolSign_add_boolSign_not (s : Bool) : boolSign s + boolSign (!s) = 0 := by
  cases s <;> rfl

theorem boolSign_mul_self (s : Bool) : boolSign s * boolSign s = 1 := by
  cases s <;> rfl

theorem boolSign_eq_boolSign_iff {s t : Bool} : boolSign s = boolSign t ↔ s = t :=
  boolSign_injective.eq_iff

theorem IsLong.apply_mem {e : Fin n → ℤ} (he : IsLong e) (m : Fin n) :
    e m = 0 ∨ e m = 1 ∨ e m = -1 := by
  obtain ⟨i, j, hij, s, t, rfl⟩ := he
  by_cases hmi : m = i
  · subst hmi
    rw [single_add_single_apply_left hij]
    exact Or.inr (boolSign_eq_one_or_eq_neg_one s)
  · by_cases hmj : m = j
    · subst hmj
      rw [single_add_single_apply_right hij]
      exact Or.inr (boolSign_eq_one_or_eq_neg_one t)
    · exact Or.inl (single_add_single_apply_of_ne hmi hmj _ _)

theorem IsLong.ne_zero {e : Fin n → ℤ} (he : IsLong e) : e ≠ 0 := by
  obtain ⟨i, j, hij, s, t, rfl⟩ := he
  intro h
  have := congrFun h i
  rw [single_add_single_apply_left hij, Pi.zero_apply] at this
  exact boolSign_ne_zero s this

theorem IsLong.exists_eq_of_apply_ne_zero {e : Fin n → ℤ} (he : IsLong e) {m : Fin n}
    (hm : e m ≠ 0) :
    ∃ (j : Fin n) (_ : m ≠ j) (s t : Bool),
      e = Pi.single m (boolSign s) + Pi.single j (boolSign t) := by
  obtain ⟨i, j, hij, s, t, rfl⟩ := he
  rcases eq_or_eq_of_single_add_single_apply_ne_zero hm with rfl | rfl
  · exact ⟨j, hij, s, t, rfl⟩
  · exact ⟨i, Ne.symm hij, t, s, add_comm _ _⟩

theorem eq_of_single_add_single_eq_of_lt {i j i' j' : Fin n} (hij : i < j) (hij' : i' < j')
    {s t s' t' : Bool}
    (h : (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) =
      Pi.single i' (boolSign s') + Pi.single j' (boolSign t')) :
    i = i' ∧ j = j' ∧ s = s' ∧ t = t' := by
  rcases (single_add_single_eq_iff hij.ne hij'.ne (boolSign_ne_zero s)
    (boolSign_ne_zero t)).mp h with ⟨h1, h2, h3, h4⟩ | ⟨h1, -, h3, -⟩
  · exact ⟨h1, h3, boolSign_injective h2, boolSign_injective h4⟩
  · subst h1 h3
    exact absurd (hij.trans hij') (lt_irrefl _)

@[expose] def repSign (i j : Fin n) (s t : Bool) : ℤ := if i < j then boolSign s else -boolSign t

theorem repSign_of_lt {i j : Fin n} (h : i < j) (s t : Bool) : repSign i j s t = boolSign s := by
  rw [repSign, ite_eq_left h]

theorem repSign_of_not_lt {i j : Fin n} (h : ¬i < j) (s t : Bool) :
    repSign i j s t = -boolSign t := by
  rw [repSign, ite_eq_right h]

theorem repSign_eq_one_or_eq_neg_one (i j : Fin n) (s t : Bool) :
    repSign i j s t = 1 ∨ repSign i j s t = -1 := by
  unfold repSign
  split_ifs
  · exact boolSign_eq_one_or_eq_neg_one s
  · rcases boolSign_eq_one_or_eq_neg_one t with h | h <;> rw [h] <;> simp

theorem repSign_mul_self (i j : Fin n) (s t : Bool) : repSign i j s t * repSign i j s t = 1 := by
  rcases repSign_eq_one_or_eq_neg_one i j s t with h | h <;> rw [h] <;> rfl

theorem repSign_swap {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    repSign j i t s = -repSign i j s t := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [repSign_of_not_lt (lt_asymm h), repSign_of_lt h]
  · rw [repSign_of_lt h, repSign_of_not_lt (lt_asymm h), neg_neg]

end Vectors

section Field

variable {K : Type*} [Field K]

theorem intCast_mul_self_of_sq {z : ℤ} (hz : z = 1 ∨ z = -1) : (z : K) * z = 1 := by
  rcases hz with rfl | rfl <;> simp

theorem intCast_ne_zero_of_sq {z : ℤ} (hz : z = 1 ∨ z = -1) : (z : K) ≠ 0 := by
  rcases hz with rfl | rfl <;> simp

theorem repSign_cast_mul_self {n : ℕ} (i j : Fin n) (s t : Bool) :
    (repSign i j s t : K) * repSign i j s t = 1 :=
  intCast_mul_self_of_sq (repSign_eq_one_or_eq_neg_one i j s t)

end Field

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : HypFrame Q n)

theorem longRoot_congr {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') {s t s' t' : Bool} (hs : s = s') (ht : t = t') :
    F.longRoot hij s t = F.longRoot hij' s' t' := by
  subst hi hj hs ht
  rfl

open _root_.Classical in
@[expose] def rootElt (e : Fin n → ℤ) (c : K) : spinGroup Q :=
  if h : ∃ p : Fin n × Fin n × Bool × Bool, p.1 < p.2.1 ∧
      e = Pi.single p.1 (boolSign p.2.2.1) + Pi.single p.2.1 (boolSign p.2.2.2) then
    F.longRoot (ne_of_lt h.choose_spec.1) h.choose.2.2.1 h.choose.2.2.2
      (.ofAdd ((boolSign h.choose.2.2.1 : K) * c))
  else 1

theorem rootElt_eq_of_lt {e : Fin n → ℤ} {i j : Fin n} (hij : i < j) {s t : Bool}
    (he : e = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (c : K) :
    rootElt F e c = F.longRoot hij.ne s t (.ofAdd ((boolSign s : K) * c)) := by
  have hex : ∃ p : Fin n × Fin n × Bool × Bool, p.1 < p.2.1 ∧
      e = Pi.single p.1 (boolSign p.2.2.1) + Pi.single p.2.1 (boolSign p.2.2.2) :=
    ⟨(i, j, s, t), hij, he⟩
  rw [rootElt, dite_eq_left hex]
  obtain ⟨h1, h2, h3, h4⟩ :=
    eq_of_single_add_single_eq_of_lt hex.choose_spec.1 hij (hex.choose_spec.2.symm.trans he)
  rw [longRoot_congr F _ hij.ne h1 h2 h3 h4, h3]

theorem rootElt_eq {e : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) {s t : Bool}
    (he : e = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (c : K) :
    rootElt F e c = F.longRoot hij s t (.ofAdd ((repSign i j s t : K) * c)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [rootElt_eq_of_lt F h he, repSign_of_lt h]
  · rw [rootElt_eq_of_lt F h (he.trans (add_comm _ _)), repSign_of_not_lt (lt_asymm h),
      F.longRoot_swap h.ne t s]
    congr 2
    push_cast
    ring

theorem longRoot_eq_rootElt {e : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) {s t : Bool}
    (he : e = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (c : K) :
    F.longRoot hij s t (.ofAdd c) = rootElt F e ((repSign i j s t : K) * c) := by
  rw [rootElt_eq F hij he, ← mul_assoc, repSign_cast_mul_self, one_mul]

theorem rootElt_of_not {e : Fin n → ℤ} (he : ¬IsLong e) (c : K) : rootElt F e c = 1 := by
  rw [rootElt, dite_eq_right fun ⟨_, hp, h⟩ => he ⟨_, _, ne_of_lt hp, _, _, h⟩]

theorem rootElt_zero (e : Fin n → ℤ) : rootElt F e (0 : K) = 1 := by
  by_cases he : IsLong e
  · obtain ⟨i, j, hij, s, t, he⟩ := he
    rw [rootElt_eq F hij he, mul_zero, ofAdd_zero, map_one]
  · exact rootElt_of_not F he 0

theorem rootElt_add (e : Fin n → ℤ) (c d : K) :
    rootElt F e (c + d) = rootElt F e c * rootElt F e d := by
  by_cases he : IsLong e
  · obtain ⟨i, j, hij, s, t, he⟩ := he
    rw [rootElt_eq F hij he, rootElt_eq F hij he, rootElt_eq F hij he, ← map_mul, ← ofAdd_add,
      mul_add]
  · rw [rootElt_of_not F he, rootElt_of_not F he, rootElt_of_not F he, mul_one]

theorem rootElt_neg (e : Fin n → ℤ) (c : K) : rootElt F e (-c) = (rootElt F e c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootElt_add, neg_add_cancel, rootElt_zero]

theorem rootElt_injective {e : Fin n → ℤ} (he : IsLong e) :
    Function.Injective (rootElt F e : K → spinGroup Q) := by
  obtain ⟨i, j, hij, s, t, he⟩ := he
  intro c d h
  rw [rootElt_eq F hij he, rootElt_eq F hij he] at h
  have h' := congrArg Multiplicative.toAdd (F.longRoot_injective hij s t h)
  simp only [toAdd_ofAdd] at h'
  exact mul_left_cancel₀ (intCast_ne_zero_of_sq (repSign_eq_one_or_eq_neg_one i j s t)) h'

theorem exists_rootElt_eq_iff {e : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) {s t : Bool}
    (he : e = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (g : spinGroup Q) :
    g ∈ (F.longRoot hij s t).range ↔ ∃ c : K, rootElt F e c = g := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨(repSign i j s t : K) * Multiplicative.toAdd c, ?_⟩
    rw [← longRoot_eq_rootElt F hij he, ofAdd_toAdd]
  · rintro ⟨c, rfl⟩
    rw [rootElt_eq F hij he]
    exact ⟨_, rfl⟩

end CFSG.LieType.Steinberg.SpinFrame
