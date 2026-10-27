module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Heis
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public noncomputable section

open scoped commutatorElement

namespace CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3

@[ext] structure UHeis {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) where
  a : K
  c : K
  hc : c + h.bar c + a * h.bar a = 0

namespace UHeis

section Group

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

instance : Mul (UHeis h) :=
  ⟨fun x y => ⟨x.a + y.a, x.c + y.c - x.a * h.bar y.a, by
    simp only [map_add, map_sub, map_mul, h.bar_bar]
    linear_combination x.hc + y.hc⟩⟩

instance : One (UHeis h) := ⟨⟨0, 0, by simp⟩⟩

instance : Inv (UHeis h) :=
  ⟨fun x => ⟨-x.a, h.bar x.c, by
    simp only [map_neg, h.bar_bar]
    linear_combination x.hc⟩⟩

@[simp] theorem mul_a (x y : UHeis h) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_c (x y : UHeis h) : (x * y).c = x.c + y.c - x.a * h.bar y.a := rfl
@[simp] theorem one_a : (1 : UHeis h).a = 0 := rfl
@[simp] theorem one_c : (1 : UHeis h).c = 0 := rfl
@[simp] theorem inv_a (x : UHeis h) : (x⁻¹).a = -x.a := rfl
@[simp] theorem inv_c (x : UHeis h) : (x⁻¹).c = h.bar x.c := rfl

instance : Group (UHeis h) :=
  Group.ofLeftAxioms
    (fun x y z => by
      ext
      · simp only [mul_a]; ring
      · simp only [mul_a, mul_c, map_add]; ring)
    (fun x => by ext <;> simp)
    (fun x => by
      ext
      · simp only [mul_a, inv_a, one_a]; ring
      · simp only [mul_c, inv_a, inv_c, one_c]
        linear_combination x.hc)

theorem commutator_a (x y : UHeis h) : (⁅x, y⁆).a = 0 := by
  rw [commutatorElement_def]
  simp only [mul_a, inv_a]
  ring

theorem commutator_c (x y : UHeis h) :
    (⁅x, y⁆).c = y.a * h.bar x.a - x.a * h.bar y.a := by
  rw [commutatorElement_def]
  simp only [mul_a, mul_c, inv_a, inv_c, map_neg]
  linear_combination x.hc + y.hc

theorem pow_a (x : UHeis h) (k : ℕ) : (x ^ k).a = k * x.a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; simp [ih]; ring

theorem pow_c (x : UHeis h) (k : ℕ) :
    (x ^ k).c = k * x.c - (Nat.choose k 2 : K) * (x.a * h.bar x.a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    simp only [mul_c, ih, pow_a]
    rw [Nat.choose_succ_succ k 1]
    push_cast
    simp [Nat.choose_one_right]
    ring

theorem pow_prime_eq_one (hp2 : p ≠ 2) (x : UHeis h) : x ^ p = 1 := by
  have : CharP K p := h.charP
  have hch : (Nat.choose p 2 : K) = 0 :=
    (CharP.cast_eq_zero_iff K p _).mpr
      (h.prime.dvd_choose_self (by norm_num) (by have := h.prime.two_le; omega))
  ext
  · simp [pow_a]
  · simp [pow_c, hch]

theorem exists_c (a : K) : ∃ c : K, c + h.bar c + a * h.bar a = 0 := by
  obtain ⟨c, hc⟩ := h.traceLin_surjective ⟨-(a * h.bar a), by
    rw [UnitaryFieldData.mem_fixedField, map_neg, map_mul, h.bar_bar, mul_comm]⟩
  have := congrArg Subtype.val hc
  refine ⟨c, ?_⟩
  simp only [UnitaryFieldData.coe_traceLin, UnitaryFieldData.trace] at this
  linear_combination this

theorem mem_center {x : UHeis h} : x ∈ Subgroup.center (UHeis h) ↔ x.a = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hx
    by_contra hxa
    obtain ⟨τ, hτ⟩ := h.exists_bar_ne
    obtain ⟨c, hc⟩ := exists_c (h := h) (x.a * τ)
    have hxy := congrArg UHeis.c (hx ⟨x.a * τ, c, hc⟩)
    simp only [mul_c, map_mul] at hxy
    have hb : h.bar x.a ≠ 0 := (map_ne_zero h.bar).mpr hxa
    have e : (x.a * h.bar x.a) * (τ - h.bar τ) = 0 := by linear_combination -hxy
    rcases mul_eq_zero.mp e with h1 | h1
    · exact mul_ne_zero hxa hb h1
    · exact hτ (by linear_combination -h1)
  · intro ha g
    ext
    · simp only [mul_a]; ring
    · simp only [mul_c, ha, map_zero, mul_zero, sub_zero]; ring

theorem commutator_eq_center :
    ⁅(⊤ : Subgroup (UHeis h)), ⊤⁆ = Subgroup.center (UHeis h) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x _ y _
    rw [mem_center]
    exact commutator_a x y
  · intro z hz
    rw [mem_center] at hz
    have hz0 : h.trace z.c = 0 := by
      have := z.hc
      rw [hz] at this
      simp only [zero_mul, add_zero] at this
      exact this
    obtain ⟨t, ht⟩ : z.c ∈ h.barSub.range := by
      rw [h.range_barSub]
      exact (h.mem_traceZero).mpr hz0
    obtain ⟨c₁, hc₁⟩ := exists_c (h := h) 1
    obtain ⟨c₂, hc₂⟩ := exists_c (h := h) (-t)
    have : z = ⁅(⟨1, c₁, hc₁⟩ : UHeis h), ⟨-t, c₂, hc₂⟩⁆ := by
      ext
      · rw [commutator_a, hz]
      · rw [commutator_c]
        simp only [map_one, mul_one, one_mul, map_neg]
        rw [UnitaryFieldData.barSub_apply] at ht
        linear_combination -ht
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end Group

section Card

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

instance (h : UnitaryFieldData p f K) : Finite (UHeis h) := by
  have := h.finite
  exact Finite.of_injective (fun x : UHeis h => (x.a, x.c)) (fun x y hxy => by
    rw [Prod.mk.injEq] at hxy
    exact UHeis.ext hxy.1 hxy.2)

theorem card_eq (h : UnitaryFieldData p f K) : Nat.card (UHeis h) = (p ^ f) ^ 3 := by
  have := h.finite
  have := Fintype.ofFinite K
  let e : UHeis h ≃ {q : K × K // q.2 + h.bar q.2 + q.1 * h.bar q.1 = 0} :=
    { toFun := fun x => ⟨(x.a, x.c), x.hc⟩
      invFun := fun q => ⟨q.1.1, q.1.2, q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfib : ∀ a : K, Nat.card {c : K // c + h.bar c + a * h.bar a = 0} = p ^ f := fun a => by
    have hh := card_trace_eq h (m := -(a * h.bar a))
      (by rw [map_neg, map_mul, h.bar_bar, mul_comm])
    rw [← hh]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => by
      constructor <;> intro hc <;> linear_combination hc)
  rw [Nat.card_congr e, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    fun (a c : K) => c + h.bar c + a * h.bar a = 0), Nat.card_sigma,
    Finset.sum_congr rfl fun a _ => hfib a, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, h.card_eq_sq, smul_eq_mul]
  ring

def centerEquiv : Subgroup.center (UHeis h) ≃ h.traceZero where
  toFun z := ⟨z.1.c, by
    have ha := mem_center.mp z.2
    have hc := z.1.hc
    rw [ha] at hc
    rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace]
    simpa using hc⟩
  invFun γ := ⟨⟨0, γ.1, by
    have := (UnitaryFieldData.mem_traceZero h).mp γ.2
    simpa [UnitaryFieldData.trace] using this⟩, mem_center.mpr rfl⟩
  left_inv z := by
    apply Subtype.ext
    obtain ⟨z, hz⟩ := z
    have ha := mem_center.mp hz
    ext <;> simp [ha]
  right_inv γ := rfl

theorem card_center (h : UnitaryFieldData p f K) :
    Nat.card (Subgroup.center (UHeis h)) = p ^ f :=
  (Nat.card_congr centerEquiv).trans h.card_traceZero

end Card

section Bound

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem exists_line (E : Subgroup (UHeis h)) (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ a₀ c₀ : K, c₀ + h.bar c₀ + a₀ * h.bar a₀ = 0 ∧
      ∀ x ∈ E, ∃ t : K, h.bar t = t ∧ x.a = t * a₀ := by
  by_cases hne : ∃ x₀ ∈ E, x₀.a ≠ 0
  · obtain ⟨x₀, hx₀, hne⟩ := hne
    refine ⟨x₀.a, x₀.c, x₀.hc, fun x hx => ⟨x.a / x₀.a, ?_, ?_⟩⟩
    · have hc := congrArg UHeis.c (hE x hx x₀ hx₀)
      simp only [mul_c] at hc
      have key : x₀.a * h.bar x.a = x.a * h.bar x₀.a := by linear_combination hc
      have hb : h.bar x₀.a ≠ 0 := (map_ne_zero h.bar).mpr hne
      rw [map_div₀]
      field_simp
      linear_combination key
    · field_simp
  · push Not at hne
    exact ⟨0, 0, by simp, fun x hx => ⟨0, by simp, by simpa using hne x hx⟩⟩

theorem card_le_sq (E : Subgroup (UHeis h)) (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ (p ^ f) ^ 2 := by
  have := h.finite
  obtain ⟨a₀, c₀, hc₀, hv⟩ := exists_line E hE
  choose t ht ha using hv
  have hmem : ∀ x : E, h.trace (x.1.c - t x.1 x.2 ^ 2 * c₀) = 0 := fun x => by
    have hxc := x.1.hc
    rw [ha x.1 x.2, map_mul, ht x.1 x.2] at hxc
    simp only [UnitaryFieldData.trace, map_sub, map_mul, map_pow, ht x.1 x.2]
    linear_combination hxc - t x.1 x.2 ^ 2 * hc₀
  let φ : E → h.fixedField × h.traceZero := fun x =>
    (⟨t x.1 x.2, (UnitaryFieldData.mem_fixedField h).mpr (ht x.1 x.2)⟩,
      ⟨x.1.c - t x.1 x.2 ^ 2 * c₀, (UnitaryFieldData.mem_traceZero h).mpr (hmem x)⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    apply Subtype.ext
    ext
    · rw [ha x.1 x.2, ha y.1 y.2, h1]
    · rw [h1] at h2
      linear_combination h2
  have := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, h.card_fixedField, h.card_traceZero, ← sq] at this

theorem le_index (E : Subgroup (UHeis h)) (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    p ^ f ≤ E.index := by
  have h1 := card_le_sq E hE
  have h2 := E.index_mul_card
  rw [card_eq h] at h2
  have hq : 0 < p ^ f := pow_pos h.prime.pos f
  have : (p ^ f) ^ 2 * p ^ f ≤ (p ^ f) ^ 2 * E.index := by
    calc (p ^ f) ^ 2 * p ^ f = (p ^ f) ^ 3 := by ring
      _ = E.index * Nat.card E := h2.symm
      _ ≤ E.index * (p ^ f) ^ 2 := Nat.mul_le_mul_left _ h1
      _ = (p ^ f) ^ 2 * E.index := by ring
  exact Nat.le_of_mul_le_mul_left this (by positivity)

end Bound

end UHeis

theorem frattini_eq_commutator_of_exponent {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hQp : IsPGroup p G) (hexp : ∀ x : G, x ^ p = 1) : frattini G = _root_.commutator G := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p G) := ⟨hQp⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (hy | ⟨x, rfl⟩)
    · exact hy
    · show x ^ p ∈ _root_.commutator G
      rw [hexp x]
      exact one_mem _
  · exact fun y hy => Subgroup.subset_closure (Or.inl hy)

theorem UHeis.specialP {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    SpecialP p f (UHeis h) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hpg : IsPGroup p (UHeis h) :=
    IsPGroup.of_card (n := f * 3) (by rw [UHeis.card_eq h, pow_mul])
  refine ⟨fun E hE => ?_, UHeis.commutator_eq_center.symm, ?_, ?_, ?_⟩
  · have := hE.toIsMulCommutative
    have hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
    refine ⟨UHeis.le_index E hc, ?_⟩
    rw [pow_mul']
    exact UHeis.card_le_sq E hc
  · rw [frattini_eq_commutator_of_exponent h.prime hpg (UHeis.pow_prime_eq_one hp2), commutator_def,
      UHeis.commutator_eq_center]
  · exact
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
          Subtype.ext (UHeis.pow_prime_eq_one hp2 g.1) }
  · exact UHeis.card_center h

end CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3
