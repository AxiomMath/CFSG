module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs

public section

namespace CFSG.OddStandard.Solomon75

open scoped commutatorElement

structure GoodQ (Q : Type) [Group Q] : Prop where
  gen3 : ∀ q : Q, ∃ x y z : Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ q = x * y * z
  center_sq : ∀ z : Q, (∀ g : Q, g * z = z * g) → z * z = 1
  two_mul : ∀ x y : Q, x ^ 4 = 1 → y ^ 4 = 1 → (x * y) ^ 4 = 1
  exp_dvd : ∀ q : Q, q ^ 12 = 1
  two_pow : ∀ q : Q, q ^ 8 = 1 → q ^ 4 = 1
  comm_two : ∀ x y : Q, ⁅x, y⁆ ^ 4 = 1
  noncentral_two : ∃ t h : Q, t ^ 4 = 1 ∧ h ^ 3 = 1 ∧
    ∃ g : Q, g * (t⁻¹ * (h⁻¹ * t * h)) ≠ (t⁻¹ * (h⁻¹ * t * h)) * g
  normal_dich : ∀ d : Q, (∃ g : Q, g * d ≠ d * g) → ∀ q : Q, q ^ 4 = 1 →
    ∃ a b : Q, q = ⁅d, a⁆ * ⁅d, b⁆
  nontriv3 : ∃ h : Q, h ≠ 1 ∧ h ^ 3 = 1
  outer3 : ∀ σ : MulAut Q, σ ^ 3 = 1 → ∃ h : Q, h ^ 3 = 1 ∧ ∀ q, σ q = h * q * h⁻¹

theorem GoodQ.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (h : GoodQ Q) :
    GoodQ Q' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨x, y, z, hx, hy, hz, hq⟩ := h.gen3 (e.symm q)
    refine ⟨e x, e y, e z, ?_, ?_, ?_, ?_⟩
    · rw [← map_pow, hx, map_one]
    · rw [← map_pow, hy, map_one]
    · rw [← map_pow, hz, map_one]
    · rw [← map_mul, ← map_mul, ← hq, MulEquiv.apply_symm_apply]
  · intro z hz
    have := h.center_sq (e.symm z) (fun g => by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (e g))
    have h2 := congrArg e this
    rwa [map_mul, map_one, MulEquiv.apply_symm_apply] at h2
  · intro x y hx hy
    have := h.two_mul (e.symm x) (e.symm y) (by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hx, map_one]) (by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hy, map_one])
    have h2 := congrArg e this
    rwa [map_pow, map_mul, map_one, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  · intro q
    have h2 := congrArg e (h.exp_dvd (e.symm q))
    rwa [map_pow, map_one, MulEquiv.apply_symm_apply] at h2
  · intro q hq
    have hq' : (e.symm q) ^ 8 = 1 := by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hq, map_one]
    have h2 := congrArg e (h.two_pow (e.symm q) hq')
    rwa [map_pow, map_one, MulEquiv.apply_symm_apply] at h2
  · intro x y
    have h2 := congrArg e (h.comm_two (e.symm x) (e.symm y))
    rwa [map_pow, map_one, map_commutatorElement, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply] at h2
  · obtain ⟨t, k, ht, hk, g, hg⟩ := h.noncentral_two
    refine ⟨e t, e k, ?_, ?_, e g, ?_⟩
    · rw [← map_pow, ht, map_one]
    · rw [← map_pow, hk, map_one]
    · intro hc
      apply hg
      apply e.injective
      simpa [map_mul, map_inv] using hc
  · intro d hd q hq
    obtain ⟨g, hg⟩ := hd
    have hd' : ∃ g' : Q, g' * e.symm d ≠ e.symm d * g' := by
      refine ⟨e.symm g, fun hc => hg ?_⟩
      have := congrArg e hc
      simpa [map_mul] using this
    have hq' : (e.symm q) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hq, map_one]
    obtain ⟨a, b, hab⟩ := h.normal_dich (e.symm d) hd' (e.symm q) hq'
    refine ⟨e a, e b, ?_⟩
    have h2 := congrArg e hab
    rwa [MulEquiv.apply_symm_apply, map_mul, map_commutatorElement, map_commutatorElement,
      MulEquiv.apply_symm_apply] at h2
  · obtain ⟨k, hk1, hk3⟩ := h.nontriv3
    refine ⟨e k, ?_, ?_⟩
    · intro hc
      exact hk1 (e.injective (by rw [hc, map_one]))
    · rw [← map_pow, hk3, map_one]
  · intro σ hσ
    have hσ' : ((MulAut.congr e).symm σ) ^ 3 = 1 := by
      rw [← map_pow, hσ, map_one]
    obtain ⟨k, hk3, hk⟩ := h.outer3 _ hσ'
    refine ⟨e k, by rw [← map_pow, hk3, map_one], fun q => ?_⟩
    have := hk (e.symm q)
    have h2 := congrArg e this
    simpa [MulAut.congr] using h2

namespace QModels


@[expose] def dg (n i : ℕ) : ℕ := n / 3 ^ i % 3

@[expose] def cd (a b c d : ℕ) : ℕ := a % 3 + 3 * (b % 3) + 9 * (c % 3) + 27 * (d % 3)

@[expose] def mulN (m n : ℕ) : ℕ :=
  cd (dg m 0 * dg n 0 + dg m 1 * dg n 2) (dg m 0 * dg n 1 + dg m 1 * dg n 3)
    (dg m 2 * dg n 0 + dg m 3 * dg n 2) (dg m 2 * dg n 1 + dg m 3 * dg n 3)

@[expose] def detN (n : ℕ) : ℕ := (dg n 0 * dg n 3 + 2 * (dg n 1 * dg n 2)) % 3

@[expose] def invN (n : ℕ) : ℕ := cd (dg n 3) (2 * dg n 1) (2 * dg n 2) (dg n 0)

@[expose] def ValidN (n : ℕ) : Prop := n < 81 ∧ detN n = 1

instance : DecidablePred ValidN := fun n => inferInstanceAs (Decidable (n < 81 ∧ detN n = 1))

@[expose] def SL23c : Type := {n : Fin 81 // detN n = 1}

instance : DecidableEq SL23c := inferInstanceAs (DecidableEq {n : Fin 81 // detN n = 1})
instance : Fintype SL23c := inferInstanceAs (Fintype {n : Fin 81 // detN n = 1})

theorem mulN_lt (m n : ℕ) : mulN m n < 81 := by
  unfold mulN cd
  omega

theorem det_mulN : ∀ x y : SL23c, detN (mulN x.1 y.1) = 1 := by decide

theorem det_invN : ∀ x : SL23c, detN (invN x.1) = 1 := by decide


theorem invN_lt (n : ℕ) : invN n < 81 := by
  unfold invN cd
  omega

instance : Mul SL23c := ⟨fun x y => ⟨⟨mulN x.1 y.1, mulN_lt _ _⟩, det_mulN x y⟩⟩
instance : One SL23c := ⟨⟨⟨cd 1 0 0 1, by decide⟩, by decide⟩⟩
instance : Inv SL23c := ⟨fun x => ⟨⟨invN x.1, invN_lt _⟩, det_invN x⟩⟩

theorem mul_assoc' : ∀ x y z : SL23c, x * y * z = x * (y * z) := by decide +kernel
theorem one_mul' : ∀ x : SL23c, 1 * x = x := by decide +kernel
theorem mul_one' : ∀ x : SL23c, x * 1 = x := by decide +kernel
theorem inv_mul' : ∀ x : SL23c, x⁻¹ * x = 1 := by decide +kernel

instance : Group SL23c where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul'


open scoped commutatorElement

theorem gen3 : ∀ q : SL23c, ∃ x y z : SL23c, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ q = x * y * z := by
  decide +kernel
theorem center_sq : ∀ z : SL23c, (∀ g : SL23c, g * z = z * g) → z * z = 1 := by decide +kernel
theorem two_mul : ∀ x y : SL23c, x ^ 4 = 1 → y ^ 4 = 1 → (x * y) ^ 4 = 1 := by decide +kernel
theorem exp_dvd : ∀ q : SL23c, q ^ 12 = 1 := by decide +kernel
theorem comm_two : ∀ x y : SL23c, ⁅x, y⁆ ^ 4 = 1 := by decide +kernel
theorem two_pow : ∀ q : SL23c, q ^ 8 = 1 → q ^ 4 = 1 := by decide +kernel
theorem noncentral_two : ∃ t h : SL23c, t ^ 4 = 1 ∧ h ^ 3 = 1 ∧
    ∃ g : SL23c, g * (t⁻¹ * (h⁻¹ * t * h)) ≠ (t⁻¹ * (h⁻¹ * t * h)) * g := by decide +kernel
theorem normal_dich : ∀ d : SL23c, (∃ g : SL23c, g * d ≠ d * g) → ∀ q : SL23c, q ^ 4 = 1 →
    ∃ a b : SL23c, q = ⁅d, a⁆ * ⁅d, b⁆ := by decide +kernel
theorem nontriv3 : ∃ h : SL23c, h ≠ 1 ∧ h ^ 3 = 1 := by decide +kernel


@[expose] def evalW {Q : Type} [Group Q] (a b : Q) (w : List Bool) : Q :=
  (w.map fun x => if x then a else b).prod

theorem map_evalW {Q Q' : Type} [Group Q] [Group Q'] (f : Q →* Q') (a b : Q) (w : List Bool) :
    f (evalW a b w) = evalW (f a) (f b) w := by
  unfold evalW
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  cases x <;> simp

theorem outer3_of_words {Q : Type} [Group Q] (a b : Q) (wordOf : Q → List Bool)
    (hw : ∀ q, evalW a b (wordOf q) = q) (cand : Q → Q → Prop)
    (hcand : ∀ σ : MulAut Q, cand (σ a) (σ b))
    (hdec : ∀ a' b' : Q, cand a' b' →
      evalW a' b' (wordOf (evalW a' b' (wordOf a'))) = a →
      evalW a' b' (wordOf (evalW a' b' (wordOf b'))) = b →
      ∃ h : Q, h ^ 3 = 1 ∧ h * a * h⁻¹ = a' ∧ h * b * h⁻¹ = b') :
    ∀ σ : MulAut Q, σ ^ 3 = 1 → ∃ h : Q, h ^ 3 = 1 ∧ ∀ q, σ q = h * q * h⁻¹ := by
  intro σ hσ
  have hF : ∀ q, σ q = evalW (σ a) (σ b) (wordOf q) := by
    intro q
    have := map_evalW (σ : Q →* Q) a b (wordOf q)
    rw [hw q] at this
    exact this
  have h3 : ∀ q, σ (σ (σ q)) = q := by
    intro q
    have := congrArg (fun τ : MulAut Q => τ q) hσ
    simpa [pow_succ, MulAut.mul_apply] using this
  have e1 : σ (σ (σ a)) = a := h3 a
  have e2 : σ (σ (σ b)) = b := h3 b
  have hσa : σ (σ a) = evalW (σ a) (σ b) (wordOf (σ a)) := hF (σ a)
  have hσb : σ (σ b) = evalW (σ a) (σ b) (wordOf (σ b)) := hF (σ b)
  obtain ⟨h, hh3, hha, hhb⟩ := hdec (σ a) (σ b) (hcand σ)
    (by rw [← hσa, ← hF]; exact e1) (by rw [← hσb, ← hF]; exact e2)
  refine ⟨h, hh3, fun q => ?_⟩
  have hc : ∀ x, (MulAut.conj h) x = h * x * h⁻¹ := fun x => rfl
  have hq : (MulAut.conj h) q = evalW (σ a) (σ b) (wordOf q) := by
    have := map_evalW ((MulAut.conj h : MulAut Q) : Q →* Q) a b (wordOf q)
    rw [hw q] at this
    have e3 : ((MulAut.conj h : MulAut Q) : Q →* Q) a = σ a := by rw [← hha]; rfl
    have e4 : ((MulAut.conj h : MulAut Q) : Q →* Q) b = σ b := by rw [← hhb]; rfl
    rw [e3, e4] at this
    exact this
  rw [hF q, ← hc, hq]

@[expose] def wordTable : Array (List Bool) := #[
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [false, true, true, false],
  [false, true, true],
  [true, false, true, true],
  [],
  [],
  [],
  [true, false, false, true],
  [false, false, true],
  [false, false, true, false],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [true],
  [],
  [],
  [true, true],
  [],
  [],
  [false],
  [],
  [],
  [],
  [true, false],
  [true, true, false],
  [],
  [],
  [],
  [false, false],
  [],
  [true, false, false],
  [],
  [],
  [],
  [],
  [true, true, false, false],
  [],
  [],
  [true, false, true, false],
  [],
  [],
  [false, true, false],
  [],
  [],
  [true, true, false, true, false],
  [],
  [],
  [true, false, true],
  [],
  [false, true],
  [],
  [true, true, false, true],
  [],
  [],
  [],
  [],
  [true, false, true, false, false],
  [false, true, false, false],
  [],
  [],
  [],
  [false, false, true, true],
  []
]

@[expose] def wordOfC (x : SL23c) : List Bool := wordTable.getD x.1.1 []

@[expose] def gA : SL23c := ⟨⟨cd 1 1 0 1, by decide⟩, by decide⟩
@[expose] def gB : SL23c := ⟨⟨cd 1 0 1 1, by decide⟩, by decide⟩

theorem hwC : ∀ q : SL23c, evalW gA gB (wordOfC q) = q := by decide +kernel

@[expose] def candC (a' b' : SL23c) : Prop :=
  a' ^ 3 = 1 ∧ a' ≠ 1 ∧ b' ^ 3 = 1 ∧ b' ≠ 1 ∧ (a' * b') ^ 4 = 1 ∧ (a' * b') ^ 2 ≠ 1

instance : ∀ a' b', Decidable (candC a' b') := fun a' b' => by unfold candC; infer_instance

theorem candC_aut (σ : MulAut SL23c) : candC (σ gA) (σ gB) := by
  have h1 : gA ^ 3 = 1 := by decide +kernel
  have h2 : gA ≠ 1 := by decide +kernel
  have h3 : gB ^ 3 = 1 := by decide +kernel
  have h4 : gB ≠ 1 := by decide +kernel
  have h5 : (gA * gB) ^ 4 = 1 := by decide +kernel
  have h6 : (gA * gB) ^ 2 ≠ 1 := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · intro h; exact h2 (σ.injective (by rw [h, map_one]))
  · rw [← map_pow, h3, map_one]
  · intro h; exact h4 (σ.injective (by rw [h, map_one]))
  · rw [← map_mul, ← map_pow, h5, map_one]
  · intro h; exact h6 (σ.injective (by rw [map_pow, map_mul, h, map_one]))

theorem hdecC : ∀ a' b' : SL23c, candC a' b' →
    evalW a' b' (wordOfC (evalW a' b' (wordOfC a'))) = gA →
    evalW a' b' (wordOfC (evalW a' b' (wordOfC b'))) = gB →
    ∃ h : SL23c, h ^ 3 = 1 ∧ h * gA * h⁻¹ = a' ∧ h * gB * h⁻¹ = b' := by
  decide +kernel

theorem outer3_SL23c :
    ∀ σ : MulAut SL23c, σ ^ 3 = 1 → ∃ h : SL23c, h ^ 3 = 1 ∧ ∀ q, σ q = h * q * h⁻¹ :=
  outer3_of_words gA gB wordOfC hwC candC candC_aut hdecC


@[expose] def omg (v : ℕ) : ℕ := if v = 1 then 2 else if v = 2 then 3 else if v = 3 then 1 else 0

@[expose] def omgPow : ℕ → ℕ → ℕ
  | 0, v => v
  | k + 1, v => omgPow k (omg v)

@[expose] def mulA (m n : ℕ) : ℕ :=
  Nat.xor (m % 4) (omgPow (m / 4) (n % 4)) + 4 * ((m / 4 + n / 4) % 3)

@[expose] def invA (m : ℕ) : ℕ := omgPow ((3 - m / 4) % 3) (m % 4) + 4 * ((3 - m / 4) % 3)

@[expose] def A4c : Type := {_n : Fin 12 // True}

instance : DecidableEq A4c := inferInstanceAs (DecidableEq {_n : Fin 12 // True})
instance : Fintype A4c := inferInstanceAs (Fintype {_n : Fin 12 // True})

theorem mulA_lt : ∀ m n : Fin 12, mulA m n < 12 := by decide +kernel
theorem invA_lt : ∀ m : Fin 12, invA m < 12 := by decide +kernel

instance : Mul A4c := ⟨fun x y => ⟨⟨mulA x.1 y.1, mulA_lt _ _⟩, trivial⟩⟩
instance : One A4c := ⟨⟨(0 : Fin 12), trivial⟩⟩
instance : Inv A4c := ⟨fun x => ⟨⟨invA x.1, invA_lt _⟩, trivial⟩⟩

theorem mulA_assoc : ∀ x y z : A4c, x * y * z = x * (y * z) := by decide +kernel
theorem mulA_one_mul : ∀ x : A4c, 1 * x = x := by decide +kernel
theorem mulA_mul_one : ∀ x : A4c, x * 1 = x := by decide +kernel
theorem mulA_inv_mul : ∀ x : A4c, x⁻¹ * x = 1 := by decide +kernel

instance : Group A4c where
  mul_assoc := mulA_assoc
  one_mul := mulA_one_mul
  mul_one := mulA_mul_one
  inv_mul_cancel := mulA_inv_mul

theorem gen3A : ∀ q : A4c, ∃ x y z : A4c, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ q = x * y * z := by
  decide +kernel
theorem center_sqA : ∀ z : A4c, (∀ g : A4c, g * z = z * g) → z * z = 1 := by decide +kernel
theorem two_mulA : ∀ x y : A4c, x ^ 4 = 1 → y ^ 4 = 1 → (x * y) ^ 4 = 1 := by decide +kernel
theorem exp_dvdA : ∀ q : A4c, q ^ 12 = 1 := by decide +kernel
theorem comm_twoA : ∀ x y : A4c, ⁅x, y⁆ ^ 4 = 1 := by decide +kernel
theorem two_powA : ∀ q : A4c, q ^ 8 = 1 → q ^ 4 = 1 := by decide +kernel
theorem noncentral_twoA : ∃ t h : A4c, t ^ 4 = 1 ∧ h ^ 3 = 1 ∧
    ∃ g : A4c, g * (t⁻¹ * (h⁻¹ * t * h)) ≠ (t⁻¹ * (h⁻¹ * t * h)) * g := by decide +kernel
theorem normal_dichA : ∀ d : A4c, (∃ g : A4c, g * d ≠ d * g) → ∀ q : A4c, q ^ 4 = 1 →
    ∃ a b : A4c, q = ⁅d, a⁆ * ⁅d, b⁆ := by decide +kernel
theorem nontriv3A : ∃ h : A4c, h ≠ 1 ∧ h ^ 3 = 1 := by decide +kernel

@[expose] def wordTableA : Array (List Bool) := #[
  [],
  [false],
  [true, false, true, true],
  [true, true, false, true],
  [true],
  [false, true],
  [true, false],
  [false, true, false],
  [true, true],
  [false, true, true],
  [true, false, true],
  [true, true, false]
]

@[expose] def wordOfA (x : A4c) : List Bool := wordTableA.getD x.1.1 []

@[expose] def gAA : A4c := ⟨(4 : Fin 12), trivial⟩
@[expose] def gBA : A4c := ⟨(1 : Fin 12), trivial⟩

theorem hwA : ∀ q : A4c, evalW gAA gBA (wordOfA q) = q := by decide +kernel

@[expose] def candA (a' b' : A4c) : Prop :=
  a' ^ 3 = 1 ∧ a' ≠ 1 ∧ b' ^ 2 = 1 ∧ b' ≠ 1 ∧ (a' * b') ^ 3 = 1 ∧ a' * b' ≠ 1

instance : ∀ a' b', Decidable (candA a' b') := fun a' b' => by unfold candA; infer_instance

theorem candA_aut (σ : MulAut A4c) : candA (σ gAA) (σ gBA) := by
  have h1 : gAA ^ 3 = 1 := by decide +kernel
  have h2 : gAA ≠ 1 := by decide +kernel
  have h3 : gBA ^ 2 = 1 := by decide +kernel
  have h4 : gBA ≠ 1 := by decide +kernel
  have h5 : (gAA * gBA) ^ 3 = 1 := by decide +kernel
  have h6 : gAA * gBA ≠ 1 := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · intro h; exact h2 (σ.injective (by rw [h, map_one]))
  · rw [← map_pow, h3, map_one]
  · intro h; exact h4 (σ.injective (by rw [h, map_one]))
  · rw [← map_mul, ← map_pow, h5, map_one]
  · intro h; exact h6 (σ.injective (by rw [map_mul, h, map_one]))

theorem hdecA : ∀ a' b' : A4c, candA a' b' →
    evalW a' b' (wordOfA (evalW a' b' (wordOfA a'))) = gAA →
    evalW a' b' (wordOfA (evalW a' b' (wordOfA b'))) = gBA →
    ∃ h : A4c, h ^ 3 = 1 ∧ h * gAA * h⁻¹ = a' ∧ h * gBA * h⁻¹ = b' := by
  decide +kernel

theorem outer3_A4c : ∀ σ : MulAut A4c, σ ^ 3 = 1 → ∃ h : A4c, h ^ 3 = 1 ∧ ∀ q, σ q = h * q * h⁻¹ :=
  outer3_of_words gAA gBA wordOfA hwA candA candA_aut hdecA


theorem goodQ_SL23c : GoodQ SL23c :=
  ⟨gen3, center_sq, two_mul, exp_dvd, two_pow, comm_two, noncentral_two, normal_dich, nontriv3,
    outer3_SL23c⟩

theorem goodQ_A4c : GoodQ A4c :=
  ⟨gen3A, center_sqA, two_mulA, exp_dvdA, two_powA, comm_twoA, noncentral_twoA, normal_dichA,
    nontriv3A, outer3_A4c⟩

theorem det_toSL : ∀ x : SL23c, ((dg x.1 0 : ℕ) : ZMod 3) * (dg x.1 3 : ℕ) -
    ((dg x.1 1 : ℕ) : ZMod 3) * (dg x.1 2 : ℕ) = 1 := by decide +kernel

@[expose] def toSL (x : SL23c) : SL23 :=
  ⟨!![((dg x.1 0 : ℕ) : ZMod 3), ((dg x.1 1 : ℕ) : ZMod 3);
      ((dg x.1 2 : ℕ) : ZMod 3), ((dg x.1 3 : ℕ) : ZMod 3)], by
    rw [Matrix.det_fin_two_of]
    exact det_toSL x⟩

theorem toSL_mul : ∀ x y : SL23c, toSL (x * y) = toSL x * toSL y := by decide +kernel

theorem toSL_inj : ∀ x y : SL23c, toSL x = toSL y → x = y := by decide +kernel

theorem card_SL23 : Fintype.card SL23 = Fintype.card SL23c := by decide +kernel

@[expose] noncomputable def equivSL : SL23c ≃* SL23 :=
  MulEquiv.ofBijective
    ({ toFun := toSL
       map_one' := by decide +kernel
       map_mul' := toSL_mul } : SL23c →* SL23)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun x y h => toSL_inj x y h, card_SL23.symm⟩)


@[expose] def affF (n : Fin 12) (y : Fin 4) : Fin 4 :=
  ⟨Nat.xor (n.1 % 4) (omgPow (n.1 / 4) y.1) % 4, Nat.mod_lt _ (by decide)⟩

@[expose] def affInv (n : Fin 12) (z : Fin 4) : Fin 4 :=
  ⟨omgPow ((3 - n.1 / 4) % 3) (Nat.xor (n.1 % 4) z.1 % 4) % 4, Nat.mod_lt _ (by decide)⟩

theorem aff_left : ∀ n y, affInv n (affF n y) = y := by decide +kernel
theorem aff_right : ∀ n z, affF n (affInv n z) = z := by decide +kernel

@[expose] def affPerm (n : Fin 12) : Equiv.Perm (Fin 4) :=
  ⟨affF n, affInv n, aff_left n, aff_right n⟩

theorem aff_even : ∀ n : Fin 12, affPerm n ∈ alternatingGroup (Fin 4) := by
  intro n
  rw [Equiv.Perm.mem_alternatingGroup]
  revert n
  decide +kernel

@[expose] def toA4 (x : A4c) : A4 := ⟨affPerm x.1, aff_even x.1⟩

theorem toA4_mul : ∀ x y : A4c, toA4 (x * y) = toA4 x * toA4 y := by decide +kernel

theorem toA4_inj : ∀ x y : A4c, toA4 x = toA4 y → x = y := by decide +kernel

theorem card_A4 : Fintype.card A4 = Fintype.card A4c := by decide +kernel

@[expose] noncomputable def equivA4 : A4c ≃* A4 :=
  MulEquiv.ofBijective
    ({ toFun := toA4
       map_one' := by decide +kernel
       map_mul' := toA4_mul } : A4c →* A4)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun x y h => toA4_inj x y h, card_A4.symm⟩)

end QModels

theorem goodQ_SL23 : GoodQ SL23 := GoodQ.of_mulEquiv QModels.equivSL QModels.goodQ_SL23c

theorem goodQ_A4 : GoodQ A4 := GoodQ.of_mulEquiv QModels.equivA4 QModels.goodQ_A4c

end CFSG.OddStandard.Solomon75
