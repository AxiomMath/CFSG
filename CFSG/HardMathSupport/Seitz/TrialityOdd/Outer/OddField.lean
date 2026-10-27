module

public import CFSG.RankThree.PartOne.SEITZ8.D4Field
import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ8
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem card_fixedField_gen {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ ℓ ^ f) :
    Nat.card (fixedField σ) = ℓ ^ f := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  obtain ⟨σ₀, -, -, -, -, k, hk, hkc, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 hℓ hf K hK
  have hfk : fixedField σ = k := by
    apply SetLike.coe_injective
    rw [hk]
    ext c
    simp [fixedField, RingHom.eqLocusField, hσ]
  rw [hfk]
  exact hkc

theorem sigma_pow_on_fix_gen {ℓ f0 p : ℕ} {k : Subfield K} (hk : Nat.card k = ℓ ^ (3 * f0))
    {a : K} (ha : a ∈ k) : a ^ ℓ ^ (f0 * p) = a ^ (ℓ ^ f0) ^ (p % 3) := by
  have h1 : a ^ ℓ ^ (3 * f0) = a :=
    CFSG.RankThree.Chevalley.SteinbergBT.pow_card_eq_self_of_mem hk ha
  have h2 : ∀ m : ℕ, a ^ (ℓ ^ (3 * f0)) ^ m = a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, h1]
  have e : ℓ ^ (f0 * p) = (ℓ ^ (3 * f0)) ^ (p / 3) * (ℓ ^ f0) ^ (p % 3) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    calc f0 * p = f0 * (3 * (p / 3) + p % 3) := by rw [Nat.div_add_mod]
      _ = 3 * f0 * (p / 3) + f0 * (p % 3) := by ring
  rw [e, pow_mul, h2]

theorem field_data_odd {ℓ f0 p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp5 : 5 ≤ p) (hf0 : 1 ≤ f0)
    (hK : Nat.card K = ℓ ^ (3 * f0 * p)) {σ δ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ ℓ ^ (f0 * p)) (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * f0)) :
    ∃ (k : Subfield K) (F0 : Subfield (fixedField σ.toRingHom)),
      (∀ c ∈ k, δ c = c) ∧ Rat3 σ.toRingHom k ∧
      (∀ c : fixedField σ.toRingHom, c ∈ F0 ↔ (c : K) ∈ k) ∧
      Nat.card (fixedField σ.toRingHom) = Nat.card F0 ^ p ∧
      (∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a}) := by
  classical
  have hp3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨-, -, -, hk, hord⟩ := CFSG.RankThree.Chevalley.triality_canonical_field_facts
    hℓ hf0 hp.two_le hp3 hK hσ hδ
  set k : Subfield K := fixSubfield δ with hkdef
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have hQ : 2 ≤ ℓ ^ f0 := by
    calc 2 ≤ ℓ := hℓ2
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f0 := Nat.pow_le_pow_right (by omega) hf0
  have hcardF : Nat.card (fixedField σ.toRingHom) = ℓ ^ (f0 * p) :=
    card_fixedField_gen hℓ (by nlinarith) (by rw [hK, ← pow_mul]; congr 1; ring) (fun c => hσ c)
  set F0 : Subfield (fixedField σ.toRingHom) := k.comap (fixedField σ.toRingHom).subtype
    with hF0def
  have hF0mem : ∀ c : fixedField σ.toRingHom, c ∈ F0 ↔ (c : K) ∈ k := fun c => Iff.rfl
  set σ0 := fixSubfieldRestrict σ δ with hσ0
  have hS := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ
    (by omega : 1 ≤ 3 * f0) hk σ0).2
  rw [hord, Nat.mul_div_cancel_left f0 (by norm_num : 0 < 3)] at hS
  have hF0card : Nat.card F0 = ℓ ^ f0 := by
    rw [← hS]
    exact Nat.card_congr ⟨fun x => ⟨⟨x.1.1, x.2⟩, Subtype.ext x.1.2⟩,
      fun y => ⟨⟨y.1.1, congrArg Subtype.val y.2⟩, y.1.2⟩, fun x => rfl, fun y => rfl⟩
  have hcard : Nat.card (fixedField σ.toRingHom) = Nat.card F0 ^ p := by
    rw [hcardF, hF0card, ← pow_mul]
  have hstab : ∀ a ∈ k, σ.toRingHom a ∈ k := fun a ha => by
    have ha' : δ a = a := ha
    have e : σ a = a ^ ℓ ^ (f0 * p) := hσ a
    show δ (σ a) = σ a
    rw [e, map_pow, ha']
  have hkcard : Nat.card k = (ℓ ^ f0) ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    omega
  have hσk : ∀ a : k, (RingHom.restrict σ.toRingHom k k hstab) a = a ^ (ℓ ^ f0) ^ (p % 3) := by
    intro a
    apply Subtype.ext
    show σ (a : K) = ((a ^ (ℓ ^ f0) ^ (p % 3) : k) : K)
    rw [hσ, sigma_pow_on_fix_gen hk a.2]
    rfl
  have hind : MonoInd k (RingHom.restrict σ.toRingHom k k hstab) := by
    have : Fintype k := Fintype.ofFinite k
    exact monoInd_of_frobenius (RingHom.restrict σ.toRingHom k k hstab) (q := ℓ ^ f0) hQ
      (by rw [← Nat.card_eq_fintype_card, hkcard]) hj hσk
  have hspan := span_of_card (fixedField σ.toRingHom) k (Q := ℓ ^ f0) (p := p) hQ hp
    (by omega) (by rw [hcardF, ← pow_mul]) hkcard (by rw [hK, ← pow_mul]; congr 1; ring)
  exact ⟨k, F0, fun c hc => hc, ⟨hstab, hind⟩, hF0mem, hcard, hspan⟩

end CFSG.HardMathSupport.Seitz.TrialityOdd
