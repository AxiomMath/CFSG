module

public import CFSG.LieType.Chevalley.GraphFixedOrbitParameters
public import CFSG.LieType.Chevalley.FoldedRootOrbits
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

theorem finite_graph_field_parameter_fields (t : TwistTag) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (p ^ f) ^ t.order) :
    ∃ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) ∧ orderOf σ = t.order ∧
      (∀ a, Nat.card (orbitField t K σ.toRingHom a) = (p ^ f) ^ (t.orbit a).card) ∧
      (∀ a, (t.orbit a).card = t.order → orbitField t K σ.toRingHom a = ⊤) ∧
      ∃ k : Subfield K, (k : Set K) = {c | c ^ (p ^ f) = c} ∧ Nat.card k = p ^ f ∧
        ∀ a, (t.orbit a).card = 1 → orbitField t K σ.toRingHom a = k := by
  have hm := t.order_pos
  have hn : 1 ≤ f * t.order := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hK' : Nat.card K = p ^ (f * t.order) := by rw [hK, ← pow_mul]
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK']; exact (pow_pos hp.pos _).ne')
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨φ, hφ, hord, -, -, hfix⟩ := finite_field_automorphism_fixed_field_cardinality hp hn hK'
  have hφpow : ∀ (n : ℕ) (c : K), (φ ^ n) c = c ^ (p ^ n) := by
    intro n
    induction n with
    | zero => intro c; rw [pow_zero, RingAut.one_apply, pow_zero, pow_one]
    | succ n ih => intro c; rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, ← pow_succ]
  set σ := φ ^ f
  have hσ : ∀ c, σ c = c ^ (p ^ f) := hφpow f
  have hσord : orderOf σ = t.order := by
    rw [orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro _ rfl), hord,
      Nat.mul_div_cancel_left _ (by omega)]
  have hσpow : ∀ (n : ℕ) (c : K), (σ.toRingHom ^ n) c = c ^ ((p ^ f) ^ n) := by
    intro n
    induction n with
    | zero => intro c; rw [pow_zero, pow_zero, pow_one]; rfl
    | succ n ih =>
      intro c
      rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih]
      change σ (c ^ ((p ^ f) ^ n)) = _
      rw [hσ, ← pow_mul, ← pow_succ]
  obtain ⟨-, S, hS, hcardS⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσord, Nat.mul_div_cancel _ (by omega)] at hcardS
  have hSσ : (S : Set K) = {c | c ^ (p ^ f) = c} := by
    rw [hS]
    ext c
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      rw [← hσ]
      exact h σ (Subgroup.mem_zpowers σ)
    · intro h τ hτ
      have hfin : IsOfFinOrder σ := orderOf_pos_iff.1 (by rw [hσord]; exact hm)
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 hτ)
      induction n with
      | zero => rw [pow_zero, RingAut.one_apply]
      | succ n ih => rw [pow_succ', RingAut.mul_apply, ih (Subgroup.npow_mem_zpowers _ _), hσ, h]
  have htop : ∀ a, (t.orbit a).card = t.order → orbitField t K σ.toRingHom a = ⊤ := by
    intro a ha
    refine eq_top_iff.2 fun c _ => mem_orbitField.2 ?_
    rw [hσpow, ha, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hone : ∀ a, (t.orbit a).card = 1 → orbitField t K σ.toRingHom a = S := by
    intro a ha
    refine SetLike.ext' ?_
    rw [hSσ]
    ext c
    rw [SetLike.mem_coe, mem_orbitField, hσpow, ha, pow_one, Set.mem_ofPred_eq]
  refine ⟨σ, hσ, hσord, fun a => ?_, htop, S, hSσ, hcardS, hone⟩
  rcases t.card_orbit a with ha | ha
  · rw [hone a ha, hcardS, ha, pow_one]
  · rw [htop a ha, ha, ← hK]
    exact Nat.card_congr Subfield.topEquiv.toEquiv

end CFSG.LieType.Chevalley
