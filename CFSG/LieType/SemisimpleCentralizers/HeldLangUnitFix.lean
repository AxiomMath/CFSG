module

public import CFSG.LieType.SemisimpleCentralizers.HeldLang
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.HardMathSupport.Foote.ModuleExclusions CFSG.ClassicalGroups.Unitary
  CFSG.Semidihedral.FixedFieldData CFSG.LieType.BorelTits

variable {K : Type} [Field K]

theorem card_fixField {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (σ : K ≃+* K) :
    Nat.card (fixField σ) = p ^ (e / orderOf σ) := by
  obtain ⟨-, -, -, -, -, -, hfix⟩ := finite_field_automorphism_fixed_field_cardinality p e hp he K hK
  obtain ⟨-, -, hcard, -⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hcard
  exact hcard

theorem orderOf_dvd_of_card {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (σ : K ≃+* K) :
    orderOf σ ∣ e := by
  obtain ⟨-, -, -, -, -, -, hfix⟩ := finite_field_automorphism_fixed_field_cardinality p e hp he K hK
  obtain ⟨hdvd, -, -, -⟩ := hfix (Subgroup.zpowers σ)
  rwa [Nat.card_zpowers] at hdvd

theorem exists_fixed_ne_of_odd {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (σ bar : K ≃+* K) (hbb : bar * bar = 1) (hne : bar ≠ 1) (hσ : Odd (orderOf σ)) :
    ∃ x, σ x = x ∧ bar x ≠ x := by
  by_contra hcon
  push Not at hcon
  have : Finite K := finite_of_prime_power_card K hp hK
  obtain ⟨-, -, -, -, -, -, hfix⟩ := finite_field_automorphism_fixed_field_cardinality p e hp he K hK
  set A : Subgroup (K ≃+* K) := Subgroup.zpowers σ ⊔ Subgroup.zpowers bar with hA
  obtain ⟨hdvdA, hmemA, hcardA, -⟩ := hfix A
  obtain ⟨hdvdZ, hmemZ, hcardZ, -⟩ := hfix (Subgroup.zpowers σ)
  have hsub : FixedPoints.subfield A K = FixedPoints.subfield (Subgroup.zpowers σ) K := by
    ext x
    rw [mem_fixedSubfield_iff, mem_fixedSubfield_iff]
    constructor
    · intro h a
      exact h ⟨a, Subgroup.mem_sup_left a.2⟩
    · intro h a
      have hσx : σ x = x := h ⟨σ, Subgroup.mem_zpowers σ⟩
      have hbx : bar x = x := hcon x hσx
      have hs1 : σ ∈ MulAction.stabilizer (K ≃+* K) x := by
        rw [MulAction.mem_stabilizer_iff]; exact hσx
      have hs2 : bar ∈ MulAction.stabilizer (K ≃+* K) x := by
        rw [MulAction.mem_stabilizer_iff]; exact hbx
      have hle : A ≤ MulAction.stabilizer (K ≃+* K) x :=
        sup_le (Subgroup.zpowers_le.mpr hs1) (Subgroup.zpowers_le.mpr hs2)
      have := hle a.2
      rw [MulAction.mem_stabilizer_iff] at this
      exact this
  rw [hsub, hcardZ] at hcardA
  have hcardA' := Nat.pow_right_injective hp.two_le hcardA
  rw [Nat.card_zpowers] at hdvdZ hcardA'
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hmpos : 0 < orderOf σ := orderOf_pos σ
  have hAeq : Nat.card A = orderOf σ := by
    obtain ⟨a, ha⟩ := hdvdA
    obtain ⟨b, hb⟩ := hdvdZ
    have h1 : e / Nat.card A = a := by
      conv_lhs => rw [ha]
      exact Nat.mul_div_cancel_left _ hApos
    have h2 : e / orderOf σ = b := by
      conv_lhs => rw [hb]
      exact Nat.mul_div_cancel_left _ hmpos
    have hab : a = b := h1.symm.trans (hcardA'.symm.trans h2)
    subst hab
    have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h, mul_zero] at ha; omega
      · exact h
    exact Nat.eq_of_mul_eq_mul_right ha0 (ha.symm.trans hb)
  have hzA : Subgroup.zpowers σ ≤ A := le_sup_left
  have hAz : A = Subgroup.zpowers σ :=
    (Subgroup.eq_of_le_of_card_ge hzA (by rw [Nat.card_zpowers, hAeq])).symm
  have hbmem : bar ∈ Subgroup.zpowers σ := by
    rw [← hAz]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers bar)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbmem
  have hdvd : orderOf bar ∣ orderOf σ := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have h2 : orderOf bar = 2 := orderOf_eq_prime (by rw [sq]; exact hbb) hne
  rw [h2] at hdvd
  exact (Nat.not_even_iff_odd.2 hσ) (even_iff_two_dvd.2 hdvd)

section Bar

variable (σ bar : K ≃+* K) (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hbb : ∀ x, bar (bar x) = x)

@[expose] def barFix : fixField σ ≃+* fixField σ where
  toFun x := ⟨bar (x : K), mem_fixField.2 (by rw [hcomm, mem_fixField.1 x.2])⟩
  invFun x := ⟨bar (x : K), mem_fixField.2 (by rw [hcomm, mem_fixField.1 x.2])⟩
  left_inv x := Subtype.ext (hbb x)
  right_inv x := Subtype.ext (hbb x)
  map_mul' x y := Subtype.ext (map_mul bar (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add bar (x : K) (y : K))

theorem coe_barFix (x : fixField σ) : ((barFix σ bar hcomm hbb x : fixField σ) : K) = bar (x : K) := rfl

end Bar

theorem pow_apply_of_frobenius' {F : Type} [Field F] {p : ℕ} {φ : F ≃+* F} (hφ : ∀ x, φ x = x ^ p) :
    ∀ (k : ℕ) (x : F), (φ ^ k) x = x ^ p ^ k := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ, mul_comm]

theorem even_and_eq_pow_of_involution {F : Type} [Field F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card F = p ^ f) {τ : F ≃+* F} (hτ : τ ≠ 1) (hττ : τ * τ = 1) :
    Even f ∧ ∀ x, τ x = x ^ p ^ (f / 2) := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality p f hp hf F hK
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨k, hk, rfl⟩ : ∃ k < f, φ ^ k = τ := by
    have hmem : τ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top τ
    rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k % f, Nat.mod_lt _ (by omega), ?_⟩
    rw [← hk, ← hord, pow_mod_orderOf]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hτ (pow_zero φ)
  have h2k : f ∣ 2 * k := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, two_mul, pow_add, hττ]
  obtain ⟨c, hc⟩ := h2k
  have hc1 : c = 1 := by
    rcases c with _ | _ | c
    · omega
    · rfl
    · nlinarith
  rw [hc1, mul_one] at hc
  refine ⟨⟨k, by omega⟩, fun x => ?_⟩
  rw [pow_apply_of_frobenius' hφ, show f / 2 = k by omega]

theorem exists_barFix_eq {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    {σ bar : K ≃+* K} (hbar : IsUnitaryInvolution bar) (hcomm : ∀ x, σ (bar x) = bar (σ x))
    (hodd : Odd (orderOf σ)) :
    ∃ j : ℕ, 2 * j = e / orderOf σ ∧ Nat.card (fixField σ) = (p ^ j) ^ 2 ∧
      ∀ x, barFix σ bar hcomm hbar.invol x = x ^ p ^ j := by
  haveI : Finite K := finite_of_prime_power_card K hp hK
  have hbb : bar * bar = 1 := RingEquiv.ext hbar.invol
  have hne : bar ≠ 1 := by
    obtain ⟨c, hc⟩ := hbar.exists_ne
    intro h
    exact hc (by rw [h]; rfl)
  obtain ⟨x₁, hx₁σ, hx₁b⟩ := exists_fixed_ne_of_odd hp he hK σ bar hbb hne hodd
  have hbF1 : barFix σ bar hcomm hbar.invol ≠ 1 := fun h => hx₁b (by
    have := congrArg (fun ρ : fixField σ ≃+* fixField σ => ((ρ ⟨x₁, mem_fixField.2 hx₁σ⟩ : fixField σ) : K)) h
    simpa [coe_barFix] using this)
  have hbFbb : barFix σ bar hcomm hbar.invol * barFix σ bar hcomm hbar.invol = 1 :=
    RingEquiv.ext fun x => Subtype.ext (hbar.invol x)
  have hF0 := card_fixField hp he hK σ
  have hdvd := orderOf_dvd_of_card hp he hK σ
  have hmpos : 0 < orderOf σ := orderOf_pos σ
  have hf0 : 1 ≤ e / orderOf σ := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hmpos
  obtain ⟨hev, hform⟩ := even_and_eq_pow_of_involution hp hf0 hF0 hbF1 hbFbb
  obtain ⟨j, hj⟩ := hev
  refine ⟨j, by omega, ?_, fun x => ?_⟩
  · rw [hF0, hj, ← pow_mul]
    ring_nf
  · rw [hform x]
    congr 2
    omega

theorem isUnitaryInvolution_barFix {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    {σ bar : K ≃+* K} (hbar : IsUnitaryInvolution bar) (hcomm : ∀ x, σ (bar x) = bar (σ x))
    (hodd : Odd (orderOf σ)) : IsUnitaryInvolution (barFix σ bar hcomm hbar.invol) := by
  obtain ⟨j, hj2, hcard2, hform⟩ := exists_barFix_eq hp he hK hbar hcomm hodd
  have hF0 := card_fixField hp he hK σ
  haveI : Finite (fixField σ) := finite_of_prime_power_card _ hp hF0
  haveI : CharP (fixField σ) p := characteristic_of_prime_power_card _ hp hF0
  haveI : Fact p.Prime := ⟨hp⟩
  have heq : barFix σ bar hcomm hbar.invol = unitaryInvolution (fixField σ) p j := by
    refine RingEquiv.ext fun x => ?_
    rw [hform x, unitaryInvolution_apply]
  rw [heq]
  exact isUnitaryInvolution_unitaryInvolution hcard2

end CFSG.LieType.SemisimpleCentralizers.HeldLang
