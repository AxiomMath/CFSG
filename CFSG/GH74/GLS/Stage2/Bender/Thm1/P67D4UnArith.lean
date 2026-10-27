module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPolarDefs

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair

section Arith

variable {p f : ℕ} [Fact p.Prime]

private theorem unArith_two_le_pow_four (hf : 1 ≤ f) : 2 ≤ (p ^ f) ^ 4 := by
  have hp : p.Prime := Fact.out
  have h : 2 ≤ p ^ f :=
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  exact h.trans (Nat.le_self_pow (by omega) _)

theorem un_a2Std (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    {K : Type} [Field K] [Finite K] [CharP K p] (hK : Nat.card K = ((p ^ f) ^ 4) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ ((p ^ f) ^ 4)) {b : Kˣ} (hb3 : b ^ 3 = 1)
    (hb1 : b ≠ 1) : A2Std σ b ((p ^ f) ^ 4) := by
  have hmod : ((p ^ f) ^ 4) % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  refine ⟨unArith_two_le_pow_four hf, hK, hσ, hmod, ?_, ?_, hb3, hb1⟩
  · rw [ringChar.eq K p]
    exact hp2
  · obtain ⟨k, hk⟩ : ∃ k, (p ^ f) ^ 4 = 3 * k + 1 := ⟨((p ^ f) ^ 4) / 3, by omega⟩
    have hbn : b ^ ((p ^ f) ^ 4) = b := by
      rw [hk, pow_succ, pow_mul, hb3, one_pow, one_mul]
    apply Units.ext
    change σ (b : K) = (b : K)
    rw [hσ, ← Units.val_pow_eq_pow_val, hbn]

omit [Fact p.Prime] in
theorem un_eps_sigma {K : Type} [Field K] {σ ε : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ ((p ^ f) ^ 4)) (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) :
    ∀ c, ε (σ c) = σ (ε c) := by
  intro c
  rw [hε, hσ, hσ, hε, ← pow_mul c, ← pow_mul c, mul_comm]

omit [Fact p.Prime] in
theorem un_eps_unit (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] {ε : K ≃+* K}
    (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) {b : Kˣ} (hb3 : b ^ 3 = 1) :
    Units.map ε.toRingHom.toMonoidHom b = b⁻¹ := by
  have hmod : ((p ^ f) ^ 9) % 3 = 2 := by
    rw [Nat.pow_mod, hq]
  obtain ⟨k, hk⟩ : ∃ k, (p ^ f) ^ 9 = 3 * k + 2 := ⟨((p ^ f) ^ 9) / 3, by omega⟩
  have hbn : b ^ ((p ^ f) ^ 9) = b⁻¹ := by
    rw [hk, pow_add, pow_mul, hb3, one_pow, one_mul]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hb3])
  apply Units.ext
  change ε (b : K) = ((b⁻¹ : Kˣ) : K)
  rw [hε, ← Units.val_pow_eq_pow_val, hbn]

omit [Fact p.Prime] in
theorem un_eps_sq_unit (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] {ε : K ≃+* K}
    (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) {b : Kˣ} (hb3 : b ^ 3 = 1) :
    Units.map (ε * ε).toRingHom.toMonoidHom b = b := by
  have h1 : ε (b : K) = ((b⁻¹ : Kˣ) : K) := congrArg Units.val (un_eps_unit hq hε hb3)
  have h2 : ε ((b⁻¹ : Kˣ) : K) = ((b⁻¹⁻¹ : Kˣ) : K) :=
    congrArg Units.val (un_eps_unit hq hε (b := b⁻¹) (by rw [inv_pow, hb3, inv_one]))
  apply Units.ext
  change ε (ε (b : K)) = (b : K)
  rw [h1, h2, inv_inv]

omit [Fact p.Prime] in
theorem un_eps_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = ((p ^ f) ^ 4) ^ 3)
    {ε : K ≃+* K} (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) :
    ∀ c, ε (ε (ε (ε c))) = c := by
  intro c
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = (p ^ f) ^ 12 := by
    rw [← Nat.card_eq_fintype_card, hK]
    ring
  have h4 : ε (ε (ε (ε c))) = c ^ ((p ^ f) ^ 36) := by
    rw [hε, hε, hε, hε, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have h36 : (p ^ f) ^ 36 = (Fintype.card K) ^ 3 := by
    rw [hcard]
    ring
  rw [h4, h36, FiniteField.pow_card_pow]

omit [Fact p.Prime] in
theorem un_charP_unK {K : Type} [Field K] [Finite K] [CharP K p] (σ : K ≃+* K) :
    CharP (UnK σ) p := by
  exact inferInstance

theorem un_card_unK {K : Type} [Field K] [Finite K] (hf : 1 ≤ f)
    (hK : Nat.card K = ((p ^ f) ^ 4) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ ((p ^ f) ^ 4)) : Nat.card (UnK σ) = (p ^ f) ^ 4 :=
  card_fixedField_of_cube σ.toRingHom (q := (p ^ f) ^ 4) (unArith_two_le_pow_four hf) hK hσ

omit [Fact p.Prime] in
theorem un_eps_frob {K : Type} [Field K] [Finite K] {σ ε : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ ((p ^ f) ^ 4)) (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9))
    (hεσ : ∀ c, ε (σ c) = σ (ε c)) (a : UnK σ) : unEps ε hεσ a = a ^ (p ^ f) := by
  apply Subtype.ext
  have hfix : (a : K) ^ ((p ^ f) ^ 4) = (a : K) := by
    rw [← hσ]
    exact a.2
  have hfix2 : (a : K) ^ (((p ^ f) ^ 4) ^ 2) = (a : K) := by
    rw [pow_two, pow_mul, hfix, hfix]
  have h9 : (p ^ f) ^ 9 = ((p ^ f) ^ 4) ^ 2 * p ^ f := by ring
  rw [coe_unEps, hε, h9, pow_mul, hfix2, SubmonoidClass.coe_pow]

theorem unEps_mul {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (ε₁ ε₂ : K ≃+* K)
    (h₁ : ∀ c, ε₁ (σ c) = σ (ε₁ c)) (h₂ : ∀ c, ε₂ (σ c) = σ (ε₂ c))
    (h₃ : ∀ c, (ε₁ * ε₂) (σ c) = σ ((ε₁ * ε₂) c)) (a : UnK σ) :
    unEps (ε₁ * ε₂) h₃ a = unEps ε₁ h₁ (unEps ε₂ h₂ a) :=
  Subtype.ext rfl

end Arith

end CFSG.GH74.GLS.Stage2.Bender.Thm1
