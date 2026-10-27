module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWGoursatJThree
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6MEnding
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6SProdSq
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6PlacementSome

set_option linter.unusedSectionVars false

public noncomputable section

open Subgroup
open scoped MatrixGroups

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.ClassicalInvolution.G2D4Models
  CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.SEITZ3
  CFSG.LocalAnalysis.ComponentInitial

section Cubes

variable {F : Type} [Field F]

theorem sl2Upper_mul' (a b : F) : sl2Upper F a * sl2Upper F b = sl2Upper F (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Upper, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem sl2Lower_mul' (a b : F) : sl2Lower F a * sl2Lower F b = sl2Lower F (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Upper_zero' : sl2Upper F 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Upper]

theorem sl2Lower_zero' : sl2Lower F 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Lower]

theorem sl2Upper_cube (h3 : (3 : F) = 0) (c : F) : sl2Upper F c ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one, sl2Upper_mul', sl2Upper_mul']
  have : c + c + c = 0 := by linear_combination c * h3
  rw [this, sl2Upper_zero']

theorem sl2Lower_cube (h3 : (3 : F) = 0) (c : F) : sl2Lower F c ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one, sl2Lower_mul', sl2Lower_mul']
  have : c + c + c = 0 := by linear_combination c * h3
  rw [this, sl2Lower_zero']

end Cubes

section Twisted

theorem goursatJThree_twisted {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hq3 : ℓ ^ f = 3) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (ψ : SL(2, fixedField σ.toRingHom) →* twistedGroup σ.toRingHom)
    (hψ : ∀ g, ψ g = 1 ↔ g = 1 ∨ g = -1) (D : Subgroup (twistedGroup σ.toRingHom))
    (hDψ : ψ.range = D) (hDc : Nat.card D = 12)
    (hDM : D ≤ invCentGroup σ.toRingHom hσ) (hDJ : D ≤ JTw σ.toRingHom)
    (ν : twistedGroup σ.toRingHom) (hν : ν ∈ invCentGroup σ.toRingHom hσ) :
    ν ∈ JTw σ.toRingHom ∨
      (slB σ.toRingHom hσ).range ≤
        (D ⊔ D.map (MulAut.conj ν).toMonoidHom) ⊔ (slLong σ.toRingHom hσ).range := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hcardF : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hℓ hf hK σ hσq
  have h3 : Module.finrank (fixedField σ.toRingHom) K = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := fixedField σ.toRingHom) (V := K)
    rw [hK, hcardF] at h
    exact (Nat.pow_right_injective (by omega : 2 ≤ ℓ ^ f) h).symm
  have hcardSL : Nat.card SL(2, fixedField σ.toRingHom) = 24 := by
    rw [CFSG.GorensteinWalter.sl2_card_formula, hcardF, hq3]
    norm_num
  exact GoursatJ.goursatJThree h3 hK2 (by rw [hcardF, hq3]) (slLong σ.toRingHom hσ)
    (slB σ.toRingHom hσ) (slLong_injective hσ) (slB_injective hσ)
    (fun a b => slLong_comm_slB hσ a b) (slB_neg_one hσ).symm (JTw σ.toRingHom)
    (slLong_mem_JTw hσ) (fun b => slB_mem_JTw_iff hσ b) ψ hψ D hDψ
    (by rw [hcardSL, hDc]) hDM hDJ ν hν

theorem map_conj_range_le_invCentGroup {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hq3 : ℓ ^ f = 3) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (ψ : SL(2, fixedField σ.toRingHom) →* twistedGroup σ.toRingHom)
    (w g : twistedGroup σ.toRingHom) (hg : g * w * g⁻¹ = slLong σ.toRingHom hσ (-1))
    (hψw : ∀ s, ψ s * w = w * ψ s) :
    ψ.range.map (MulAut.conj g).toMonoidHom ≤ invCentGroup σ.toRingHom hσ := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hKm : (-1 : Kˣ) ≠ 1 := by
    intro h
    apply h2K
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have hrange := range_twistedIncl_eq_of_card (σ := σ.toRingHom) hK2 hq2 hK hσq
  have hC₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤
      (twistedIncl σ.toRingHom).range := hrange.ge
  have hgF : ∀ y : twistedGroup σ.toRingHom,
      twistedIncl σ.toRingHom y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    fun y => hrange ▸ ⟨y, rfl⟩
  have hcardF : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hℓ hf hK σ hσq
  have h3F : (3 : fixedField σ.toRingHom) = 0 := by
    have : Fintype (fixedField σ.toRingHom) := Fintype.ofFinite _
    have hc : Fintype.card (fixedField σ.toRingHom) = 3 := by
      rw [← Nat.card_eq_fintype_card, hcardF, hq3]
    have := FiniteField.cast_card_eq_zero (fixedField σ.toRingHom)
    rw [hc] at this
    exact_mod_cast this
  set S : Set (twistedGroup σ.toRingHom) :=
    {x | ∃ c : fixedField σ.toRingHom, x = g * ψ (sl2Upper _ c) * g⁻¹ ∨
      x = g * ψ (sl2Lower _ c) * g⁻¹} with hS
  have hSodd : ∀ x ∈ S, x ∈ SProd σ.toRingHom hσ ∧ ∃ k : ℕ, x ^ (2 * k + 1) = 1 := by
    rintro x ⟨c, hx | hx⟩
    · refine ⟨?_, 1, ?_⟩
      · have hxτ : x * slLong σ.toRingHom hσ (-1) = slLong σ.toRingHom hσ (-1) * x := by
          rw [hx, ← hg]
          calc g * ψ (sl2Upper _ c) * g⁻¹ * (g * w * g⁻¹)
              = g * (ψ (sl2Upper _ c) * w) * g⁻¹ := by group
            _ = g * (w * ψ (sl2Upper _ c)) * g⁻¹ := by rw [hψw]
            _ = g * w * g⁻¹ * (g * ψ (sl2Upper _ c) * g⁻¹) := by group
        exact mem_SProd_of_centralizes hσ hKm hC₀ hgF hxτ
      · rw [hx]
        have h1 : (g * ψ (sl2Upper _ c) * g⁻¹) ^ 3 = g * ψ (sl2Upper _ c) ^ 3 * g⁻¹ := conj_pow
        rw [show 2 * 1 + 1 = 3 by norm_num, h1, ← map_pow, sl2Upper_cube h3F, map_one]; group
    · refine ⟨?_, 1, ?_⟩
      · have hxτ : x * slLong σ.toRingHom hσ (-1) = slLong σ.toRingHom hσ (-1) * x := by
          rw [hx, ← hg]
          calc g * ψ (sl2Lower _ c) * g⁻¹ * (g * w * g⁻¹)
              = g * (ψ (sl2Lower _ c) * w) * g⁻¹ := by group
            _ = g * (w * ψ (sl2Lower _ c)) * g⁻¹ := by rw [hψw]
            _ = g * w * g⁻¹ * (g * ψ (sl2Lower _ c) * g⁻¹) := by group
        exact mem_SProd_of_centralizes hσ hKm hC₀ hgF hxτ
      · rw [hx]
        have h1 : (g * ψ (sl2Lower _ c) * g⁻¹) ^ 3 = g * ψ (sl2Lower _ c) ^ 3 * g⁻¹ := conj_pow
        rw [show 2 * 1 + 1 = 3 by norm_num, h1, ← map_pow, sl2Lower_cube h3F, map_one]; group
  refine le_trans ?_ (closure_le_invCentGroup_of_odd hσ hSodd)
  rintro _ ⟨d, ⟨s, rfl⟩, rfl⟩
  have hs : s ∈ Subgroup.closure (Set.range (sl2Upper (fixedField σ.toRingHom)) ∪
      Set.range (sl2Lower (fixedField σ.toRingHom))) := by
    rw [sl2_closure_upper_lower]; trivial
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact Subgroup.subset_closure ⟨c, Or.inl rfl⟩
    · exact Subgroup.subset_closure ⟨c, Or.inr rfl⟩
  | one =>
    simp only [map_one]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have : (MulAut.conj g).toMonoidHom (ψ (x * y)) =
        (MulAut.conj g).toMonoidHom (ψ x) * (MulAut.conj g).toMonoidHom (ψ y) := by
      rw [map_mul, map_mul]
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : (MulAut.conj g).toMonoidHom (ψ x⁻¹) = ((MulAut.conj g).toMonoidHom (ψ x))⁻¹ := by
      rw [map_inv, map_inv]
    rw [this]
    exact inv_mem hx

theorem slB_le_of_phi6_datum_three
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hq3 : ℓ ^ f = 3) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrq : r ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1)
    (E₀ : Subgroup (twistedGroup σ.toRingHom)) (hexp : ∀ x ∈ E₀, x ^ r = 1)
    (hcard : Nat.card E₀ = r ^ 2) (w : twistedGroup σ.toRingHom)
    (hinv : ∀ x ∈ E₀, w * x * w⁻¹ = x⁻¹) (g : twistedGroup σ.toRingHom)
    (hg : g * w * g⁻¹ = slLong σ.toRingHom hσ (-1))
    (ψ : SL(2, fixedField σ.toRingHom) →* twistedGroup σ.toRingHom)
    (hψ : ∀ s, ψ s = 1 ↔ s = 1 ∨ s = -1) (D : Subgroup (twistedGroup σ.toRingHom))
    (hDψ : ψ.range = D) (hDc : Nat.card D = 12) (hDw : ∀ x ∈ D, x * w = w * x)
    (hDJ : ∀ x ∈ D, g * x * g⁻¹ ∈ JTw σ.toRingHom)
    (c : twistedGroup σ.toRingHom) (hcE : c ∈ E₀) (hc1 : c ≠ 1)
    (hcJ : g * c * g⁻¹ ∈ JTw σ.toRingHom) (a b : twistedGroup σ.toRingHom)
    (haE : ∀ x ∈ E₀, a * x * a⁻¹ ∈ E₀) (hbE : ∀ x ∈ E₀, b * x * b⁻¹ ∈ E₀)
    (haM : g * a * g⁻¹ ∈ invCentGroup σ.toRingHom hσ)
    (hbM : g * b * g⁻¹ ∈ invCentGroup σ.toRingHom hσ) (hab : a * b * a⁻¹ * b⁻¹ = w) :
    ∃ ν, (ν = a ∨ ν = b) ∧
      (slB σ.toRingHom hσ).range ≤
        (D.map (MulAut.conj g).toMonoidHom ⊔
          (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * ν * g⁻¹)).toMonoidHom) ⊔
          (slLong σ.toRingHom hσ).range := by
  classical
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => hσ c
  set D' : Subgroup (twistedGroup σ.toRingHom) := D.map (MulAut.conj g).toMonoidHom with hD'
  set ψ' : SL(2, fixedField σ.toRingHom) →* twistedGroup σ.toRingHom :=
    (MulAut.conj g).toMonoidHom.comp ψ with hψ'
  have hψ'inj : ∀ s, ψ' s = 1 ↔ s = 1 ∨ s = -1 := fun s => by
    rw [← hψ s]
    constructor
    · intro h
      have h2 : g * ψ s * g⁻¹ = 1 := h
      have h3 : g * ψ s = g * 1 := by rw [mul_one]; exact mul_inv_eq_one.1 h2
      exact mul_left_cancel h3
    · intro h
      show g * ψ s * g⁻¹ = 1
      rw [h]; group
  have hDψ' : ψ'.range = D' := by
    rw [hψ', MonoidHom.range_comp, hDψ]
  have hD'c : Nat.card D' = 12 := by
    rw [← hDc]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective D (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm
  have hD'J : D' ≤ JTw σ.toRingHom := by
    rintro _ ⟨x, hx, rfl⟩
    exact hDJ x hx
  have hD'M : D' ≤ invCentGroup σ.toRingHom hσ := by
    rw [hD', ← hDψ]
    exact map_conj_range_le_invCentGroup hℓ hℓ2 hf hq3 hK σ hσq hσ ψ w g hg
      (fun s => hDw (ψ s) (by rw [← hDψ]; exact ⟨s, rfl⟩))
  have hJor : ∀ ν : twistedGroup σ.toRingHom, g * ν * g⁻¹ ∈ invCentGroup σ.toRingHom hσ →
      g * ν * g⁻¹ ∉ JTw σ.toRingHom →
      (slB σ.toRingHom hσ).range ≤
        (D' ⊔ D'.map (MulAut.conj (g * ν * g⁻¹)).toMonoidHom) ⊔
          (slLong σ.toRingHom hσ).range := fun ν hνM hνJ => by
    rcases goursatJThree_twisted hℓ hℓ2 hf hq3 hK σ hσq hσ ψ' hψ'inj D' hDψ' hD'c hD'M hD'J
      (g * ν * g⁻¹) hνM with h | h
    · exact absurd h hνJ
    · exact h
  by_cases hJa : g * a * g⁻¹ ∈ JTw σ.toRingHom
  · by_cases hJb : g * b * g⁻¹ ∈ JTw σ.toRingHom
    · exfalso
      have hwc : w * c * w⁻¹ = c⁻¹ := hinv c hcE
      have hnot : ¬ (a * c * a⁻¹ ∈ zpowers c ∧ b * c * b⁻¹ ∈ zpowers c) := fun ⟨h1, h2⟩ =>
        not_both_stabilize_line hr (by omega) (hexp c hcE) hc1 hwc hab h1 h2
      have hplane : ∃ c'' ∈ E₀, c'' ∉ zpowers c ∧ g * c'' * g⁻¹ ∈ JTw σ.toRingHom := by
        by_cases h1 : a * c * a⁻¹ ∈ zpowers c
        · refine ⟨b * c * b⁻¹, hbE c hcE, fun h2 => hnot ⟨h1, h2⟩, ?_⟩
          have : g * (b * c * b⁻¹) * g⁻¹ =
              (g * b * g⁻¹) * (g * c * g⁻¹) * (g * b * g⁻¹)⁻¹ := by group
          rw [this]
          exact mul_mem (mul_mem hJb hcJ) (inv_mem hJb)
        · refine ⟨a * c * a⁻¹, haE c hcE, h1, ?_⟩
          have : g * (a * c * a⁻¹) * g⁻¹ =
              (g * a * g⁻¹) * (g * c * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
          rw [this]
          exact mul_mem (mul_mem hJa hcJ) (inv_mem hJa)
      obtain ⟨c'', hc''E, hc''Z, hc''J⟩ := hplane
      have hE0 := closure_pair_eq hr hcE hc''E hexp hcard hc1 hc''Z
      have hEJ : E₀.map (MulAut.conj g).toMonoidHom ≤ JTw σ.toRingHom := by
        rw [← hE0, MonoidHom.map_closure]
        refine closure_le _ |>.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        rcases hx with rfl | rfl
        · exact hcJ
        · exact hc''J
      refine no_plane_in_JTw hℓ hℓ2 hf (by omega) hK σ hσq hσ3 hr hr5 hrq
        (E₀.map (MulAut.conj g).toMonoidHom) hEJ ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hexp x hx, map_one]
      · rw [← hcard]
        exact (Nat.card_congr (Subgroup.equivMapOfInjective E₀ (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).toEquiv).symm
    · exact ⟨b, Or.inr rfl, hJor b hbM hJb⟩
  · exact ⟨a, Or.inl rfl, hJor a haM hJa⟩

end Twisted

section Core

@[expose] def Phi6PlacementThree {K : Type} [Field K] (σ : K →+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) (E₀ : Subgroup (twistedGroup σ)) (w : twistedGroup σ) : Prop :=
  ∃ (g : twistedGroup σ) (ψ : SL(2, fixedField σ) →* twistedGroup σ)
    (x₁ c a b : twistedGroup σ),
    g * w * g⁻¹ = slLong σ hσ (-1) ∧ (∀ s, ψ s = 1 ↔ s = 1 ∨ s = -1) ∧ Nat.card ψ.range = 12 ∧
    (∀ s, ψ s * w = w * ψ s) ∧ x₁ ∈ E₀ ∧ x₁ ≠ 1 ∧ (∀ s, ψ s * x₁ = x₁ * ψ s) ∧
    (∀ s, g * ψ s * g⁻¹ ∈ JTw σ) ∧ c ∈ E₀ ∧ c ≠ 1 ∧ g * c * g⁻¹ ∈ JTw σ ∧
    (∀ x ∈ E₀, a * x * a⁻¹ ∈ E₀) ∧ (∀ x ∈ E₀, b * x * b⁻¹ ∈ E₀) ∧
    g * a * g⁻¹ ∈ invCentGroup σ hσ ∧ g * b * g⁻¹ ∈ invCentGroup σ hσ ∧
    a * b * a⁻¹ * b⁻¹ = w

@[expose] def Phi6PlacementSomeThree (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ℓ ^ f < 5 → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c,
    r.Prime → r ≠ ℓ → (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 →
    ∃ (E₀ : Subgroup (twistedGroup σ.toRingHom)) (w : twistedGroup σ.toRingHom)
      (P : Sylow r (twistedGroup σ.toRingHom)),
      (∀ x ∈ E₀, x ^ r = 1) ∧ Nat.card E₀ = r ^ 2 ∧ w * w = 1 ∧
      (∀ x ∈ E₀, w * x * w⁻¹ = x⁻¹) ∧ E₀ ≤ (P : Subgroup (twistedGroup σ.toRingHom)) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)),
        ∀ y ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x * y = y * x) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x ^ r = 1 → x ∈ E₀) ∧
      (∃ u x₁ : twistedGroup σ.toRingHom, u * u = 1 ∧ u ≠ 1 ∧ x₁ ∈ E₀ ∧ x₁ ≠ 1 ∧
        u * w = w * u ∧ u * x₁ = x₁ * u) ∧
      Phi6PlacementThree σ.toRingHom hσ E₀ w

theorem phi6CoreWLt5_of_placementSome {r : ℕ} (hr5 : 5 ≤ r) (h : Phi6PlacementSomeThree r) :
    Phi6CoreWLt5 r := by
  intro ℓ f hℓ hℓ2 hf hlt K _ _ hK σ hσq hσ hr hrℓ hd
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact r.Prime := ⟨hr⟩
  have hq3 : ℓ ^ f = 3 := by
    have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
    have h3 : 3 ≤ ℓ := by
      have := hℓ.two_le
      rcases Nat.lt_or_ge ℓ 3 with h | h
      · omega
      · exact h
    have : 3 ≤ ℓ ^ f := le_trans h3 (Nat.le_self_pow (by omega) ℓ)
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨E₀, w, P, hEp, hEc, hww, hwE, hEP, hPc, hPΩ, ⟨u, x₁', huu, hu1, hx₁'E, hx₁'1, huw, hux⟩,
    g, ψ, x₂, c, a, b, hg, hψ, hDc, hψw, hx₂E, hx₂1, hψx₂, hψJ, hcE, hc1, hcJ, haE, hbE,
    haM, hbM, hab⟩ := h ℓ f hℓ hℓ2 hf hlt K hK σ hσq hσ hr hrℓ hd
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hqq : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hrq : r ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := by
    have : (((ℓ ^ f) ^ 2 - ℓ ^ f + 1 : ℕ) : ℤ) =
        ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
      push_cast [Nat.cast_sub hqq]
      ring
    exact Int.natCast_dvd_natCast.1 (this ▸ hd)
  obtain ⟨ν, hν, hBX⟩ := slB_le_of_phi6_datum_three hℓ hℓ2 hf hq3 hK σ hσq hσ hr hr5 hrq E₀ hEp hEc
    w hwE g hg ψ hψ ψ.range rfl hDc (fun x hx => by obtain ⟨s, rfl⟩ := hx; exact hψw s)
    (fun x hx => by obtain ⟨s, rfl⟩ := hx; exact hψJ s) c hcE hc1 hcJ a b haE hbE haM hbM hab
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hrK2 : r ∣ Nat.card K ^ 2 - 1 := by rw [hK]; exact dvd_pow_six_sub_one_of_phi6 hq1 hd
  have hrq' : ¬ r ∣ ℓ ^ f := fun h' =>
    hrℓ ((Nat.prime_dvd_prime_iff_eq hr hℓ).1 (hr.dvd_of_dvd_pow h'))
  have hFcard : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq2 hK hσq
  have : Finite (fixedField σ.toRingHom) := Subtype.finite
  have hrF : ¬ r ∣ Nat.card (SL(2, fixedField σ.toRingHom)) := by
    rw [card_SL2_eq, hFcard]
    exact not_dvd_card_SL2_of_phi6 hr hr5 hq1 hrq' hd
  set H : Subgroup (twistedGroup σ.toRingHom) := closure (cenGen E₀) with hH
  have hR : ∀ c ∈ H, c ^ r = 1 → c ≠ 1 →
      Subgroup.centralizer ({c} : Set (twistedGroup σ.toRingHom)) ≤ H :=
    fun c hc hcr hc1 => CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.centralizer_le_closure_cenGen
      P hEP hPc hPΩ hc hcr hc1
  have hR' := rclosure_map_conj hR g
  have hDH : ∀ s, ψ s ∈ H := fun s => subset_closure ⟨x₂, hx₂E, hx₂1, hψx₂ s⟩
  have hνE : ∀ x ∈ E₀, ν * x * ν⁻¹ ∈ E₀ := by
    rcases hν with rfl | rfl
    · exact haE
    · exact hbE
  have hνM : g * ν * g⁻¹ ∈ invCentGroup σ.toRingHom hσ := by
    rcases hν with rfl | rfl
    · exact haM
    · exact hbM
  set D' : Subgroup (twistedGroup σ.toRingHom) := ψ.range.map (MulAut.conj g).toMonoidHom with hD'
  have hD'M : D' ≤ invCentGroup σ.toRingHom hσ :=
    map_conj_range_le_invCentGroup hℓ hℓ2 hf hq3 hK σ hσq hσ ψ w g hg hψw
  have hXM : D' ⊔ D'.map (MulAut.conj (g * ν * g⁻¹)).toMonoidHom ≤
      invCentGroup σ.toRingHom hσ := by
    refine sup_le hD'M ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hνM (hD'M hy)) (inv_mem hνM)
  have hD'H : D' ≤ H.map (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨x, ⟨s, rfl⟩, rfl⟩
    exact ⟨ψ s, hDH s, rfl⟩
  have hXH : D' ⊔ D'.map (MulAut.conj (g * ν * g⁻¹)).toMonoidHom ≤
      H.map (MulAut.conj g).toMonoidHom := by
    refine sup_le hD'H ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, ⟨s, rfl⟩, rfl⟩ := hy
    refine ⟨ν * ψ s * ν⁻¹, conj_mem_closure_cenGen hνE (hDH s), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hMH := invCentGroup_le_of_slB_le hσ hrK2 hrF hXM hXH hBX hR'
  refine ⟨E₀, w, P, hEp, hEc, hww, hwE, hEP, hPc, hPΩ, ⟨g, hg, ?_⟩, ⟨u, x₁', huu, hu1, hx₁'E, hx₁'1,
    huw, hux⟩⟩
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨y, hy, hym⟩ := hMH hm
  have : (MulAut.conj g⁻¹).toMonoidHom m = y := by
    rw [← hym]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [this]
  exact hy

theorem phi6CoreW_of_placementSome {r : ℕ} (hr5 : 5 ≤ r)
    (h5 : CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6PlacementSome r)
    (h3 : Phi6PlacementSomeThree r) : Phi6CoreW r :=
  phi6CoreW_of_ge5_of_lt5
    (CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phi6CoreWGe5_of_placementSome hr5 h5)
    (phi6CoreWLt5_of_placementSome hr5 h3)

end Core

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
