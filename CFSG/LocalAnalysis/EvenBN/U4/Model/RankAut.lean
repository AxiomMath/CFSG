module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Rank

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Twisted

theorem map_bar (σ : K →+* K) (c : K) : σ (h.bar c) = h.bar (σ c) := by
  rw [h.bar_apply, h.bar_apply, map_pow]

include h in
theorem ncard_fixed_le_of_ne (σ : K →+* K) (hσ : ∃ k, σ k ≠ k) :
    {k : K | σ k = k}.ncard ≤ 2 ^ f := by
  have := h.finite
  set F₀ : Subfield K := σ.eqLocusField (RingHom.id K)
  have hF₀ : {k : K | σ k = k} = (F₀ : Set K) := rfl
  have : Finite F₀ := Subtype.finite
  have : Module.Finite F₀ K := Module.finite_iff_finite.2 h.finite
  have hpow := Module.natCard_eq_pow_finrank (K := F₀) (V := K)
  rw [h.card_eq_sq] at hpow
  rw [hF₀, ← Nat.card_coe_set_eq]
  change Nat.card F₀ ≤ 2 ^ f
  set n := Module.finrank F₀ K
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.one_le; omega)
  have hn0 : n ≠ 0 := by
    intro hn
    rw [hn, pow_zero] at hpow
    have : 1 < (2 ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) hq
    omega
  have hn1 : n ≠ 1 := by
    intro hn
    rw [hn, pow_one] at hpow
    obtain ⟨k, hk⟩ := hσ
    have huniv : (F₀ : Set K) = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [Set.ncard_univ, ← Nat.card_coe_set_eq, h.card_eq_sq]
      exact hpow.le
    exact hk (huniv ▸ Set.mem_univ k : k ∈ (F₀ : Set K))
  have hle : Nat.card F₀ ^ 2 ≤ (2 ^ f) ^ 2 := by
    rw [hpow]
    exact Nat.pow_le_pow_right Nat.card_pos (by omega)
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 hle

theorem map_miyamotoXGL (σ : K →+* K) (a b c d : K) :
    Matrix.GeneralLinearGroup.map σ (miyamotoXGL h a b c d) =
      miyamotoXGL h (σ a) (σ b) (σ c) (σ d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoX, map_bar h σ]

variable [CharP K 2]

@[expose] def miyamotoTwistedFixA1 (σ : K →+* K) (g : GL (Fin 4) K) : Subgroup (GL (Fin 4) K) :=
  miyamotoA1 h ⊓ MonoidHom.eqLocus
    ((MulAut.conj g⁻¹).toMonoidHom.comp (Matrix.GeneralLinearGroup.map σ)) (MonoidHom.id _)

omit [CharP K 2] in
theorem mem_miyamotoTwistedFixA1 {σ : K →+* K} {g y : GL (Fin 4) K} :
    y ∈ miyamotoTwistedFixA1 h σ g ↔
      y ∈ miyamotoA1 h ∧ g⁻¹ * Matrix.GeneralLinearGroup.map σ y * g = y := by
  simp [miyamotoTwistedFixA1, MonoidHom.eqLocus]

omit [CharP K 2] in
include h in
theorem ncard_eq_mul_map_le (σ : K →+* K) (hσ : ∃ k, σ k ≠ k) (w : K) :
    {c : K | c = w * σ c}.ncard ≤ 2 ^ f := by
  have := h.finite
  by_cases hex : ∃ c₀ : K, c₀ ≠ 0 ∧ c₀ = w * σ c₀
  · obtain ⟨c₀, hc₀, e₀⟩ := hex
    refine le_trans (Set.ncard_le_ncard_of_injOn (fun c => c / c₀) (fun c hc => ?_)
      (fun c _ c' _ e => ?_) (Set.toFinite _)) (ncard_fixed_le_of_ne h σ hσ)
    · have hc : c = w * σ c := hc
      change σ (c / c₀) = c / c₀
      have hσc₀ : σ c₀ ≠ 0 := (map_ne_zero σ).2 hc₀
      rw [map_div₀]
      field_simp
      linear_combination (σ c) * e₀ - (σ c₀) * hc
    · simpa [div_left_inj' hc₀] using e
  · push Not at hex
    calc {c : K | c = w * σ c}.ncard ≤ ({0} : Set K).ncard :=
          Set.ncard_le_ncard (fun c hc => by
            by_contra hne
            exact hex c hne hc) (Set.toFinite _)
      _ = 1 := Set.ncard_singleton 0
      _ ≤ 2 ^ f := Nat.one_le_two_pow

theorem card_miyamotoTwistedFixA1_le (σ : K →+* K) (hσ : ∃ k, σ k ≠ k) (p : Kˣ × Kˣ)
    {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) :
    Nat.card (miyamotoTwistedFixA1 h σ (miyamotoIHom h p * g)) ≤ (2 ^ f) ^ 3 := by
  have := h.finite
  have hbb := h.bar_bar
  obtain ⟨a, β, γ, δ, hβ, -, rfl⟩ := (mem_P h).1 hg
  have hN : Nat.card (miyamotoTwistedFixA1 h σ (miyamotoIHom h p * miyamotoXGL h a β γ δ) ⊓
      miyamotoRootC h : Subgroup _) ≤ 2 ^ f := by
    refine le_trans ?_ (ncard_eq_mul_map_le h σ hσ ((p.1 : K) * h.bar (p.2 : K)))
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    refine Set.ncard_le_ncard_of_injOn (fun y : GL (Fin 4) K =>
      (y : Matrix (Fin 4) (Fin 4) K) 2 0) ?_ ?_ (Set.toFinite _)
    · rintro y ⟨hy, ⟨c, rfl⟩⟩
      have e := ((mem_miyamotoTwistedFixA1 h).1 hy).2
      rw [_root_.mul_inv_rev, map_miyamotoXGL, map_zero] at e
      have e' : (miyamotoXGL h a β γ δ)⁻¹ * ((miyamotoIHom h p)⁻¹ * miyamotoXGL h 0 0 (σ c) 0 *
          miyamotoIHom h p) * miyamotoXGL h a β γ δ = miyamotoXGL h 0 0 c 0 := by
        rw [← e]
        simp only [mul_assoc]
      rw [miyamotoIHom_conj, mul_zero, mul_zero, mul_zero, miyamotoXGL_conj h hβ (map_zero _),
        miyamotoXGL_inj] at e'
      simpa using e'.2.2.1.symm
    · rintro y ⟨-, ⟨c, rfl⟩⟩ y' ⟨-, ⟨c', rfl⟩⟩ e
      simp only [coe_miyamotoXGL, miyamotoX_two_zero] at e
      rw [e]
  have key := card_le_card_inf_mul_ncard
    (H := miyamotoTwistedFixA1 h σ (miyamotoIHom h p * miyamotoXGL h a β γ δ))
    (N := miyamotoRootC h) (fun y : GL (Fin 4) K =>
      ((y : Matrix (Fin 4) (Fin 4) K) 2 1, (y : Matrix (Fin 4) (Fin 4) K) 3 0))
    (T := {b : K | h.bar b = b} ×ˢ {d : K | h.bar d = d}) (Set.toFinite _) ?_ ?_
  · rw [Set.ncard_prod, ncard_fixed] at key
    calc _ ≤ _ := key
      _ ≤ 2 ^ f * (2 ^ f * 2 ^ f) := Nat.mul_le_mul_right _ hN
      _ = (2 ^ f) ^ 3 := by ring
  · intro y hy
    obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 ((mem_miyamotoTwistedFixA1 h).1 hy).1
    exact ⟨by simpa using hb, by simpa using hd⟩
  · intro y hy y' hy' e
    have hyA := ((mem_miyamotoTwistedFixA1 h).1 hy).1
    obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hyA
    obtain ⟨b', c', d', hb', hd', rfl⟩ := (mem_A1 h).1 ((mem_miyamotoTwistedFixA1 h).1 hy').1
    simp only [coe_miyamotoXGL, miyamotoX_two_one, miyamotoX_three_zero, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rw [miyamotoXGL_inv h hb, miyamotoXGL_mul h hb]
    refine ⟨c + c', (miyamotoXGL_inj h).2 ⟨by simp, ?_, by ring, ?_⟩⟩
    · exact CharTwo.add_self_eq_zero b
    · simp only [mul_zero, zero_mul, map_zero, add_zero]
      exact CharTwo.add_self_eq_zero d

end Twisted

section Thompson

variable [CharP K 2]

theorem two_mul_card_lt_of_twisted (hf : 2 ≤ f) (σ : K →+* K) (hσ : ∃ k, σ k ≠ k)
    (p : Kˣ × Kˣ) {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) {E : Subgroup (GL (Fin 4) K)}
    (hEP : E ≤ miyamotoP h) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hfix : ∀ y ∈ E, (miyamotoIHom h p * g)⁻¹ * Matrix.GeneralLinearGroup.map σ y *
      (miyamotoIHom h p * g) = y) :
    2 * Nat.card E < (2 ^ f) ^ 4 := by
  have := h.finite
  have hq : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h3 : 2 * (2 ^ f) ^ 3 < (2 ^ f) ^ 4 := by
    rw [pow_succ (2 ^ f) 3, mul_comm ((2 ^ f) ^ 3)]
    exact Nat.mul_lt_mul_of_pos_right hq (by positivity)
  have hle : Nat.card E ≤ (2 ^ f) ^ 3 := by
    by_cases hEA : E ≤ miyamotoA1 h
    · refine (card_le_of_le fun y hy => ?_).trans (card_miyamotoTwistedFixA1_le h σ hσ p hg)
      exact (mem_miyamotoTwistedFixA1 h).2 ⟨hEA hy, hfix y hy⟩
    · exact card_le_of_commute_of_not_le_A1 h hEP hcomm hEA
  omega

end Thompson

section ThompsonModA1

variable [CharP K 2]

theorem miyamotoP_mod_A1 : (∀ x ∈ miyamotoP h, x * x ∈ miyamotoA1 h) ∧
    ∀ x ∈ miyamotoP h, ∀ y ∈ miyamotoP h, ⁅x, y⁆ ∈ miyamotoA1 h := by
  have hbb := h.bar_bar
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨a, b, c, d, hb, -, rfl⟩ := (mem_P h).1 hx
    rw [miyamotoXGL_mul_self h hb]
    refine (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, ?_⟩
    simp only [map_add, map_mul, hbb, hb]
    ring
  · have : ⁅x, y⁆ ∈ miyamotoZ2 h := by
      rw [← commutator_miyamotoP h]
      exact commutator_mem_commutator hx hy
    exact miyamotoZ2_le_A1 h this

theorem two_mul_card_lt_of_twisted_mod_A1 (hf : 2 ≤ f) (σ : K →+* K) (hσ : ∃ k, σ k ≠ k)
    (p : Kˣ × Kˣ) {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) {E : Subgroup (GL (Fin 4) K)}
    (hEP : E ≤ miyamotoP h)
    (hfix : ∀ y ∈ E, (miyamotoIHom h p * g)⁻¹ * Matrix.GeneralLinearGroup.map σ y *
      (miyamotoIHom h p * g) * y⁻¹ ∈ miyamotoA1 h) :
    2 * Nat.card E < (2 ^ f) ^ 6 := by
  have := h.finite
  have hbb := h.bar_bar
  obtain ⟨a₀, β₀, γ₀, δ₀, hβ₀, -, rfl⟩ := (mem_P h).1 hg
  have hq : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set w : K := (p.1 : K) * (p.2 : K)⁻¹
  have hT : ∀ y ∈ E, (y : Matrix (Fin 4) (Fin 4) K) 1 0 ∈ {c : K | c = w * σ c} := by
    intro y hy
    obtain ⟨a, b, c, d, hb, -, rfl⟩ := (mem_P h).1 (hEP hy)
    have e := hfix _ hy
    have hσb : h.bar (σ b) = σ b := by rw [← map_bar h σ, hb]
    have hb' : h.bar ((p.2 : K) * h.bar p.2 * σ b) = (p.2 : K) * h.bar p.2 * σ b := by
      rw [map_mul, map_mul, hbb, hσb]
      ring
    have e' : (miyamotoXGL h a₀ β₀ γ₀ δ₀)⁻¹ * ((miyamotoIHom h p)⁻¹ *
        Matrix.GeneralLinearGroup.map σ (miyamotoXGL h a b c d) * miyamotoIHom h p) *
        miyamotoXGL h a₀ β₀ γ₀ δ₀ * (miyamotoXGL h a b c d)⁻¹ ∈ miyamotoA1 h := by
      have : (miyamotoIHom h p * miyamotoXGL h a₀ β₀ γ₀ δ₀)⁻¹ *
          Matrix.GeneralLinearGroup.map σ (miyamotoXGL h a b c d) *
          (miyamotoIHom h p * miyamotoXGL h a₀ β₀ γ₀ δ₀) * (miyamotoXGL h a b c d)⁻¹ =
          (miyamotoXGL h a₀ β₀ γ₀ δ₀)⁻¹ * ((miyamotoIHom h p)⁻¹ *
          Matrix.GeneralLinearGroup.map σ (miyamotoXGL h a b c d) * miyamotoIHom h p) *
          miyamotoXGL h a₀ β₀ γ₀ δ₀ * (miyamotoXGL h a b c d)⁻¹ := by group
      rw [← this]
      exact e
    rw [map_miyamotoXGL, miyamotoIHom_conj, miyamotoXGL_conj h hβ₀ hb',
      miyamotoXGL_inv h hb, miyamotoXGL_mul h hb'] at e'
    have ha := ((miyamotoXGL_mem_A1 h).1 e').1
    change a = w * σ a
    linear_combination -ha + a * CharTwo.two_eq_zero (R := K)
  have key := card_le_card_inf_mul_ncard (H := E) (N := miyamotoA1 h)
    (fun y : GL (Fin 4) K => (y : Matrix (Fin 4) (Fin 4) K) 1 0) (Set.toFinite _) hT
    (fun y hy y' hy' e => inv_mul_mem_A1_of_coord h (hEP hy) (hEP hy') e)
  have h1 : Nat.card (E ⊓ miyamotoA1 h : Subgroup _) ≤ (2 ^ f) ^ 4 :=
    (card_le_of_le inf_le_right).trans_eq (card_miyamotoA1 h)
  have h2 := ncard_eq_mul_map_le h σ hσ w
  have h3 : Nat.card E ≤ (2 ^ f) ^ 4 * 2 ^ f :=
    key.trans (Nat.mul_le_mul h1 h2)
  have h4 : 2 * ((2 ^ f) ^ 4 * 2 ^ f) < (2 ^ f) ^ 6 := by
    rw [show (2 ^ f) ^ 6 = (2 ^ f) * ((2 ^ f) ^ 4 * 2 ^ f) by ring]
    exact Nat.mul_lt_mul_of_pos_right hq (by positivity)
  omega

end ThompsonModA1

end CFSG.LocalAnalysis.EvenBN.U4
