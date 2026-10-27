module

public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.AS16.E2.Outer1

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG.GH74.KGroups

structure OuterTable (K : Type*) [Group K] : Prop where
  outer_cent3 : ∀ τ : MulAut K, τ ^ 2 = 1 → ¬ IsInn τ → ∀ ψ : MulAut K,
    (∀ c : K, orderOf c = 3 → τ c = c → ψ c = c) → ψ = 1 ∨ ψ = τ
  bang : ∀ τ : MulAut K, τ ^ 2 = 1 → ¬ IsInn τ → ∃ l c₁ c₂ : K, orderOf c₁ = 3 ∧ orderOf c₂ = 3 ∧
    τ c₁ = c₁ ∧ τ c₂ = c₂ ∧ (c₁ * c₂) ^ 2 = 1 ∧ c₁ * c₂ ≠ 1 ∧ τ l * l⁻¹ = c₁ * c₂
  inner_sq : ∀ v : K, orderOf v = 2 → ∀ ψ : MulAut K,
    (∀ c : K, orderOf c = 3 → c * v = v * c → ψ c = c) →
      (ψ ^ 2 = 1 ∨ ψ ^ 2 = MulAut.conj v) ∧
      (IsInn ψ → ψ ^ 2 = 1 → ψ = 1 ∨ ψ = MulAut.conj v)

structure OuterSylowTable (K : Type*) [Group K] (Q : Subgroup K) : Prop where
  exists_s : ∃ s ∈ Q, s ≠ 1 ∧ s ^ 2 = 1 ∧ (∀ q ∈ Q, q * s = s * q) ∧
    (∀ a ∈ Q, (∀ q ∈ Q, q * a = a * q) → a ^ 2 = 1 → a = 1 ∨ a = s) ∧
    (∀ ψ : MulAut K, (∀ q ∈ Q, ψ q = q) →
      ∃ a ∈ Q, (∀ q ∈ Q, q * a = a * q) ∧ ψ = MulAut.conj a) ∧
    (∃ a b : K, orderOf a = 3 ∧ orderOf b = 3 ∧ a * s = s * a ∧ b * s = s * b ∧
      (a * b) ^ 3 = s)
  sq : ∀ ψ : MulAut K, ¬ IsInn ψ → (∀ q ∈ Q, ψ q ∈ Q) → ∀ v ∈ Q, orderOf v = 2 →
    (∀ c : K, orderOf c = 3 → c * v = v * c → ψ c = c) → ψ ^ 2 = MulAut.conj v →
      ∀ q ∈ Q, q * v = v * q
  conj4 : ∀ a ∈ Q, orderOf a = 4 →
    (∀ c : K, orderOf c = 3 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
    ∃ k : K, k⁻¹ * a * k ∈ Q ∧ ∀ y ∈ Q, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y

structure OuterCycTable (K : Type*) [Group K] : Prop where
  cyc : ∀ v : K, orderOf v = 2 → ∃ φ : MulAut K, ∀ ψ : MulAut K,
    (∀ c : K, orderOf c = 3 → c * v = v * c → ψ c = c) → ψ ∈ Subgroup.zpowers φ

section Model

variable {K : Type*} [Group K] {G : Type*} [Group G]

@[expose] def AM.twist (M : AutModel K G) (e' : K ≃* M.P) : AutModel K G where
  P := M.P
  A := M.A
  e := e'
  Φ := (MulAut.conj (e'.trans M.e.symm : MulAut K)).trans M.Φ
  spec := by
    intro φ x
    set θ : MulAut K := e'.trans M.e.symm with hθ
    have h1 := M.spec (θ * φ * θ⁻¹) (θ x)
    have e1 : (θ * φ * θ⁻¹) (θ x) = θ (φ x) := by
      simp [MulAut.mul_apply, MulAut.inv_apply]
    have e2 : ∀ y : K, M.e (θ y) = e' y := by
      intro y
      simp [hθ]
    rw [e1, e2, e2] at h1
    exact h1

theorem AM.Φ_conj (M : AutModel K G) (hPA : M.P ≤ M.A) (k : K) :
    (M.Φ (MulAut.conj k) : G) = (M.e k : G) := by
  set a : M.A := ⟨(M.e k : G), hPA (M.e k).2⟩ with ha
  set ψ : MulAut K := M.Φ.symm a with hψ
  have hΦψ : M.Φ ψ = a := M.Φ.apply_symm_apply a
  have hψ' : ψ = MulAut.conj k := by
    ext x
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec ψ x, hΦψ]
    simp [ha, MulAut.conj_apply]
  rw [← hψ', hΦψ]

theorem AM.isInn_iff (M : AutModel K G) (hPA : M.P ≤ M.A) (φ : MulAut K) :
    IsInn φ ↔ (M.Φ φ : G) ∈ M.P := by
  constructor
  · rintro ⟨k, hk⟩
    have : φ = MulAut.conj k := by
      ext x
      simpa [MulAut.conj_apply] using hk x
    rw [this, AM.Φ_conj M hPA k]
    exact (M.e k).2
  · intro h
    exact M.inner_of_mem φ h

theorem AM.fix_iff (M : AutModel K G) (φ : MulAut K) (x : K) :
    φ x = x ↔ (M.Φ φ : G) * (M.e x : G) = (M.e x : G) * (M.Φ φ : G) := by
  have h := M.spec φ x
  constructor
  · intro hx
    rw [hx] at h
    calc (M.Φ φ : G) * (M.e x : G)
        = ((M.Φ φ : G) * (M.e x : G) * (M.Φ φ : G)⁻¹) * (M.Φ φ : G) := by group
      _ = (M.e x : G) * (M.Φ φ : G) := by rw [← h]
  · intro hc
    apply M.e.injective
    apply Subtype.ext
    rw [h]
    calc (M.Φ φ : G) * (M.e x : G) * (M.Φ φ : G)⁻¹
        = ((M.e x : G) * (M.Φ φ : G)) * (M.Φ φ : G)⁻¹ := by rw [hc]
      _ = (M.e x : G) := by group

theorem AM.pow_e (M : AutModel K G) (c : K) (n : ℕ) :
    ((M.e c : M.P) : G) ^ n = ((M.e (c ^ n) : M.P) : G) := by
  rw [map_pow]
  rfl

theorem AM.e_eq_one (M : AutModel K G) {c : K} : ((M.e c : M.P) : G) = 1 ↔ c = 1 := by
  constructor
  · intro h
    apply M.e.injective
    apply Subtype.ext
    rw [h]
    simp
  · rintro rfl
    simp

theorem AM.exists_e (M : AutModel K G) {c' : G} (hc' : c' ∈ M.P) :
    ∃ c : K, ((M.e c : M.P) : G) = c' :=
  ⟨M.e.symm ⟨c', hc'⟩, by simp⟩

theorem AM.e_mul (M : AutModel K G) (a b : K) :
    ((M.e (a * b) : M.P) : G) = ((M.e a : M.P) : G) * ((M.e b : M.P) : G) := by
  simp

theorem AM.e_inv (M : AutModel K G) (a : K) :
    ((M.e a⁻¹ : M.P) : G) = ((M.e a : M.P) : G)⁻¹ := by
  simp

theorem AM.orderOf_three_iff (M : AutModel K G) (c : K) :
    orderOf c = 3 ↔ ((M.e c : M.P) : G) ^ 3 = 1 ∧ ((M.e c : M.P) : G) ≠ 1 := by
  constructor
  · intro h
    refine ⟨?_, fun h1 => ?_⟩
    · rw [AM.pow_e M, ← h, pow_orderOf_eq_one]
      simp
    · have := (AM.e_eq_one M).1 h1
      rw [this, orderOf_one] at h
      omega
  · rintro ⟨h3, h1⟩
    have h3' : c ^ 3 = 1 := by
      have : ((M.e (c ^ 3) : M.P) : G) = 1 := by rw [← AM.pow_e M]; exact h3
      exact (AM.e_eq_one M).1 this
    refine orderOf_eq_prime h3' (fun h => h1 ?_)
    rw [h]
    simp


theorem AM.fix_of_comm (M : AutModel K G) (v : K) (ψ : MulAut K)
    (hfix : ∀ c : K, orderOf c = 3 → c * v = v * c → ψ c = c) :
    ∀ c' ∈ M.P, c' ^ 3 = 1 → c' * ((M.e v : M.P) : G) = ((M.e v : M.P) : G) * c' →
      (M.Φ ψ : G) * c' = c' * (M.Φ ψ : G) := by
  intro c' hc'P hc'3 hc'v
  obtain ⟨c, rfl⟩ := AM.exists_e M hc'P
  by_cases hc1 : c = 1
  · rw [hc1]
    simp
  · have hc3 : orderOf c = 3 :=
      (AM.orderOf_three_iff M c).2 ⟨hc'3, fun h => hc1 ((AM.e_eq_one M).1 h)⟩
    have hcv : c * v = v * c := by
      apply M.e.injective
      apply Subtype.ext
      rw [AM.e_mul M, AM.e_mul M]
      exact hc'v
    exact (AM.fix_iff M ψ c).1 (hfix c hc3 hcv)


theorem outerTable_of_model (M : AutModel K G) (hPA : M.P ≤ M.A)
    (h1 : ∀ τ ∈ M.A, τ ^ 2 = 1 → τ ∉ M.P → ∀ ψ ∈ M.A,
      (∀ c ∈ M.P, c ^ 3 = 1 → c * τ = τ * c → ψ * c = c * ψ) → ψ = 1 ∨ ψ = τ)
    (h2 : ∀ τ ∈ M.A, τ ^ 2 = 1 → τ ∉ M.P → ∃ l ∈ M.P, ∃ c₁ ∈ M.P, ∃ c₂ ∈ M.P, c₁ ^ 3 = 1 ∧
      c₂ ^ 3 = 1 ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧ c₁ * τ = τ * c₁ ∧ c₂ * τ = τ * c₂ ∧ (c₁ * c₂) ^ 2 = 1 ∧
      c₁ * c₂ ≠ 1 ∧ τ * l * τ⁻¹ * l⁻¹ = c₁ * c₂)
    (h3 : ∀ v ∈ M.P, v ^ 2 = 1 → v ≠ 1 → ∀ ψ ∈ M.A,
      (∀ c ∈ M.P, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) →
      (ψ ^ 2 = 1 ∨ ψ ^ 2 = v) ∧ (ψ ∈ M.P → ψ ^ 2 = 1 → ψ = 1 ∨ ψ = v)) :
    OuterTable K where
  outer_cent3 := by
    intro τ hτ2 hτi ψ hψ
    have hτ2' : (M.Φ τ : G) ^ 2 = 1 := by rw [← M.Φ_pow, hτ2, M.Φ_one]
    have hτP : (M.Φ τ : G) ∉ M.P := fun h => hτi ((AM.isInn_iff M hPA τ).2 h)
    have key := h1 (M.Φ τ) (M.Φ τ).2 hτ2' hτP (M.Φ ψ) (M.Φ ψ).2 (by
      intro c' hc'P hc'3 hc'τ
      obtain ⟨c, rfl⟩ := AM.exists_e M hc'P
      by_cases hc1 : c = 1
      · rw [hc1]
        simp
      · have hc3 : orderOf c = 3 := by
          rw [AM.orderOf_three_iff M]
          exact ⟨hc'3, fun h => hc1 ((AM.e_eq_one M).1 h)⟩
        have hτc : τ c = c := (AM.fix_iff M τ c).2 hc'τ.symm
        exact ((AM.fix_iff M ψ c).1 (hψ c hc3 hτc)))
    rcases key with h | h
    · exact Or.inl ((M.Φ_eq_one).1 h)
    · right
      apply M.Φ.injective
      exact Subtype.ext h
  bang := by
    intro τ hτ2 hτi
    have hτ2' : (M.Φ τ : G) ^ 2 = 1 := by rw [← M.Φ_pow, hτ2, M.Φ_one]
    have hτP : (M.Φ τ : G) ∉ M.P := fun h => hτi ((AM.isInn_iff M hPA τ).2 h)
    obtain ⟨l', hl', c₁', hc₁', c₂', hc₂', hc₁3, hc₂3, hc₁1, hc₂1, hc₁τ, hc₂τ, hw2, hw1, hlτ⟩ :=
      h2 _ (M.Φ τ).2 hτ2' hτP
    obtain ⟨l, rfl⟩ := AM.exists_e M hl'
    obtain ⟨c₁, rfl⟩ := AM.exists_e M hc₁'
    obtain ⟨c₂, rfl⟩ := AM.exists_e M hc₂'
    refine ⟨l, c₁, c₂, (AM.orderOf_three_iff M c₁).2 ⟨hc₁3, hc₁1⟩,
      (AM.orderOf_three_iff M c₂).2 ⟨hc₂3, hc₂1⟩, (AM.fix_iff M τ c₁).2 hc₁τ.symm,
      (AM.fix_iff M τ c₂).2 hc₂τ.symm, ?_, ?_, ?_⟩
    · apply (AM.e_eq_one M).1
      rw [← AM.pow_e M, AM.e_mul M]
      exact hw2
    · intro h
      apply hw1
      rw [← AM.e_mul M, h]
      simp
    · apply M.e.injective
      apply Subtype.ext
      rw [AM.e_mul M, AM.e_mul M, AM.e_inv M, M.spec τ l]
      exact hlτ
  inner_sq := by
    intro v hv2 ψ hψ
    have hv2' : v ^ 2 = 1 := hv2 ▸ pow_orderOf_eq_one v
    have hv'2 : ((M.e v : M.P) : G) ^ 2 = 1 := by
      rw [AM.pow_e M, hv2']
      simp
    have hv'1 : ((M.e v : M.P) : G) ≠ 1 := by
      intro h
      have := (AM.e_eq_one M).1 h
      rw [this, orderOf_one] at hv2
      omega
    have key := h3 _ (M.e v).2 hv'2 hv'1 (M.Φ ψ) (M.Φ ψ).2 (AM.fix_of_comm M v ψ hψ)
    have hΦsq : (M.Φ (ψ ^ 2) : G) = (M.Φ ψ : G) ^ 2 := M.Φ_pow ψ 2
    refine ⟨?_, ?_⟩
    · rcases key.1 with h | h
      · left
        apply (M.Φ_eq_one).1
        rw [hΦsq]
        exact h
      · right
        apply M.Φ.injective
        apply Subtype.ext
        rw [hΦsq, AM.Φ_conj M hPA]
        exact h
    · intro hinn hψ2
      have hP : (M.Φ ψ : G) ∈ M.P := (AM.isInn_iff M hPA ψ).1 hinn
      have hψ2' : (M.Φ ψ : G) ^ 2 = 1 := by rw [← hΦsq, hψ2, M.Φ_one]
      rcases key.2 hP hψ2' with h | h
      · left
        exact (M.Φ_eq_one).1 h
      · right
        apply M.Φ.injective
        apply Subtype.ext
        rw [AM.Φ_conj M hPA]
        exact h


theorem outerSylowTable_of_model (M : AutModel K G) (hPA : M.P ≤ M.A) {S : Subgroup G}
    (hSP : S ≤ M.P) {Q : Subgroup K} (hQ : ∀ k : K, k ∈ Q ↔ ((M.e k : M.P) : G) ∈ S)
    (hs : ∃ s ∈ S, s ≠ 1 ∧ s ^ 2 = 1 ∧ (∀ q ∈ S, q * s = s * q) ∧
      (∀ a ∈ S, (∀ q ∈ S, q * a = a * q) → a ^ 2 = 1 → a = 1 ∨ a = s) ∧
      (∀ ψ ∈ M.A, (∀ q ∈ S, q * ψ = ψ * q) → ψ ∈ S) ∧
      (∃ a ∈ M.P, ∃ b ∈ M.P, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * s = s * a ∧
        b * s = s * b ∧ (a * b) ^ 3 = s))
    (hsq : ∀ ψ ∈ M.A, ψ ∉ M.P → (∀ q ∈ S, ψ * q * ψ⁻¹ ∈ S) → ∀ v ∈ S, v ^ 2 = 1 → v ≠ 1 →
      (∀ c ∈ M.P, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) → ψ ^ 2 = v →
        ∀ q ∈ S, q * v = v * q)
    (hconj4 : ∀ a ∈ S, a ^ 4 = 1 → a ^ 2 ≠ 1 →
      (∀ c ∈ M.P, c ^ 3 = 1 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
      ∃ k ∈ M.P, k⁻¹ * a * k ∈ S ∧ ∀ y ∈ S, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y) :
    OuterSylowTable K Q := by
  have hSQ : ∀ y' ∈ S, ∃ y ∈ Q, ((M.e y : M.P) : G) = y' := by
    intro y' hy'
    obtain ⟨y, hy⟩ := AM.exists_e M (hSP hy')
    exact ⟨y, (hQ y).2 (by rw [hy]; exact hy'), hy⟩
  have hcentQ : ∀ x : K, (∀ q ∈ Q, q * x = x * q) ↔
      ∀ q' ∈ S, q' * ((M.e x : M.P) : G) = ((M.e x : M.P) : G) * q' := by
    intro x
    constructor
    · intro h q' hq'
      obtain ⟨q, hq, rfl⟩ := hSQ q' hq'
      have := congrArg (fun w : K => ((M.e w : M.P) : G)) (h q hq)
      simpa [AM.e_mul M] using this
    · intro h q hq
      apply M.e.injective
      apply Subtype.ext
      rw [AM.e_mul M, AM.e_mul M]
      exact h _ ((hQ q).1 hq)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s', hs'S, hs'1, hs'2, hs'c, hs'u, hscent, a', ha'P, b', hb'P, ha'3, hb'3, ha'1, hb'1,
      ha's, hb's, hab⟩ := hs
    obtain ⟨s, hs_e⟩ := AM.exists_e M (hSP hs'S)
    have hsQ : s ∈ Q := (hQ s).2 (by rw [hs_e]; exact hs'S)
    have hs1 : s ≠ 1 := by
      intro h
      apply hs'1
      rw [← hs_e, h]
      simp
    have hs2 : s ^ 2 = 1 := by
      apply (AM.e_eq_one M).1
      rw [← AM.pow_e M, hs_e]
      exact hs'2
    refine ⟨s, hsQ, hs1, hs2, ?_, ?_, ?_, ?_⟩
    · exact (hcentQ s).2 (by rw [hs_e]; exact fun q' hq' => hs'c q' hq')
    · intro a haQ hac ha2
      have h1 := (hcentQ a).1 hac
      have h2 : ((M.e a : M.P) : G) ^ 2 = 1 := by
        rw [AM.pow_e M, ha2]
        simp
      rcases hs'u _ ((hQ a).1 haQ) h1 h2 with h | h
      · exact Or.inl ((AM.e_eq_one M).1 h)
      · right
        rw [← hs_e] at h
        apply M.e.injective
        exact Subtype.ext h
    · intro ψ hψ
      have hfix : ∀ q' ∈ S, q' * (M.Φ ψ : G) = (M.Φ ψ : G) * q' := by
        intro q' hq'
        obtain ⟨q, hq, rfl⟩ := hSQ q' hq'
        exact ((AM.fix_iff M ψ q).1 (hψ q hq)).symm
      have hΦS := hscent _ (M.Φ ψ).2 hfix
      obtain ⟨a, haQ, ha⟩ := hSQ _ hΦS
      refine ⟨a, haQ, (hcentQ a).2 (by rw [ha]; exact hfix), ?_⟩
      apply M.Φ.injective
      apply Subtype.ext
      rw [AM.Φ_conj M hPA, ha]
    · obtain ⟨a, ha_e⟩ := AM.exists_e M ha'P
      obtain ⟨b, hb_e⟩ := AM.exists_e M hb'P
      refine ⟨a, b, (AM.orderOf_three_iff M a).2 ⟨by rw [ha_e]; exact ha'3, by rw [ha_e]; exact ha'1⟩,
        (AM.orderOf_three_iff M b).2 ⟨by rw [hb_e]; exact hb'3, by rw [hb_e]; exact hb'1⟩, ?_, ?_, ?_⟩
      · apply M.e.injective
        apply Subtype.ext
        rw [AM.e_mul M, AM.e_mul M, ha_e, hs_e]
        exact ha's
      · apply M.e.injective
        apply Subtype.ext
        rw [AM.e_mul M, AM.e_mul M, hb_e, hs_e]
        exact hb's
      · apply M.e.injective
        apply Subtype.ext
        rw [← AM.pow_e M, AM.e_mul M, ha_e, hb_e, hs_e]
        exact hab
  · intro ψ hψi hψQ v hvQ hv2 hfix hψ2 q hq
    have hψP : (M.Φ ψ : G) ∉ M.P := fun h' => hψi ((AM.isInn_iff M hPA ψ).2 h')
    have hv2' : v ^ 2 = 1 := hv2 ▸ pow_orderOf_eq_one v
    have hv'S : ((M.e v : M.P) : G) ∈ S := (hQ v).1 hvQ
    have hv'2 : ((M.e v : M.P) : G) ^ 2 = 1 := by
      rw [AM.pow_e M, hv2']
      simp
    have hv'1 : ((M.e v : M.P) : G) ≠ 1 := by
      intro h
      have := (AM.e_eq_one M).1 h
      rw [this, orderOf_one] at hv2
      omega
    have hψa : ∀ q' ∈ S, (M.Φ ψ : G) * q' * (M.Φ ψ : G)⁻¹ ∈ S := by
      intro q' hq'
      obtain ⟨q₀, hq₀, rfl⟩ := hSQ q' hq'
      rw [← M.spec ψ q₀]
      exact (hQ _).1 (hψQ q₀ hq₀)
    have key := hsq (M.Φ ψ) (M.Φ ψ).2 hψP hψa _ hv'S hv'2 hv'1 (AM.fix_of_comm M v ψ hfix)
      (by rw [← M.Φ_pow, hψ2, AM.Φ_conj M hPA]) ((M.e q : M.P) : G) ((hQ q).1 hq)
    apply M.e.injective
    apply Subtype.ext
    rw [AM.e_mul M, AM.e_mul M]
    exact key
  · intro a haQ ha4 hfix
    have ha4' : a ^ 4 = 1 := ha4 ▸ pow_orderOf_eq_one a
    have ha'S : ((M.e a : M.P) : G) ∈ S := (hQ a).1 haQ
    have ha'4 : ((M.e a : M.P) : G) ^ 4 = 1 := by
      rw [AM.pow_e M, ha4']
      simp
    have ha'2 : ((M.e a : M.P) : G) ^ 2 ≠ 1 := by
      intro h'
      have h2 : a ^ 2 = 1 := by
        apply (AM.e_eq_one M).1
        rw [← AM.pow_e M]
        exact h'
      have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [ha4] at this
      omega
    obtain ⟨k', hk'P, hk'S, hk'c⟩ := hconj4 _ ha'S ha'4 ha'2 (by
      intro c' hc'P hc'3 hc'a
      obtain ⟨c, rfl⟩ := AM.exists_e M hc'P
      by_cases hc1 : c = 1
      · rw [hc1]
        simp
      · have hc3 : orderOf c = 3 :=
          (AM.orderOf_three_iff M c).2 ⟨hc'3, fun h => hc1 ((AM.e_eq_one M).1 h)⟩
        have hca : c * a ^ 2 = a ^ 2 * c := by
          apply M.e.injective
          apply Subtype.ext
          rw [AM.e_mul M, AM.e_mul M, ← AM.pow_e M]
          exact hc'a
        have := hfix c hc3 hca
        have h2 := congrArg (fun w : K => ((M.e w : M.P) : G)) this
        simpa [AM.e_mul M] using h2)
    obtain ⟨k, rfl⟩ := AM.exists_e M hk'P
    refine ⟨k, (hQ _).2 (by rw [AM.e_mul M, AM.e_mul M, AM.e_inv M]; exact hk'S), (hcentQ _).2 ?_⟩
    intro y' hy'
    have := hk'c y' hy'
    rw [AM.e_mul M, AM.e_mul M, AM.e_inv M]
    exact this

theorem outerCycTable_of_model (M : AutModel K G) (_hPA : M.P ≤ M.A)
    (h : ∀ v ∈ M.P, v ^ 2 = 1 → v ≠ 1 → ∃ φ ∈ M.A, ∀ ψ ∈ M.A,
      (∀ c ∈ M.P, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) → ∃ k : ℕ, ψ = φ ^ k) :
    OuterCycTable K where
  cyc := by
    intro v hv2
    have hv2' : v ^ 2 = 1 := hv2 ▸ pow_orderOf_eq_one v
    have hv'2 : ((M.e v : M.P) : G) ^ 2 = 1 := by
      rw [AM.pow_e M, hv2']
      simp
    have hv'1 : ((M.e v : M.P) : G) ≠ 1 := by
      intro h
      have := (AM.e_eq_one M).1 h
      rw [this, orderOf_one] at hv2
      omega
    obtain ⟨φ', hφ'A, hφ'⟩ := h _ (M.e v).2 hv'2 hv'1
    refine ⟨M.Φ.symm ⟨φ', hφ'A⟩, fun ψ hψ => ?_⟩
    obtain ⟨k, hk⟩ := hφ' (M.Φ ψ) (M.Φ ψ).2 (AM.fix_of_comm M v ψ hψ)
    have : ψ = (M.Φ.symm ⟨φ', hφ'A⟩) ^ k := by
      apply M.Φ.injective
      apply Subtype.ext
      rw [map_pow]
      simpa using hk
    rw [this]
    exact (zpowers (M.Φ.symm ⟨φ', hφ'A⟩)).pow_mem (mem_zpowers _) k

end Model

end CFSG.GH74.AS16.E2
