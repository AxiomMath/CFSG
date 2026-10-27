module

import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPhaseThree
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

structure AltScalar (p : ℕ) (K X : Subgroup G) (c₀ c₁ s : G) (g : ℕ) : Prop where
  span : X = Subgroup.zpowers c₀ ⊔ Subgroup.zpowers c₁
  mem : s ∈ K
  normalizes : s ∈ Subgroup.normalizer (X : Set G)
  order_g : orderOf (g : ZMod p) = p - 1
  conj_zero : s * c₀ * s⁻¹ = c₁
  conj_one : s * c₁ * s⁻¹ = c₀ ^ g

structure D2AltData (p : ℕ) [Fact p.Prime] (M H R X : Subgroup G) : Prop where
  pair : AGLPair p M H R
  five_le : 5 ≤ p
  eq_R : X = R
  elem : IsElemAbelian p X
  card : Nat.card X = p ^ 2
  scalar : ∃ (c₀ c₁ s : G) (g : ℕ), AltScalar p (H ⊓ M) X c₀ c₁ s g
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y
  pcore_le : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    (∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ GLBPrimeCore p H) → Y ≤ GLBPrimeCore p H
  centralizer_le : ∀ d ∈ H ⊓ M, (∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ GLBPrimeCore p H) →
    d ∈ R ⊔ GLBPrimeCore p H
  pRank_le : Open.pRank p (H ⊓ M) ≤ 2
  perfect : ∃ (c₀ c₁ s : G) (g : ℕ) (W : Subgroup G)
      (ψ : W →* alternatingGroup (Fin p) × alternatingGroup (Fin p)),
    AltScalar p (H ⊓ M) X c₀ c₁ s g ∧ W ≤ H ⊓ M ∧ ⁅W, W⁆ = W ∧ X ≤ W ∧
    H ⊓ M ≤ Subgroup.normalizer (W : Set G) ∧ Function.Surjective ψ ∧
    ψ.ker = (GLBPrimeCore p H).subgroupOf W ∧
    (∀ w : W, (w : G) = c₀ → (ψ w).2 = 1) ∧ (∀ w : W, (w : G) = c₁ → (ψ w).1 = 1) ∧
    ∀ w w' : W, (w' : G) = s * w * s⁻¹ →
      ((ψ w).2 = 1 → (ψ w').1 = 1) ∧ ((ψ w).1 = 1 → (ψ w').2 = 1)

section Scalar

namespace AltData

omit [Finite G] in
theorem mem_sup_of_forall_commute {S T : Subgroup G} (hc : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a)
    {x : G} (hx : x ∈ S ⊔ T) : ∃ a ∈ S, ∃ b ∈ T, x = a * b := by
  rw [← Subgroup.closure_eq S, ← Subgroup.closure_eq T, ← Subgroup.closure_union] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ a ∈ S, ∃ b ∈ T, x = a * b) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, T.one_mem, by simp⟩
    · exact ⟨1, S.one_mem, x, hx, by simp⟩
  · exact ⟨1, S.one_mem, 1, T.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', S.mul_mem ha ha', b * b', T.mul_mem hb hb', ?_⟩
    have := hc a' ha' b hb
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← this]
      _ = a * a' * (b * b') := by group
  · rintro _ _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, S.inv_mem ha, b⁻¹, T.inv_mem hb, ?_⟩
    have := hc a⁻¹ (S.inv_mem ha) b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = a⁻¹ * b⁻¹ := by
        have h2 := hc a⁻¹ (S.inv_mem ha) b⁻¹ (T.inv_mem hb)
        exact h2.symm

omit [Finite G] in
theorem not_sq_of_orderOf_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {g a : ZMod p}
    (hg : orderOf g = p - 1) (hga : g = a ^ 2) : False := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have ha : a ≠ 0 := by
    rintro rfl
    rw [hga, zero_pow two_ne_zero, orderOf_zero] at hg
    omega
  have h1 : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have hpk : p - 1 = 2 * k := by omega
  have h2 : g ^ k = 1 := by
    rw [hga, ← pow_mul, ← hpk]
    exact h1
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hg] at h3
  have := Nat.le_of_dvd (by omega) h3
  omega

end AltData

namespace AltScalar

variable {p : ℕ} {K X : Subgroup G} {c₀ c₁ s : G} {g : ℕ}

omit [Finite G] in
theorem mem_zero (h : AltScalar p K X c₀ c₁ s g) : c₀ ∈ X :=
  h.span ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c₀)

omit [Finite G] in
theorem mem_one (h : AltScalar p K X c₀ c₁ s g) : c₁ ∈ X :=
  h.span ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c₁)

omit [Finite G] in
theorem exists_zpow_eq (h : AltScalar p K X c₀ c₁ s g) (hX : IsMulCommutative X) {x : G}
    (hx : x ∈ X) : ∃ i j : ℤ, x = c₀ ^ i * c₁ ^ j := by
  have hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.1 hX ⟨a, ha⟩ ⟨b, hb⟩)
  rw [h.span] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := AltData.mem_sup_of_forall_commute (S := Subgroup.zpowers c₀)
    (T := Subgroup.zpowers c₁) (fun a ha b hb => hc a (h.span ▸ Subgroup.mem_sup_left ha) b
      (h.span ▸ Subgroup.mem_sup_right hb)) hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact ⟨i, j, rfl⟩

omit [Finite G] in
theorem sq_conj (h : AltScalar p K X c₀ c₁ s g) (hX : IsMulCommutative X) {x : G} (hx : x ∈ X) :
    s * (s * x * s⁻¹) * s⁻¹ = x ^ g := by
  obtain ⟨i, j, rfl⟩ := h.exists_zpow_eq hX hx
  have hcomm : Commute c₀ c₁ := congrArg Subtype.val (isMulCommutative_iff.1 hX
    ⟨c₀, h.mem_zero⟩ ⟨c₁, h.mem_one⟩)
  have e1 : s * (c₀ ^ i * c₁ ^ j) * s⁻¹ = c₁ ^ i * (c₀ ^ g) ^ j := by
    have : s * (c₀ ^ i * c₁ ^ j) * s⁻¹ = (s * c₀ * s⁻¹) ^ i * (s * c₁ * s⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]
      group
    rw [this, h.conj_zero, h.conj_one]
  have e2 : s * (c₁ ^ i * (c₀ ^ g) ^ j) * s⁻¹ = (c₀ ^ g) ^ i * (c₁ ^ g) ^ j := by
    have : s * (c₁ ^ i * (c₀ ^ g) ^ j) * s⁻¹ =
        (s * c₁ * s⁻¹) ^ i * ((s * c₀ * s⁻¹) ^ g) ^ j := by
      rw [conj_pow, conj_zpow, conj_zpow]
      group
    rw [this, h.conj_one, h.conj_zero]
  have hpw : ∀ (a : G) (k : ℤ), (a ^ g) ^ k = (a ^ k) ^ g := fun a k => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [e1, e2, (hcomm.zpow_zpow i j).mul_pow, hpw, hpw]

omit [Finite G] in
theorem not_mem_normalizer [Fact p.Prime] (h : AltScalar p K X c₀ c₁ s g) (hp2 : p ≠ 2)
    (hX : IsElemAbelian p X) {Y : Subgroup G} (hYX : Y ≤ X) (hY : Nat.card Y = p) :
    s ∉ Subgroup.normalizer (Y : Set G) := by
  intro hs
  have hp : p.Prime := Fact.out
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; exact hp.ne_zero)
  have : IsCyclic Y := isCyclic_of_prime_card hY
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := Y)
  have hy1 : (y : G) ≠ 1 := by
    intro h1
    have hbot : Y = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hy ⟨z, hz⟩)
      have := congrArg Subtype.val hm
      simpa [h1] using this.symm
    rw [hbot, Subgroup.card_bot] at hY
    have := hp.two_le
    omega
  have hord : orderOf (y : G) = p := orderOf_eq_prime (hX.2 _ (hYX y.2)) hy1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
    (hy ⟨s * (y : G) * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs y).mp y.2⟩)
  have hm' : (y : G) ^ m = s * y * s⁻¹ := congrArg Subtype.val hm
  have h1 := h.sq_conj hX.1 (hYX y.2)
  have h2 : s * (s * (y : G) * s⁻¹) * s⁻¹ = (y : G) ^ (m * m) := by
    rw [← hm', ← conj_zpow, ← hm', ← zpow_mul]
  have h3 : (y : G) ^ (g : ℤ) = (y : G) ^ (m * m) := by
    rw [zpow_natCast, ← h1, h2]
  have h4 := zpow_eq_zpow_iff_modEq.mp h3
  rw [hord] at h4
  have h5 : (g : ZMod p) = (m : ZMod p) ^ 2 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ p).mpr h4
    simpa [sq] using this
  exact AltData.not_sq_of_orderOf_eq hp2 h.order_g h5

end AltScalar

end Scalar

namespace D2AltData

variable {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

theorem scalar_no_fixed_line (h : D2AltData p M H R X) :
    ∃ (s : G) (g : ℕ), s ∈ H ⊓ M ∧ s ∈ Subgroup.normalizer (X : Set G) ∧
      orderOf (g : ZMod p) = p - 1 ∧ (g : ZMod p) ≠ 1 ∧
      (∀ x ∈ X, s * (s * x * s⁻¹) * s⁻¹ = x ^ g) ∧
      ∀ Y : Subgroup G, Y ≤ X → Nat.card Y = p → s ∉ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨c₀, c₁, s, g, hsc⟩ := h.scalar
  refine ⟨s, g, hsc.mem, hsc.normalizes, hsc.order_g, ?_, fun x hx => hsc.sq_conj h.elem.1 hx,
    fun Y hYX hY => hsc.not_mem_normalizer h.pair.ne_two h.elem hYX hY⟩
  intro h1
  have hp := h.pair.prime
  have hp2 := h.pair.ne_two
  have := hsc.order_g
  rw [h1, orderOf_one] at this
  have := hp.two_le
  omega

theorem pCore_eq_bot (h : D2AltData p M H R X) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ := by
  have h3 := h.pair
  by_contra hO
  apply h3.pCorePreimage_not_le hO
  refine h.pcore_le _ (h3.pCorePreimage_le_inf h84 hD2)
    (inf_le_right.trans (le_normalizer_pCorePreimage p M)) ?_
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ CFSG.pCore 2 ↥M)
    ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hm⟩
  refine ⟨k, ?_⟩
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (m ^ p ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  simpa using h3.twoCore_M_le_glbPrimeCore (coe_mem_pCoreOf_two_of_mk_eq_one _ hk')

end D2AltData

end CFSG.AGLEmbeddingD2
