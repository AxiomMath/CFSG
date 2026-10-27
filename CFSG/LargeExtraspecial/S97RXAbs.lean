module

public import CFSG.CGT.Timmesfeld75.WCBasic

public section

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.CGT.Timmesfeld75

theorem mem_normalizer_conj_iff97 {K : Type*} [Group K] {x y : K} {U : Subgroup K} :
    y ∈ normalizer (conjSubgroup x U : Set K) ↔ x⁻¹ * y * x ∈ normalizer (U : Set K) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, mem_normalizer_iff_conjSubgroup_eq,
    conjSubgroup_conjSubgroup, show y * x = x * (x⁻¹ * y * x) by group,
    ← conjSubgroup_conjSubgroup, conjSubgroup_inj]

theorem free_orbit {D V : Type*} [Group D] [Fintype D] [AddCommMonoid V] [DecidableEq V]
    (σ : D → V → V) (hσ1 : ∀ v, σ 1 v = v) (hσm : ∀ d e v, σ (d * e) v = σ d (σ e v))
    (s : Finset V) (hs : ∀ d, ∀ v ∈ s, σ d v ∈ s) (hfree : ∀ d, ∀ v ∈ s, σ d v = v → d = 1) :
    Fintype.card D ∣ s.card ∧ ((∀ v ∈ s, ∑ d, σ d v = 0) → ∑ v ∈ s, v = 0) := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · simp
  set O := Finset.univ.image (fun d => σ d v₀) with hO
  have hinj : Function.Injective (fun d => σ d v₀) := by
    intro d e hde
    have h1 : σ (e⁻¹ * d) v₀ = v₀ := by
      rw [hσm]
      simp only at hde
      rw [hde, ← hσm, inv_mul_cancel, hσ1]
    exact (inv_mul_eq_one.mp (hfree _ v₀ hv₀ h1)).symm
  have hOs : O ⊆ s := by
    intro w hw
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hw
    exact hs d v₀ hv₀
  have hOc : O.card = Fintype.card D := by
    rw [hO, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hs' : ∀ d, ∀ v ∈ s \ O, σ d v ∈ s \ O := by
    intro d v hv
    rw [Finset.mem_sdiff] at hv ⊢
    refine ⟨hs d v hv.1, fun hmem => hv.2 ?_⟩
    obtain ⟨e, -, he⟩ := Finset.mem_image.mp hmem
    refine Finset.mem_image.mpr ⟨d⁻¹ * e, Finset.mem_univ _, ?_⟩
    rw [hσm, he, ← hσm, inv_mul_cancel, hσ1]
  have hlt : s \ O ⊂ s :=
    Finset.sdiff_ssubset hOs ⟨v₀, Finset.mem_image.mpr ⟨1, Finset.mem_univ _, hσ1 v₀⟩⟩
  obtain ⟨h1, h2⟩ := ih (s \ O) hlt hs' (fun d v hv => hfree d v (Finset.sdiff_subset hv))
  refine ⟨?_, fun hN => ?_⟩
  · rw [← Finset.card_sdiff_add_card_eq_card hOs, hOc]
    exact dvd_add h1 dvd_rfl
  · rw [← Finset.sum_sdiff hOs, h2 (fun v hv => hN v (Finset.sdiff_subset hv)), zero_add, hO,
      Finset.sum_image (fun d _ e _ h => hinj h)]
    exact hN v₀ hv₀

theorem apply_eq_self_of_pow_prime {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (h2 : ∀ j, 0 < j → j ≤ finrank (ZMod 2) W → ¬ 2 ^ j ≡ 1 [MOD p])
    {f : W ≃ₗ[ZMod 2] W} (hf : f ^ p = 1) (w : W) : f w = w := by
  rcases (Nat.dvd_prime hp.out).mp (orderOf_dvd_of_pow_eq_one hf) with h1 | hpo
  · rw [orderOf_eq_one_iff.mp h1]
    rfl
  have hG : IsPGroup p (Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hpo, pow_one])
  have hmod := hG.card_modEq_card_fixedPoints W
  set K : Submodule (ZMod 2) W := LinearMap.ker ((f : W →ₗ[ZMod 2] W) - LinearMap.id)
  have hfix : ∀ v, v ∈ MulAction.fixedPoints (Subgroup.zpowers f) W ↔ v ∈ K := by
    intro v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]
    constructor
    · intro h
      exact h ⟨f, Subgroup.mem_zpowers f⟩
    · intro h g
      have hs : f ∈ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) v := h
      exact (Subgroup.zpowers_le.mpr hs) g.2
  have hK : Nat.card (MulAction.fixedPoints (Subgroup.zpowers f) W) = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight hfix)
  have hcW := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  have hcK := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [Nat.card_zmod] at hcW hcK
  have hdK : finrank (ZMod 2) K ≤ finrank (ZMod 2) W := Submodule.finrank_le K
  rw [hK, hcK, hcW] at hmod
  have hKt : finrank (ZMod 2) K = finrank (ZMod 2) W := by
    by_contra hne
    set e := finrank (ZMod 2) K
    set d := finrank (ZMod 2) W
    have hlt : e < d := lt_of_le_of_ne hdK hne
    have hcop : Nat.gcd p (2 ^ e) = 1 :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    have h3 : 2 ^ e * 2 ^ (d - e) ≡ 2 ^ e * 1 [MOD p] := by
      rw [← pow_add, Nat.add_sub_cancel' hdK, mul_one]
      exact hmod
    exact h2 (d - e) (by omega) (by omega) (Nat.ModEq.cancel_left_of_coprime hcop h3)
  have hw : w ∈ K := (Submodule.eq_top_of_finrank_eq hKt) ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply] at hw
  exact hw

variable {Λ V : Type*} [Group Λ] [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def SRProp (T : Subgroup Λ) : Prop :=
  ∀ y : Λ, conjSubgroup y T ≠ T → T ⊓ normalizer (conjSubgroup y T : Set Λ) = ⊥

structure ModCfg (ρ : Λ →* (V ≃ₗ[ZMod 2] V)) (T : Subgroup Λ) (a : V) : Prop where
  inj : Function.Injective ρ
  comm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x
  sq : ∀ x ∈ T, x * x = 1
  ne_zero : a ≠ 0
  stab : ∀ u y : Λ, ρ u (ρ y a) = ρ y a ↔ u ∈ normalizer (conjSubgroup y T : Set Λ)
  fix0 : ∀ v : V, (∀ u : Λ, ρ u v = v) → v = 0
  cubic : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ t₃ ∈ T, ∀ v : V,
    ρ t₁ (ρ t₂ (ρ t₃ v - v) - (ρ t₃ v - v)) - (ρ t₂ (ρ t₃ v - v) - (ρ t₃ v - v)) = 0

theorem false_of_orderOf_prime [Finite V] {ρ : Λ →* (V ≃ₗ[ZMod 2] V)}
    (hρ : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h2 : ∀ j, 0 < j → j ≤ finrank (ZMod 2) V → ¬ 2 ^ j ≡ 1 [MOD p]) {c : Λ}
    (hc : orderOf c = p) : False := by
  have hf : ρ c ^ p = 1 := by rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
  have h1 : ρ c = 1 := LinearEquiv.ext fun w => apply_eq_self_of_pow_prime hp2 h2 hf w
  have hc1 : c = 1 := hρ (by rw [h1, map_one])
  rw [hc1, orderOf_one] at hc
  exact (Fact.out : p.Prime).one_lt.ne hc

end CFSG.LargeExtraspecial.S11
