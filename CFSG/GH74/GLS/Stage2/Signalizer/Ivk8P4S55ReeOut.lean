module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55ReeDesc
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2TM
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2NT
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.SmallReeWard

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.LiteratureLocal.SmallRee CFSG.RankThree
  CFSG.SignalizerFunctorTheorem.CatalogBridge CFSG.ComponentClassification.OuterAutomorphisms

section Pure

variable {a : ℕ} {K : Type} [Field K]

theorem entrywise_smallReeTorusElt (σ : K ≃+* K) (s : Kˣ) :
    Units.map (entrywiseHom (τ := Tag.G2) σ.toRingHom) (smallReeTorusElt a K s) =
      smallReeTorusElt a K (Units.map σ.toRingHom.toMonoidHom s) := by
  rw [smallReeTorusElt, smallReeTorusElt, map_mul, entrywise_torusElt, entrywise_torusElt, map_pow]

end Pure


section Torus

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
  (hK : Nat.card K = 3 ^ (2 * a + 1))

include hK in
theorem reeGammaFieldAut_hIn (σ : K ≃+* K) (s : Kˣ) :
    ReeTag.G2.reeGammaFieldAut K a σ (hIn hK s) = hIn hK (Units.map σ.toRingHom.toMonoidHom s) :=
  Subtype.ext (entrywise_smallReeTorusElt σ s)

noncomputable def hHom : Kˣ →* ReeTag.G2.reeGamma K a where
  toFun := hIn hK
  map_one' := Subtype.ext (smallReeTorusElt_one)
  map_mul' s s' := Subtype.ext (smallReeTorusElt_mul s s')

end Torus

section Native

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem outerFalse_ree_native (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    OuterFalse 3 (ReeTag.G2.reeGamma K a) := by
  intro α hαinn hα3 _ hHH
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, σ, hασ⟩ := smallReeOuterIsField a ha K hK α
  obtain ⟨-, -, -, ⟨R, χ, -, hsec, -⟩, -⟩ := small_Ree_outer_three_kernel_field_complement a ha K hK
  have hfaith : ∀ τ : K ≃+* K, ReeTag.G2.reeGammaFieldAut K a τ ∈
      (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range →
        τ = 1 := by
    rintro τ ⟨y, hy⟩
    have h1 : (QuotientGroup.mk (ReeTag.G2.reeGammaFieldAut K a τ) :
        Outer (ReeTag.G2.reeGamma K a)) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact ⟨y, hy⟩
    have h2 := hsec τ
    rw [h1, map_one] at h2
    exact h2.symm
  have hpowα : (MulAut.conj g * ReeTag.G2.reeGammaFieldAut K a σ) ^ 3 = 1 := by
    rw [← hασ]
    exact hα3
  have hσ3 : σ ^ 3 = 1 := by
    apply hfaith
    have h1 := hpowα
    rw [conj_mul_pow] at h1
    have h2 : ReeTag.G2.reeGammaFieldAut K a σ ^ 3 =
        (MulAut.conj ((List.range 3).map fun i =>
          ((ReeTag.G2.reeGammaFieldAut K a σ) ^ i) g).prod)⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine ⟨(((List.range 3).map fun i =>
      ((ReeTag.G2.reeGammaFieldAut K a σ) ^ i) g).prod)⁻¹, ?_⟩
    rw [map_inv, ← h2]
    exact (map_pow (ReeTag.G2.reeGammaFieldAutHom K a) σ 3).symm
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hαinn
    refine ⟨g, ?_⟩
    rw [hασ]
    have : ReeTag.G2.reeGammaFieldAut K a (1 : K ≃+* K) = 1 :=
      map_one (ReeTag.G2.reeGammaFieldAutHom K a)
    rw [this, mul_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨δ, hδ⟩ := ree_coset_descent_of_field ha hK Nat.prime_three (by norm_num) σ hσord g hpowα
  obtain ⟨σ₁, hσ₁, hσ₁ord, hσ₁top, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_three (by omega) hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₁, hσ₁top⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hpf : 3 ∣ 2 * a + 1 := by
    rw [← hσord, ← hcardAut]
    exact orderOf_dvd_natCard σ
  obtain ⟨d, hd⟩ := hpf
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hd
      omega
    · exact h
  have hσ₁pow : ∀ (n : ℕ) (c : K), (σ₁ ^ n) c = c ^ (3 ^ n) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, hσ₁, ih, ← pow_mul, ← pow_succ']
  obtain ⟨k, hk⟩ : ∃ k : ℕ, σ₁ ^ k = σ := by
    have h : σ ∈ Subgroup.zpowers σ₁ := hσ₁top ▸ Subgroup.mem_top σ
    rwa [← mem_powers_iff_mem_zpowers] at h
  set τ₀ := σ₁ ^ d with hτ₀def
  have hτ₀ord : orderOf τ₀ = 3 := by
    rw [hτ₀def, orderOf_pow' _ (by omega), hσ₁ord, hd, Nat.gcd_mul_left_left]
    exact Nat.mul_div_cancel 3 hd1
  have hzz : Subgroup.zpowers τ₀ = Subgroup.zpowers σ :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hτ₀ord, hσord])
  obtain ⟨j, hj⟩ : ∃ j : ℕ, σ ^ j = τ₀ := by
    have h : τ₀ ∈ Subgroup.zpowers σ := hzz ▸ Subgroup.mem_zpowers τ₀
    rwa [← mem_powers_iff_mem_zpowers] at h
  have hq0odd : Odd (3 ^ d) := (by decide : Odd 3).pow
  have hq03 : 3 ≤ 3 ^ d := Nat.le_self_pow (by omega) 3
  obtain ⟨r, hr, hr2, hr3, hrdvd, hrnd⟩ := exists_prime_dvd_pow_sub_one_not_dvd Nat.prime_three
    (by norm_num) (dvd_pow_self 3 (by omega)) hq03 hq0odd
  have hunits : Nat.card Kˣ = (3 ^ d) ^ 3 - 1 := by
    rw [Nat.card_units, hK, hd, ← pow_mul, mul_comm]
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' r (hunits ▸ hrdvd)
  have hot : orderOf (hHom hK s) = r := by
    rw [orderOf_injective (hHom hK) (hIn_injective hK) s]
    exact hs
  have hft : ReeTag.G2.reeGammaFieldAut K a σ (hHom hK s) = (hHom hK s) ^ (3 ^ k) := by
    change ReeTag.G2.reeGammaFieldAut K a σ (hIn hK s) = (hHom hK s) ^ (3 ^ k)
    rw [reeGammaFieldAut_hIn hK, ← map_pow]
    change hIn hK _ = hIn hK _
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    show σ (s : K) = (s : K) ^ 3 ^ k
    rw [← hk, hσ₁pow]
  have hne : ReeTag.G2.reeGammaFieldAut K a σ (hHom hK s) ≠ hHom hK s := by
    intro h
    change ReeTag.G2.reeGammaFieldAut K a σ (hIn hK s) = hIn hK s at h
    rw [reeGammaFieldAut_hIn hK] at h
    have h1 : Units.map σ.toRingHom.toMonoidHom s = s := hIn_injective hK h
    have h2 : (σ ^ j) (s : K) = s := by
      have h3 : ∀ n : ℕ, (σ ^ n) (s : K) = s := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, RingAut.mul_apply]
          have : σ (s : K) = s := congrArg Units.val h1
          rw [this, ih]
      exact h3 j
    rw [hj, hτ₀def, hσ₁pow] at h2
    have h4 : (s : Kˣ) ^ (3 ^ d - 1) = 1 := by
      apply Units.ext
      have h5 : (s : K) ^ (3 ^ d) = s := h2
      have hs0 : (s : K) ≠ 0 := s.ne_zero
      have : (s : K) ^ (3 ^ d - 1) * s = 1 * s := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
        exact h5
      simpa using mul_right_cancel₀ hs0 this
    exact hrnd (hs ▸ orderOf_dvd_of_pow_eq_one h4)
  have hα' : α = δ⁻¹ * ReeTag.G2.reeGammaFieldAut K a σ * δ⁻¹⁻¹ := by
    have h1 : δ * α * δ⁻¹ = ReeTag.G2.reeGammaFieldAut K a σ := by rw [hασ]; exact hδ
    rw [← h1]
    group
  exact false_of_torus_moved_pow hα' hr hr2 hr3 hot hft hne hHH

end Native

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
