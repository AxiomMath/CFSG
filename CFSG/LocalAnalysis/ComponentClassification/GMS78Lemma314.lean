module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314Trans
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314Perm

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

abbrev deltaGroup (L T : Subgroup G) : Subgroup (Equiv.Perm (gmsDelta L T)) :=
  (deltaPerm L T).range

abbrev deltaN₁ (L T : Subgroup G) : Subgroup (Equiv.Perm (gmsDelta L T)) :=
  ((gmsN₁ L T).subgroupOf (normalizer (gmsV L T : Set G))).map (deltaPerm L T)

abbrev deltaT₀ (L T : Subgroup G) : gmsDelta L T :=
  ⟨T ⊓ centralizer (L : Set G), Sec3.mem_delta_T₀⟩

namespace Sec3

variable {L T : Subgroup G} {q : ℕ}

theorem exists_ne_deltaT₀ (h313 : Lemma313 L T q) (hX : Facts L T q) :
    ∃ Q : gmsDelta L T, Q ≠ deltaT₀ L T := by
  have h1 : 1 < Nat.card (gmsDelta L T) := by rw [h313.card_eq]; have := hX.four_le; omega
  have : Nontrivial (gmsDelta L T) := Finite.one_lt_card_iff_nontrivial.mp h1
  exact exists_ne _

theorem normalizer_T₀_le
    (h : Sec3 G L T) :
    normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  have h1 := AS76b.Lemma36.normalizer_le h.hyp.hyp31 h.isSylowOf_T₀ 1
  rwa [rightConjugate_one, rightConjugate_one] at h1

namespace IsTorus

variable {y : G}

abbrev perm (hy : IsTorus L T y) : Equiv.Perm (gmsDelta L T) :=
  deltaPerm L T ⟨y, hy.mem_normalizer⟩

omit [Finite G] in
theorem perm_mem_deltaN₁ (hy : IsTorus L T y) : hy.perm ∈ deltaN₁ L T :=
  mem_map.mpr ⟨_, mem_subgroupOf.mpr hy.mem_gmsN₁, rfl⟩

omit [Finite G] in
theorem perm_apply_T₀ (hy : IsTorus L T y) : hy.perm (deltaT₀ L T) = deltaT₀ L T :=
  (deltaPerm_apply_eq_iff _ _).mpr (Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun _ ht => (hy.commute ht).symm))

theorem zpow_perm_eq_one (hy : IsTorus L T y) (h313 : Lemma313 L T q) (h : Sec3 G L T)
    {k : ℤ} {Q : gmsDelta L T} (hQT : Q ≠ deltaT₀ L T) (hk : (hy.perm ^ k) Q = Q) :
    hy.perm ^ k = 1 := by
  set NV := normalizer (gmsV L T : Set G)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, y ^ m = y ^ k :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (zpow_mem (mem_zpowers y) k))
  have hyk : (⟨y, hy.mem_normalizer⟩ ^ k : NV) = ⟨y, hy.mem_normalizer⟩ ^ m :=
    Subtype.ext (by rw [coe_zpow, coe_pow, hm])
  have hpk : hy.perm ^ k = deltaPerm L T (⟨y, hy.mem_normalizer⟩ ^ m) := by
    rw [← hyk, map_zpow]
  rw [hpk] at hk ⊢
  have hN := (deltaPerm_apply_eq_iff _ Q).mp hk
  rw [coe_pow] at hN
  have hQT' : (Q : Subgroup G) ≠ T ⊓ centralizer (L : Set G) := fun h1 => hQT (Subtype.ext h1)
  have hA := (hy.aut_pow_eq_one_iff m).mp (hy.aut_pow_eq_one_of_normalizer h313 h Q.2 hQT' hN)
  apply deltaPerm_eq_one_of_commute
  rw [coe_pow]
  refine commute_gmsV (fun a ha => ?_) (fun t ht => Commute.pow_left (hy.commute ht) m)
  calc y ^ m * a = y ^ m * a * (y ^ m)⁻¹ * y ^ m := by group
    _ = a * y ^ m := by rw [hA a ha]

theorem perm_apply_ne (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q)
    (h : Sec3 G L T) {Q : gmsDelta L T} (hQT : Q ≠ deltaT₀ L T) : hy.perm Q ≠ Q := by
  intro h1
  have hN : y ^ 1 ∈ normalizer ((Q : Subgroup G) : Set G) := by
    rw [pow_one]
    exact (deltaPerm_apply_eq_iff _ Q).mp h1
  have hQT' : (Q : Subgroup G) ≠ T ⊓ centralizer (L : Set G) := fun h1 => hQT (Subtype.ext h1)
  have h2 := hy.aut_pow_eq_one_of_normalizer h313 h Q.2 hQT' hN
  rw [pow_one, ← orderOf_eq_one_iff, hy.orderOf_aut hX h] at h2
  have := hX.four_le
  omega

theorem exists_zpow_perm_apply (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q)
    (h : Sec3 G L T) {Q Q' : gmsDelta L T} (hQ : Q ≠ deltaT₀ L T) (hQ' : Q' ≠ deltaT₀ L T) :
    ∃ k : ℤ, (hy.perm ^ k) Q = Q' := by
  obtain ⟨k, hk⟩ := hy.exists_pow_eq h313 hX h Q.2 (fun h1 => hQ (Subtype.ext h1)) Q'.2
    (fun h1 => hQ' (Subtype.ext h1))
  refine ⟨-(k : ℤ), Subtype.ext ?_⟩
  rw [← map_zpow, deltaPerm_apply, coe_zpow, zpow_neg, inv_inv, zpow_natCast]
  exact hk

theorem conj_mem_zpowers
    (hy : IsTorus L T y) (h : Sec3 G L T) {x : Equiv.Perm (gmsDelta L T)}
    (hx : x ∈ deltaGroup L T) (hxT : x (deltaT₀ L T) = deltaT₀ L T) :
    x * hy.perm * x⁻¹ ∈ zpowers hy.perm := by
  obtain ⟨n, rfl⟩ := hx
  have hnT := (deltaPerm_apply_eq_iff n _).mp hxT
  have hnL := h.normalizer_T₀_le hnT
  have h1 := hy.conj (n : G)⁻¹ (mem_inf.mpr ⟨inv_mem hnL, inv_mem n.2⟩)
  rw [inv_inv] at h1
  have hle : zpowers y ≤ normalizer (centralizer (gmsV L T : Set G) : Set G) :=
    (zpowers_le).mpr (mem_normalizer_of_conj_mem
      (fun c hc => conj_mem_centralizer hy.mem_normalizer hc)
      (fun c hc => by simpa using conj_mem_centralizer (inv_mem hy.mem_normalizer) hc))
  obtain ⟨w, hw, c, hc, hwc⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hle h1
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
  have hcN : c ∈ normalizer (gmsV L T : Set G) := Subgroup.centralizer_le_normalizer _ hc
  have hc1 : deltaPerm L T ⟨c, hcN⟩ = 1 :=
    deltaPerm_eq_one_of_commute fun v hv => (mem_centralizer_iff.mp hc v hv).symm
  have heq : n * ⟨y, hy.mem_normalizer⟩ * n⁻¹ = ⟨y, hy.mem_normalizer⟩ ^ j * ⟨c, hcN⟩ :=
    Subtype.ext (by rw [coe_mul, coe_mul, coe_inv, coe_mul, coe_zpow, hwc])
  rw [← map_inv, ← map_mul, ← map_mul, heq, map_mul, hc1, mul_one, map_zpow]
  exact zpow_mem (mem_zpowers _) j

theorem trans_deltaN₁ (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q)
    (h : Sec3 G L T) : ∀ Q₁ Q₂ : gmsDelta L T, ∃ x ∈ deltaN₁ L T, x Q₁ = Q₂ := by
  set T₀' := deltaT₀ L T with hT₀'
  obtain ⟨Q₁, hQ₁⟩ := exists_ne_deltaT₀ h313 hX
  have hQ₁' : (Q₁ : Subgroup G) ≠ T ⊓ centralizer (L : Set G) := fun h1 => hQ₁ (Subtype.ext h1)
  obtain ⟨g, hg, hg1, hg2⟩ := h313.twoTransitive _ mem_delta_T₀ _ Q₁.2 _ Q₁.2 _ mem_delta_T₀
    hQ₁'.symm hQ₁'
  set g' : normalizer (gmsV L T : Set G) := ⟨g, hg⟩
  have hgT₀ : deltaPerm L T g' T₀' = Q₁ := by
    refine Subtype.ext ?_
    rw [deltaPerm_apply]
    change rightConjugate (T ⊓ centralizer (L : Set G)) g⁻¹ = Q₁
    rw [← hg2, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  obtain ⟨z, hz, hzT⟩ : ∃ z ∈ deltaN₁ L T, z T₀' ≠ T₀' := by
    refine ⟨deltaPerm L T (g'⁻¹ * ⟨y, hy.mem_normalizer⟩ * g'), mem_map.mpr ⟨_,
      mem_subgroupOf.mpr ?_, rfl⟩, ?_⟩
    · have := conj_mem_gmsN₁ h313 (inv_mem hg) hy.mem_gmsN₁
      simpa using this
    · rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgT₀]
      intro h1
      apply hy.perm_apply_ne h313 hX h hQ₁
      have h2 := congrArg (deltaPerm L T g') h1
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply,
        hgT₀] at h2
      exact h2
  have hT : ∀ Q : gmsDelta L T, ∃ x ∈ deltaN₁ L T, x T₀' = Q := by
    intro Q
    by_cases hQ : Q = T₀'
    · exact ⟨1, one_mem _, hQ ▸ rfl⟩
    obtain ⟨k, hk⟩ := hy.exists_zpow_perm_apply h313 hX h hzT hQ
    exact ⟨hy.perm ^ k * z, mul_mem (zpow_mem hy.perm_mem_deltaN₁ k) hz, hk⟩
  intro Q₁ Q₂
  obtain ⟨x₁, hx₁, hx₁T⟩ := hT Q₁
  obtain ⟨x₂, hx₂, hx₂T⟩ := hT Q₂
  refine ⟨x₂ * x₁⁻¹, mul_mem hx₂ (inv_mem hx₁), ?_⟩
  rw [Equiv.Perm.mul_apply, ← hx₁T, ← hx₂T]
  congr 1
  exact x₁.symm_apply_apply T₀'

theorem twoTransitive_deltaN₁ (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q)
    (h : Sec3 G L T) : ∀ a b a' b' : gmsDelta L T, a ≠ b → a' ≠ b' →
      ∃ x ∈ deltaN₁ L T, x a = a' ∧ x b = b' :=
  twoTransitive_of (hy.trans_deltaN₁ h313 hX h) hy.perm_mem_deltaN₁ hy.perm_apply_T₀
    fun _ _ hβ hγ => hy.exists_zpow_perm_apply h313 hX h hβ hγ

end IsTorus

end Sec3

end CFSG.ComponentClassification.GMS78
