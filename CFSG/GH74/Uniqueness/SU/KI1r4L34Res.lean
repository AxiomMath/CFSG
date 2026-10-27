module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup
open scoped commutatorElement

theorem l34_oPrimeResidual_normal (p : ℕ) (X : Type*) [Group X] :
    (GLS.oPrimeResidual p X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h : ∀ y : X, y ∈ GLS.oPrimeResidual p X → g * y * g⁻¹ ∈ GLS.oPrimeResidual p X := by
    intro y hy
    unfold GLS.oPrimeResidual at hy ⊢
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk⟩ := hy
      refine Subgroup.subset_closure ⟨k, ?_⟩
      rw [conj_pow, hk]
      group
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  exact h n hn

section Residual

variable {H : Type} [Group H]

theorem normal_sup_zpowers (K : Subgroup H) [K.Normal] (x : H) (hcomm : ∀ h : H, ⁅h, x⁆ ∈ K) :
    (K ⊔ zpowers x).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, hk, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hn
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hxL : x ∈ K ⊔ zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hgx : g * x * g⁻¹ ∈ K ⊔ zpowers x := by
    have : g * x * g⁻¹ = ⁅g, x⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hcomm g)) hxL
  have e : g * (k * x ^ i) * g⁻¹ = (g * k * g⁻¹) * (g * x * g⁻¹) ^ i := by
    rw [conj_zpow]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.Normal.conj_mem inferInstance k hk g))
    (Subgroup.zpow_mem _ hgx i)

theorem smul_sylow_le (T : Sylow 2 H) (L : Subgroup H) [L.Normal] (hTL : (T : Subgroup H) ≤ L)
    (g : H) : ((g • T : Sylow 2 H) : Subgroup H) ≤ L := by
  intro q hq
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
  have hq' : g⁻¹ * q * g ∈ (T : Subgroup H) := by
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hq
  have := Subgroup.Normal.conj_mem inferInstance _ (hTL hq') g
  simpa [mul_assoc] using this

theorem isPGroup_zpowers_of_pow_eq_one (y : H) (k : ℕ) (hy : y ^ (2 ^ k) = 1) :
    IsPGroup 2 (zpowers y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.iff_orderOf.2 fun g => ?_
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  have h1 : (g : H) ^ (2 ^ k) = 1 := by
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have h2 : orderOf g ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  exact ⟨j, hj⟩

variable [Finite H]

theorem two_elt_mem (T : Sylow 2 H) (L : Subgroup H) [L.Normal] (hTL : (T : Subgroup H) ≤ L)
    (y : H) (k : ℕ) (hy : y ^ (2 ^ k) = 1) : y ∈ L := by
  have hp := isPGroup_zpowers_of_pow_eq_one y k hy
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H T Q
  have := smul_sylow_le T L hTL g
  rw [hg] at this
  exact this (hQ (Subgroup.mem_zpowers y))

theorem index_two_of_card (T : Subgroup H) (P : Subgroup H) (hPT : P ≤ T)
    (hidx : Nat.card P * 2 = Nat.card T) : (P.subgroupOf T).index = 2 := by
  have h1 := Subgroup.card_mul_index (P.subgroupOf T)
  have hmap : (P.subgroupOf T).map T.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPT]
  have h3 := Subgroup.card_map_of_injective T.subtype_injective (K := P.subgroupOf T)
  rw [hmap] at h3
  rw [← h3] at h1
  have hpos : 0 < Nat.card P := Nat.card_pos
  have : Nat.card P * (P.subgroupOf T).index = Nat.card P * 2 := by rw [h1, hidx]
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem oPrimeResidual_eq_sup (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hKs : IsSimpleGroup ↥K) (x : H) (hx2 : x * x = 1) (hxK : x ∉ K)
    (hxT : x ∈ (T : Subgroup H)) (hcomm : ∀ h : H, ⁅h, x⁆ ∈ K)
    (hidx : Nat.card ↥((T : Subgroup H) ⊓ K) * 2 = Nat.card (T : Subgroup H))
    (hP : (T : Subgroup H) ⊓ K ≠ ⊥) :
    GLS.oPrimeResidual 2 H = K ⊔ zpowers x := by
  have hLn := normal_sup_zpowers K x hcomm
  have hPT : (T : Subgroup H) ⊓ K ≤ (T : Subgroup H) := inf_le_left
  have hTL : (T : Subgroup H) ≤ K ⊔ zpowers x := by
    intro t ht
    by_cases htK : t ∈ K
    · exact Subgroup.mem_sup_left htK
    · have h2 := index_two_of_card (T : Subgroup H) _ hPT hidx
      have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨x⁻¹, (T : Subgroup H).inv_mem hxT⟩)
        (b := ⟨t, ht⟩)).2 (by
          have ha : (⟨x⁻¹, (T : Subgroup H).inv_mem hxT⟩ : (T : Subgroup H)) ∉
              ((T : Subgroup H) ⊓ K).subgroupOf (T : Subgroup H) := by
            intro h
            exact hxK (by simpa using (Subgroup.mem_inf.1 h).2)
          have hb : (⟨t, ht⟩ : (T : Subgroup H)) ∉
              ((T : Subgroup H) ⊓ K).subgroupOf (T : Subgroup H) := by
            intro h
            exact htK (Subgroup.mem_inf.1 h).2
          exact iff_of_false ha hb)
      have h4 : x⁻¹ * t ∈ K := (Subgroup.mem_inf.1 h3).2
      have : t = x * (x⁻¹ * t) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
        (Subgroup.mem_sup_left h4)
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨k, hy⟩
    exact two_elt_mem T _ hTL y k hy
  · have hOn := l34_oPrimeResidual_normal 2 H
    have hxO : x ∈ GLS.oPrimeResidual 2 H :=
      Subgroup.subset_closure ⟨1, by simpa [pow_two] using hx2⟩
    have hPO : (T : Subgroup H) ⊓ K ≤ GLS.oPrimeResidual 2 H := by
      intro p hp
      have hpT : IsPGroup 2 (T : Subgroup H) := T.isPGroup'
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hpT) ⟨p, hp.1⟩
      refine Subgroup.subset_closure ⟨j, ?_⟩
      have : (⟨p, hp.1⟩ : (T : Subgroup H)) ^ (2 ^ j) = 1 := by
        rw [← hj]
        exact pow_orderOf_eq_one _
      simpa using congrArg Subtype.val this
    have hKO : K ≤ GLS.oPrimeResidual 2 H := by
      have hN : ((GLS.oPrimeResidual 2 H).subgroupOf K).Normal := hOn.subgroupOf K
      rcases hKs.eq_bot_or_eq_top_of_normal ((GLS.oPrimeResidual 2 H).subgroupOf K) with h | h
      · exfalso
        apply hP
        rw [eq_bot_iff]
        intro p hp
        have hpO := hPO hp
        have : (⟨p, hp.2⟩ : K) ∈ (GLS.oPrimeResidual 2 H).subgroupOf K := hpO
        rw [h, Subgroup.mem_bot] at this
        have : p = 1 := congrArg Subtype.val this
        rw [this]
        exact Subgroup.one_mem _
      · intro k hk
        have : (⟨k, hk⟩ : K) ∈ (GLS.oPrimeResidual 2 H).subgroupOf K := by
          rw [h]
          trivial
        exact this
    exact sup_le hKO (Subgroup.zpowers_le.2 hxO)

end Residual

end CFSG.GH74.Uniqueness.SU.K.R4
