module

public import CFSG.ClassicalInvolution.AschTight.MuZ2Closed

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.SD

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

structure Setup194Three (K : Subgroup G) (z : G) : Prop where
  uniqueInvolutionNormal : UniqueInvolutionNormal K z
  nonabelian : ∃ x y : G, x * y ≠ y * x
  normEq : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G)
  quat : ∀ {R : Subgroup G}, R ∈ RSet (CoreAssembly.conjClass K) → IsQuatSub R
  sylow_eq : ∀ (Q : Sylow 2 K) {S : Subgroup G}, IsPGroup 2 S →
    (Q : Subgroup K).map K.subtype ≤ S → ∀ {g : G},
      conjSubgroup g ((Q : Subgroup K).map K.subtype) ≤ S →
        conjSubgroup g ((Q : Subgroup K).map K.subtype) = (Q : Subgroup K).map K.subtype

namespace Setup194Three

variable {K : Subgroup G} {z : G} (ht : Setup194Three K z)
include ht

theorem le_centralizer : K ≤ Subgroup.centralizer ({z} : Set G) :=
  ht.uniqueInvolutionNormal.2.2.2.1

theorem isUniqueInvolution : IsUniqueInvolution K z := by
  have hU := ht.uniqueInvolutionNormal
  refine ⟨hU.2.1, ?_, ?_, ?_⟩
  · intro h
    have h2 := hU.1
    rw [h, orderOf_one] at h2
    omega
  · rw [← sq, ← hU.1, pow_orderOf_eq_one]
  · intro y hy hy2
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (hU.2.2.1 y hy (orderOf_eq_prime (by rw [sq]; exact hy2) h1))

theorem conjSub_eq_conjSub {a b : G} (h : a * z * a⁻¹ = b * z * b⁻¹) :
    conjSub a K = conjSub b K := by
  have hn : b⁻¹ * a ∈ Subgroup.normalizer (K : Set G) := by
    rw [ht.normEq, Subgroup.mem_centralizer_singleton_iff]
    calc b⁻¹ * a * z = b⁻¹ * (a * z * a⁻¹) * a := by group
      _ = b⁻¹ * (b * z * b⁻¹) * a := by rw [h]
      _ = z * (b⁻¹ * a) := by group
  calc conjSub a K = conjSub b (conjSub (b⁻¹ * a) K) := by rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub b K := by rw [conjSub_eq_of_mem_normalizer hn]

theorem mem_normalizer_of_commute {K₁ : Subgroup G} (hK₁ : K₁ ∈ CoreAssembly.conjClass K)
    {z₁ : G} (hz₁ : IsUniqueInvolution K₁ z₁) {v : G} (hv : v * z₁ = z₁ * v) :
    v ∈ Subgroup.normalizer (K₁ : Set G) := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K K₁ hK₁
  obtain rfl : z₁ = a * z * a⁻¹ := hz₁.eq (ht.isUniqueInvolution.conj a)
  have hconj : conjSub v (conjSub a K) = conjSub a K := by
    rw [← conjSub_mul]
    apply ht.conjSub_eq_conjSub
    calc v * a * z * (v * a)⁻¹ = v * (a * z * a⁻¹) * v⁻¹ := by group
      _ = a * z * a⁻¹ * v * v⁻¹ := by rw [hv]
      _ = a * z * a⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hx : v * x * v⁻¹ ∈ conjSub v (conjSub a K) ↔ x ∈ conjSub a K := by
    rw [mem_conjSub_iff]
    simp [mul_assoc]
  rw [hconj] at hx
  exact hx.symm

theorem exists_ne_comm_of_mem_rSet {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) :
    (∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) ∧ 8 ≤ Nat.card R :=
  ⟨(ht.quat hR).exists_not_commute, (ht.quat hR).eight_le⟩

variable [Finite G]

theorem isUniqueInvolution_of_mem_rSet_of_le {R : Subgroup G}
    (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K) : IsUniqueInvolution R z := by
  have hI := ht.isUniqueInvolution
  have h8 := (ht.exists_ne_comm_of_mem_rSet hR).2
  obtain ⟨k, hk⟩ := (isPGroup_of_mem_rSet hR).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk, pow_zero] at h8
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have huz : (u : G) = z := ht.uniqueInvolutionNormal.2.2.1 _ (hRK u.2) hu'
  exact ⟨huz ▸ u.2, hI.ne_one, hI.sq, fun y hy hy2 => hI.unique y (hRK hy) hy2⟩

end Setup194Three

variable [Finite G] {K : Subgroup G} {z : G}

theorem exists_conj_mem_sylow_ne [IsSimpleGroup G] (ht : Setup194Three K z) (S : Sylow 2 G)
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ g : G, g * z * g⁻¹ ∈ (S : Subgroup G) ∧ g * z * g⁻¹ ≠ z := by
  by_contra hcon
  push Not at hcon
  have hI := ht.isUniqueInvolution
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact hI.sq) hI.ne_one
  have hiso : ∀ g : G, g * z * g⁻¹ * z = z * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hg
    have hu : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hg
    have hu2 : IsPGroup 2 (Subgroup.zpowers (g * z * g⁻¹)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hord]
    obtain ⟨c, hc, hcS⟩ := exists_conj_mem_of_sylow_le S hSz hu hu2
    have h1 := hcon (c * g) (by
      rw [show c * g * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ by group]; exact hcS)
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc g * z * g⁻¹ = c⁻¹ * (c * g * z * (c * g)⁻¹) * c := by group
      _ = c⁻¹ * (z * c) := by rw [h1, mul_assoc]
      _ = z := by rw [← hcz]; group
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G z hI.ne_one hI.sq hiso
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · obtain ⟨x, y, hxy⟩ := ht.nonabelian
    have hzZ : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hN g
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h1]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · rw [hc, Subgroup.mem_bot] at hzZ
      exact hI.ne_one hzZ
    · have := Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top x) y
      exact hxy this.symm
  · rw [htop, Subgroup.card_top] at hNodd
    have h2 : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
    obtain ⟨c, hc⟩ := hNodd
    omega

end CFSG.ClassicalInvolution.Q3.Q3T6.SD
