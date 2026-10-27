module

public import CFSG.ClassicalInvolution.Asc77.AscHypOmegaMain

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

@[expose] def BStarStmt (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K₀ : Subgroup G) (z₀ : G), IsClassicalMember p f K₀ z₀ →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ P ∈ CoreAssembly.conjClass K₀, ∀ Q ∈ CoreAssembly.conjClass K₀, ∀ u r : G,
      IsUniqueInvolution P u → IsUniqueInvolution Q r → ∀ a ∈ P, orderOf a = 4 →
        a * r = r * a → u ∈ Subgroup.normalizer (Q : Set G)

@[expose] def FusionCoreStmt (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → 4 ≤ orderOf v → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) → v ∈ Subgroup.normalizer (K : Set G)

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem four_le_orderOf_of_not_mem {J K : Subgroup G} {t x : G} (hJ : IsUniqueInvolution J t)
    (hxJ : x ∈ J) (hx2 : IsPGroup 2 (Subgroup.zpowers x))
    (htK : t ∈ Subgroup.normalizer (K : Set G)) (hxK : x ∉ Subgroup.normalizer (K : Set G)) :
    4 ≤ orderOf x := by
  obtain ⟨n, hn⟩ := hx2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · exfalso
    apply hxK
    interval_cases n
    · rw [pow_zero, orderOf_eq_one_iff] at hn
      rw [hn]
      exact Subgroup.one_mem _
    · have hsq : x * x = 1 := by rw [← sq, ← hn.trans (pow_one 2), pow_orderOf_eq_one]
      rcases hJ.unique x hxJ hsq with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact htK
  · rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge

theorem exists_pow_not_mem_sq_mem {K : Subgroup G} {x : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hx : x ∉ Subgroup.normalizer (K : Set G)) :
    ∃ n : ℕ, x ^ (2 ^ n) ∉ Subgroup.normalizer (K : Set G) ∧
      (x ^ (2 ^ n)) ^ 2 ∈ Subgroup.normalizer (K : Set G) := by
  classical
  obtain ⟨k, hk⟩ := hx2.exists_card_eq
  rw [Nat.card_zpowers] at hk
  have hex : ∃ m : ℕ, x ^ (2 ^ (m + 1)) ∈ Subgroup.normalizer (K : Set G) :=
    ⟨k, by rw [pow_succ, pow_mul, ← hk, pow_orderOf_eq_one, one_pow]; exact Subgroup.one_mem _⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simpa using hx
    · have := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
      have h1 : Nat.find hex - 1 + 1 = Nat.find hex := Nat.sub_add_cancel hpos
      rwa [h1] at this
  · have := Nat.find_spec hex
    rwa [pow_succ, pow_mul] at this

theorem four_le_orderOf_of_noncentral {J : Subgroup G} {t x : G} (hJ : IsUniqueInvolution J t)
    (hxJ : x ∈ J) (hx2 : IsPGroup 2 (Subgroup.zpowers x))
    (hxc : ¬ ∀ w ∈ J, x * w = w * x) : 4 ≤ orderOf x := by
  obtain ⟨n, hn⟩ := hx2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · exfalso
    apply hxc
    interval_cases n
    · rw [pow_zero, orderOf_eq_one_iff] at hn
      intro w _
      rw [hn, one_mul, mul_one]
    · have hsq : x * x = 1 := by rw [← sq, ← hn.trans (pow_one 2), pow_orderOf_eq_one]
      rcases hJ.unique x hxJ hsq with h | h
      · intro w _
        rw [h, one_mul, mul_one]
      · intro w hw
        rw [h]
        exact hJ.commute_of_mem hw
  · rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge

theorem exists_mem_zpowers_orderOf_four {x : G} (hx2 : IsPGroup 2 (Subgroup.zpowers x))
    (h4 : 4 ≤ orderOf x) : ∃ a ∈ Subgroup.zpowers x, orderOf a = 4 := by
  obtain ⟨n, hn⟩ := hx2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ (n - 2) ∣ orderOf x := by
    rw [hn]
    exact pow_dvd_pow 2 (by omega)
  refine ⟨x ^ (2 ^ (n - 2)), Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _, ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) hdvd, hn]
  have : 2 ^ n = 2 ^ (n - 2) * 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [this, Nat.mul_div_cancel_left _ (by positivity)]

end Helpers

theorem classicalFusionStmt_of_core (hB : BStarStmt p f) (hC : FusionCoreStmt p f) :
    ClassicalFusionStmt p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow _ J hJ t ht hne v hvJ hv2 hvnc hvz
  by_contra hv
  have hUK : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have h4 : 4 ≤ orderOf v := four_le_orderOf_of_noncentral ht hvJ hv2 hvnc
  obtain ⟨a, haz', ha4⟩ := exists_mem_zpowers_orderOf_four hv2 h4
  have haJ : a ∈ J := Subgroup.zpowers_le.mpr hvJ haz'
  have hacomm : a * z = z * a := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp haz'
    exact ((Commute.zpow_left (show Commute v z from hvz) m).eq)
  have hD2 : ∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
      t ∈ Subgroup.normalizer (Q : Set G) := fun Q hQ hQz =>
    hB G K z hz hp2 hq J hJ Q hQ t z ht hQz a haJ ha4 hacomm
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hD2 K hKc hUK
  obtain ⟨n, hn1, hn2⟩ := exists_pow_not_mem_sq_mem hv2 hv
  have hv'J : v ^ (2 ^ n) ∈ J := J.pow_mem hvJ _
  have hv'2 : IsPGroup 2 (Subgroup.zpowers (v ^ (2 ^ n))) :=
    hv2.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers v) _))
  have hv'4 : 4 ≤ orderOf (v ^ (2 ^ n)) := four_le_orderOf_of_not_mem ht hv'J hv'2 htK hn1
  have hv'z : v ^ (2 ^ n) * z = z * v ^ (2 ^ n) :=
    (Commute.pow_left (show Commute v z from hvz) _).eq
  exact hn1 (hC G hnab hp2 hq K z hz hbelow J hJ t ht hne hD2 _ hv'J hv'2 hv'4 hv'z hn2)

end CFSG.ClassicalInvolution.Asc77.AscFusion
