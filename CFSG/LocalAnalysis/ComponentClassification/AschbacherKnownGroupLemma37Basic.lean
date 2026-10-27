module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace Lemma37

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_iff {H : Subgroup G} {b : G} (hb : b ∈ normalizer (H : Set G))
    (hb2 : b ^ 2 ∈ H) {g : G} : g ∈ H ⊔ zpowers b ↔ g ∈ H ∨ b⁻¹ * g ∈ H := by
  constructor
  · intro hg
    have hle : zpowers b ≤ normalizer (H : Set G) := zpowers_le.2 hb
    have hg' : g ∈ ((H ⊔ zpowers b : Subgroup G) : Set G) := hg
    rw [coe_mul_of_right_le_normalizer_left H (zpowers b) hle] at hg'
    obtain ⟨h, hh, c, hc, rfl⟩ := Set.mem_mul.1 hg'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    have hsq : ∀ j : ℤ, b ^ (2 * j) ∈ H := fun j => by
      rw [zpow_mul]
      exact zpow_mem (by exact_mod_cast hb2) j
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hk, h0, add_zero]
      exact H.mul_mem hh (hsq _)
    · right
      have hbinv : b⁻¹ ∈ normalizer (H : Set G) := inv_mem hb
      have hconj : b⁻¹ * h * b ∈ H := by
        have := (mem_normalizer_iff.1 hbinv h).1 hh
        simpa using this
      have : b⁻¹ * (h * b ^ k) = (b⁻¹ * h * b) * b ^ (2 * (k / 2)) := by
        conv_lhs => rw [hk, h1, zpow_add, zpow_one]
        rw [show b ^ (2 * (k / 2)) * b = b * b ^ (2 * (k / 2)) from
          (Commute.zpow_left (Commute.refl b) _).eq]
        group
      rw [this]
      exact H.mul_mem hconj (hsq _)
  · rintro (h | h)
    · exact mem_sup_left h
    · have : g = b * (b⁻¹ * g) := by group
      rw [this]
      exact mul_mem (mem_sup_right (mem_zpowers b)) (mem_sup_left h)

theorem card_sup_zpowers [Finite G] {H : Subgroup G} {b : G}
    (hb : b ∈ normalizer (H : Set G)) (hb2 : b ^ 2 ∈ H) (hbH : b ∉ H) :
    Nat.card (H ⊔ zpowers b : Subgroup G) = 2 * Nat.card H := by
  set K := H ⊔ zpowers b with hK
  have hHK : H ≤ K := le_sup_left
  have hbK : b ∈ K := mem_sup_right (mem_zpowers b)
  have hidx : (H.subgroupOf K).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨b, hbK⟩, fun g => ?_⟩
    simp only [mem_subgroupOf, Subgroup.coe_mul]
    rcases (mem_sup_zpowers_iff hb hb2).1 g.2 with hg | hg
    · refine Or.inr ⟨hg, fun h => hbH ?_⟩
      have := H.mul_mem (H.inv_mem hg) h
      simpa using this
    · refine Or.inl ⟨?_, fun h => ?_⟩
      · have hconj : b * (b⁻¹ * (g : G)) * b⁻¹ ∈ H :=
          (mem_normalizer_iff.1 hb _).1 hg
        have : (g : G) * b = (b * (b⁻¹ * (g : G)) * b⁻¹) * b ^ 2 := by group
        rw [this]
        exact H.mul_mem hconj hb2
      · apply hbH
        have hbinv : b⁻¹ ∈ H := by
          have := H.mul_mem hg (H.inv_mem h)
          simpa using this
        simpa using H.inv_mem hbinv
  have h1 := Subgroup.card_mul_index (H.subgroupOf K)
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hHK).toEquiv] at h1
  omega

theorem exists_mem_normalizer_sq [Finite G] {P X : Subgroup G} (hP : IsPGroup 2 P)
    (hXP : X ≤ P) (hne : X ≠ P) :
    ∃ u ∈ P, u ∉ X ∧ u ∈ normalizer (X : Set G) ∧ u ^ 2 ∈ X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X' := X.subgroupOf P with hX'
  have hlt : X' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne (le_antisymm hXP fun p hp => ?_)
    have : (⟨p, hp⟩ : P) ∈ X' := h ▸ mem_top _
    exact this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := P) X' hlt
  obtain ⟨g, hgN, hgX⟩ := IsConcreteLE.exists_of_lt hnc
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP g
  have hex : ∃ j : ℕ, g ^ (2 ^ j) ∈ X' := ⟨k, by rw [← hk, pow_orderOf_eq_one]; exact one_mem _⟩
  set j := Nat.find hex with hj
  have hjX : g ^ (2 ^ j) ∈ X' := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    apply hgX
    have := hjX
    rw [h0, pow_zero, pow_one] at this
    exact this
  set u := g ^ (2 ^ (j - 1)) with hu
  have huX : u ∉ X' := Nat.find_min hex (by omega : j - 1 < j)
  have hu2 : u ^ 2 ∈ X' := by
    rw [hu, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0)]
    exact hjX
  have huN : u ∈ normalizer (X' : Set P) := pow_mem hgN _
  refine ⟨u, u.2, huX, ?_, hu2⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhP : h ∈ P := hXP hh
    have := (mem_normalizer_iff.1 huN ⟨h, hhP⟩).1 hh
    exact this
  · intro hh
    have hhP' : (u : G) * h * (u : G)⁻¹ ∈ P := hXP hh
    have hhP : h ∈ P := by
      have : h = (u : G)⁻¹ * ((u : G) * h * (u : G)⁻¹) * u := by group
      rw [this]
      exact P.mul_mem (P.mul_mem (P.inv_mem u.2) hhP') u.2
    exact (mem_normalizer_iff.1 huN ⟨h, hhP⟩).2 hh

theorem eq_of_normalizer_le [Finite G] {P X : Subgroup G} (hP : IsPGroup 2 P) (hXP : X ≤ P)
    (hN : ∀ g ∈ P, g ∈ normalizer (X : Set G) → g ∈ X) : X = P := by
  by_contra hne
  obtain ⟨u, huP, huX, huN, -⟩ := exists_mem_normalizer_sq hP hXP hne
  exact huX (hN u huP huN)

theorem mem_zpowers_sq_eq_one {x w : G} (hx : orderOf x = 4) (hw : w ∈ zpowers x)
    (hw2 : w ^ 2 = 1) : w = 1 ∨ w = x ^ 2 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  have hx4' : x ^ (4 : ℕ) = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx4 : x ^ (4 : ℤ) = 1 := by exact_mod_cast hx4'
  have hred : ∀ j : ℤ, x ^ j = x ^ (j % 4) := fun j => by
    conv_lhs => rw [← Int.mul_ediv_add_emod j 4]
    rw [zpow_add, zpow_mul, hx4, one_zpow, one_mul]
  have h2 : x ^ (k * 2) = 1 := by rw [zpow_mul]; exact_mod_cast hw2
  have hdvd : (4 : ℤ) ∣ k * 2 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h2
    rw [hx] at this
    exact_mod_cast this
  have hk : k % 4 = 0 ∨ k % 4 = 2 := by omega
  rcases hk with h | h
  · left
    rw [hred, h, zpow_zero]
  · right
    rw [hred, h]
    norm_cast

theorem mem_zpowers_sq_ne_one {x w : G} (hx : orderOf x = 4) (hw : w ∈ zpowers x)
    (hw2 : w ^ 2 ≠ 1) : w = x ∨ w = x⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  have hx4' : x ^ (4 : ℕ) = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx4 : x ^ (4 : ℤ) = 1 := by exact_mod_cast hx4'
  have hred : ∀ j : ℤ, x ^ j = x ^ (j % 4) := fun j => by
    conv_lhs => rw [← Int.mul_ediv_add_emod j 4]
    rw [zpow_add, zpow_mul, hx4, one_zpow, one_mul]
  have hk : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hk with h | h | h | h
  · exact absurd (by rw [hred, h, zpow_zero, one_pow]) hw2
  · left
    rw [hred, h, zpow_one]
  · exfalso
    apply hw2
    rw [hred, h, ← zpow_natCast, ← zpow_mul]
    exact hx4
  · right
    rw [hred, h]
    have : x ^ (3 : ℤ) = x ^ (4 : ℤ) * x⁻¹ := by group
    rw [this, hx4, one_mul]

end Lemma37

end CFSG.ComponentClassification.AschbacherKnownGroup
