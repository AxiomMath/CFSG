module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5TypesB

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_commute {X X' : Subgroup G}
    (hcomm : ∀ a ∈ X, ∀ b ∈ X', a * b = b * a) : X' ≤ normalizer (X : Set G) := fun b hb =>
  mem_normalizer_iff.mpr fun a => ⟨fun ha => by
    rw [show b * a * b⁻¹ = a by rw [← hcomm a ha b hb, mul_inv_cancel_right]]
    exact ha, fun ha => by
    have h2 := hcomm _ ha b hb
    have h3 : a = b * a * b⁻¹ := by
      calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
        _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [mul_assoc, h2]
        _ = b * a * b⁻¹ := by group
    rw [h3]
    exact ha⟩

omit [Finite G] in
theorem exists_mul_of_mem_sup_commute {X X' : Subgroup G}
    (hcomm : ∀ a ∈ X, ∀ b ∈ X', a * b = b * a) {y : G} (hy : y ∈ X ⊔ X') :
    ∃ q₁ ∈ X, ∃ q₂ ∈ X', y = q₁ * q₂ := by
  have h1 : y ∈ ((X : Set G) * (X' : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left X X' (le_normalizer_of_commute hcomm)]
    exact hy
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := h1
  exact ⟨q₁, hq₁, q₂, hq₂, rfl⟩

omit [Finite G] in
theorem eq_of_mul_eq_mul_of_disjoint {X X' : Subgroup G} (hbot : X ⊓ X' = ⊥)
    {q₁ r₁ q₂ r₂ : G} (hq₁ : q₁ ∈ X) (hr₁ : r₁ ∈ X) (hq₂ : q₂ ∈ X') (hr₂ : r₂ ∈ X')
    (h : q₁ * q₂ = r₁ * r₂) : q₁ = r₁ ∧ q₂ = r₂ := by
  have h1 : r₁⁻¹ * q₁ = r₂ * q₂⁻¹ := by
    calc r₁⁻¹ * q₁ = r₁⁻¹ * (q₁ * q₂) * q₂⁻¹ := by group
      _ = r₁⁻¹ * (r₁ * r₂) * q₂⁻¹ := by rw [h]
      _ = r₂ * q₂⁻¹ := by group
  have h2 : r₁⁻¹ * q₁ ∈ X ⊓ X' :=
    mem_inf.mpr ⟨mul_mem (inv_mem hr₁) hq₁, by rw [h1]; exact mul_mem hr₂ (inv_mem hq₂)⟩
  rw [hbot, mem_bot] at h2
  have h3 : q₁ = r₁ := by
    calc q₁ = r₁ * (r₁⁻¹ * q₁) := by group
      _ = r₁ := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

theorem eq_one_or_eq_of_mem_center_eight {X : Subgroup G} (hX8 : Nat.card X = 8)
    (hna : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) {x : G} (hxX : x ∈ X) (hx1 : x ≠ 1)
    (hxZ : ∀ d ∈ X, d * x = x * d) {c : G} (hcX : c ∈ X) (hcZ : ∀ d ∈ X, d * c = c * d) :
    c = 1 ∨ c = x := by
  by_contra hne
  push Not at hne
  obtain ⟨hc1, hcx⟩ := hne
  obtain ⟨a, haX, b, hbX, hab⟩ := hna
  have hxC : (⟨x, hxX⟩ : X) ∈ center X :=
    mem_center_iff.mpr fun d => Subtype.ext (hxZ d d.2)
  have hcC : (⟨c, hcX⟩ : X) ∈ center X :=
    mem_center_iff.mpr fun d => Subtype.ext (hcZ d d.2)
  have h3 := three_le_card_of_ne hxC hcC (fun h1 => hx1 (congrArg Subtype.val h1))
    (fun h1 => hc1 (congrArg Subtype.val h1)) (fun h1 => hcx (congrArg Subtype.val h1).symm)
  have hdvd : Nat.card (center X) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hX8]
    exact card_subgroup_dvd_card _
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcomm : ∀ p q : X, p * q = q * p := by
    interval_cases m
    · rw [pow_zero] at hm'
      omega
    · rw [pow_one] at hm'
      omega
    · have h1 := card_eq_card_quotient_mul_card_subgroup (center X)
      rw [hX8, hm'] at h1
      have h2 : Nat.card (X ⧸ center X) = 2 := by omega
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsCyclic (X ⧸ center X) := isCyclic_of_prime_card h2
      exact (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (center X)) (by rw [QuotientGroup.ker_mk'])).is_comm.comm
    · have h1 : center X = ⊤ := eq_top_of_card_eq _ (by rw [hm', hX8]; norm_num)
      intro p q
      exact mem_center_iff.mp (h1 ▸ mem_top q) p
  exact hab (congrArg Subtype.val (hcomm ⟨a, haX⟩ ⟨b, hbX⟩))

theorem card_inf_centralizer_le_four {X : Subgroup G} (hX8 : Nat.card X = 8) {c : G}
    (hnc : ∃ d ∈ X, d * c ≠ c * d) : Nat.card ↥(X ⊓ centralizer ({c} : Set G)) ≤ 4 := by
  have hlt : X ⊓ centralizer ({c} : Set G) < X := by
    refine lt_of_le_of_ne inf_le_left fun h1 => ?_
    obtain ⟨d, hdX, hdc⟩ := hnc
    have h2 : d ∈ X ⊓ centralizer ({c} : Set G) := by rw [h1]; exact hdX
    exact hdc (mem_centralizer_singleton_iff.mp (mem_inf.mp h2).2)
  have hdvd := card_dvd_of_le hlt.le
  have hne := card_lt_of_lt hlt
  rw [hX8] at hdvd hne
  obtain ⟨k, hk⟩ := hdvd
  rcases k with _ | _ | k
  · omega
  · omega
  · have h1 : Nat.card ↥(X ⊓ centralizer ({c} : Set G)) * 2 ≤
        Nat.card ↥(X ⊓ centralizer ({c} : Set G)) * (k + 1 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem mem_four_of_commute_noncentral {X : Subgroup G} (hX8 : Nat.card X = 8) {x a q : G}
    (hxX : x ∈ X) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxZ : ∀ d ∈ X, d * x = x * d)
    (haX : a ∈ X) (ha2 : a * a = 1) (hnc : ∃ d ∈ X, d * a ≠ a * d) (hqX : q ∈ X)
    (hqa : q * a = a * q) : q = a * x ∨ q = a ∨ q = x ∨ q = 1 := by
  have ha1 : a ≠ 1 := fun h1 => by
    obtain ⟨d, -, hd⟩ := hnc
    rw [h1, mul_one, one_mul] at hd
    exact hd rfl
  have hax : a ≠ x := fun h1 => by
    obtain ⟨d, hd, hd'⟩ := hnc
    rw [h1] at hd'
    exact hd' (hxZ d hd)
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions a x ha2 hx2 (hxZ a haX) with hV
  have hVmem : ∀ e, e ∈ V ↔ e = a * x ∨ e = a ∨ e = x ∨ e = 1 := fun e => by
    change e ∈ ({a * x, a, x, 1} : Set G) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hV4 : Nat.card V = 4 := (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    a x ha2 hx2 ha1 hx1 hax (hxZ a haX)).card_four
  have hVle : V ≤ X ⊓ centralizer ({a} : Set G) := by
    intro e he
    rcases (hVmem e).mp he with rfl | rfl | rfl | rfl
    · refine mem_inf.mpr ⟨mul_mem haX hxX, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [mul_assoc, ← hxZ a haX]
    · exact mem_inf.mpr ⟨haX, mem_centralizer_singleton_iff.mpr rfl⟩
    · exact mem_inf.mpr ⟨hxX, mem_centralizer_singleton_iff.mpr (hxZ a haX).symm⟩
    · exact one_mem _
  have heq : V = X ⊓ centralizer ({a} : Set G) :=
    eq_of_le_of_card_ge hVle (by rw [hV4]; exact card_inf_centralizer_le_four hX8 hnc)
  have hq : q ∈ V := by
    rw [heq]
    exact mem_inf.mpr ⟨hqX, mem_centralizer_singleton_iff.mpr hqa⟩
  exact (hVmem q).mp hq

end CFSG.ComponentClassification.Foote5
