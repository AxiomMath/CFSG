module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankSmallSources
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.ComponentClassification.GrSLit.HeKN

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

theorem two_le_pRank_of_pair {H : Subgroup X} {y₁ y₂ : X} (h₁ : y₁ ∈ H) (h₂ : y₂ ∈ H)
    (hy₁ : y₁ * y₁ = 1) (hy₂ : y₂ * y₂ = 1) (hy₁1 : y₁ ≠ 1) (hy₂1 : y₂ ≠ 1) (hne : y₁ ≠ y₂)
    (hc : y₁ * y₂ = y₂ * y₁) : 2 ≤ pRank 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ y : X, y * y = 1 → y ≠ 1 → orderOf y = 2 := fun y hyy hy1 =>
    orderOf_eq_prime (by rw [sq]; exact hyy) hy1
  refine UnbalancedGS.RankSmallSources.two_le_pRank_of_commuting (z := ⟨y₁, h₁⟩) (u := ⟨y₂, h₂⟩)
    (by rw [Subgroup.orderOf_mk]; exact hord y₁ hy₁ hy₁1)
    (by rw [Subgroup.orderOf_mk]; exact hord y₂ hy₂ hy₂1) (Subtype.ext hc) fun hmem => ?_
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hk' : y₁ ^ k = y₂ := by simpa using congrArg Subtype.val hk
  rw [← zpow_mod_orderOf, hord y₁ hy₁ hy₁1, Nat.cast_ofNat] at hk'
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at hk'
    exact hy₂1 hk'.symm
  · rw [h, zpow_one] at hk'
    exact hne hk'

theorem eq_one_or_eq_of_pRank_eq_one {C : Subgroup X} (hC : pRank 2 ↥C = 1) {a v : X}
    (ha : a ∈ C) (hv : v ∈ C) (haa : a * a = 1) (hvv : v * v = 1) (ha1 : a ≠ 1)
    (hc : a * v = v * a) : v = 1 ∨ v = a := by
  by_contra h
  push Not at h
  have := two_le_pRank_of_pair ha hv haa hvv ha1 h.1 (Ne.symm h.2) hc
  omega

theorem exists_eq_mul_of_involution {L K U : Subgroup X} {a v : X} (ha2 : orderOf a = 2)
    (haC : a ∈ centralizer (L : Set X)) (hrank : pRank 2 ↥(centralizer (L : Set X)) = 1)
    (hCa : centralizer ({a} : Set X) ≤ normalizer (L : Set X)) (hKL : K ≤ L)
    (hCK : ∀ y ∈ L, (∀ k ∈ K, y * k = k * y) → y ∈ U)
    (hInv : ∀ n ∈ normalizer (L : Set X), n * n ∈ centralizer (L : Set X) →
      n ∉ centralizer (L : Set X) →
      (∃ y ∈ L, orderOf y = 2 ∧ y⁻¹ * n ∈ centralizer (L : Set X)) ∨
        ∀ S : Subgroup X, S ≤ L → S ≤ centralizer ({n} : Set X) → Nat.card S ≤ 15120)
    (hKcard : 15120 < Nat.card K) (hv2 : v * v = 1) (hva : a * v = v * a)
    (hvK : ∀ k ∈ K, v * k = k * v) : ∃ z ∈ U, v = z ∨ v = z * a := by
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; omega
  have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
  have hvN : v ∈ normalizer (L : Set X) := hCa (mem_centralizer_singleton_iff.mpr hva.symm)
  have hvv : v * v ∈ centralizer (L : Set X) := by rw [hv2]; exact one_mem _
  by_cases hvC : v ∈ centralizer (L : Set X)
  · rcases eq_one_or_eq_of_pRank_eq_one hrank haC hvC haa hv2 ha1 hva with h | h
    · exact ⟨1, one_mem _, Or.inl h⟩
    · exact ⟨1, one_mem _, Or.inr (by rw [h, one_mul])⟩
  · rcases hInv v hvN hvv hvC with ⟨y, hyL, hy2, hyc⟩ | hsmall
    · set c := y⁻¹ * v with hc
      have hcC : c ∈ centralizer (L : Set X) := hyc
      have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
      have hyc' : y * c = c * y := mem_centralizer_iff.mp hcC y hyL
      have hvyc : v = y * c := by rw [hc]; group
      have hyK : ∀ k ∈ K, y * k = k * y := by
        intro k hk
        have hkc : k * c = c * k := mem_centralizer_iff.mp hcC k (hKL hk)
        have hy : y = v * c⁻¹ := by rw [hc]; group
        have hkc' : k * c⁻¹ = c⁻¹ * k := by
          have h1 : Commute k c := hkc
          exact h1.inv_right.eq
        calc y * k = v * (c⁻¹ * k) := by rw [hy]; group
          _ = v * (k * c⁻¹) := by rw [hkc']
          _ = (v * k) * c⁻¹ := by group
          _ = (k * v) * c⁻¹ := by rw [hvK k hk]
          _ = k * (v * c⁻¹) := by group
          _ = k * y := by rw [hy]
      have hyU : y ∈ U := hCK y hyL hyK
      have hay : y * a = a * y := mem_centralizer_iff.mp haC y hyL
      have hac : a * c = c * a := by
        have h1 : Commute y a := hay
        have h2 : Commute a v := hva
        have h3 : Commute a y⁻¹ := h1.symm.inv_right
        exact (h3.mul_right h2).eq
      have hcc : c * c = 1 := by
        have h1 : v * v = y * y * (c * c) := by
          calc v * v = y * c * (y * c) := by rw [← hvyc]
            _ = y * (c * y) * c := by group
            _ = y * (y * c) * c := by rw [← hyc']
            _ = y * y * (c * c) := by group
        rw [hyy, one_mul] at h1
        exact h1.symm.trans hv2
      rcases eq_one_or_eq_of_pRank_eq_one hrank haC hcC haa hcc ha1 hac with h | h
      · exact ⟨y, hyU, Or.inl (by rw [hvyc, h, mul_one])⟩
      · exact ⟨y, hyU, Or.inr (by rw [hvyc, h])⟩
    · exfalso
      have := hsmall K hKL fun k hk => mem_centralizer_singleton_iff.mpr (hvK k hk).symm
      omega

omit [Finite X] in
theorem centralizer_le_normalizer {L : Subgroup X} (hstd : IsStandardSubgroup L) {c : X}
    (hc : c ∈ centralizer (L : Set X)) (hc2 : orderOf c = 2) :
    centralizer ({c} : Set X) ≤ normalizer (L : Set X) :=
  fun _ hy => CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute
    (CFSG.IsStandardSubgroup.standardComponentIsStandard hstd) hc hc2
    (mem_centralizer_singleton_iff.1 hy)

end CFSG.ComponentClassification.GrSLit.HeKN
