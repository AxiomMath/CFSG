module

public import CFSG.GH74.KGroups.TwoA7Cover
public import CFSG.GH74.GLS.IVK.A7.Core

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm2.Recip

section Main

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}

theorem pRank_eq_one (h : IsDoubleCoverA7 π z) : pRank 2 E = 1 := by
  have hbound : ∀ r : ℕ, (∃ A : Subgroup E, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r) →
      r ≤ 1 := by
    rintro r ⟨A, hA, hcard⟩
    have hle : A ≤ Subgroup.zpowers z := by
      intro x hx
      have hx2 : x * x = 1 := by
        rw [← pow_two]
        exact elemPow_eq_one_of_isElementaryAbelian x hx
      rcases h.eq_one_or_eq_z_of_sq_eq_one hx2 with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers z
    have h2 : Nat.card ↥A ≤ 2 := by
      have := Subgroup.card_le_of_le hle
      rwa [Nat.card_zpowers, orderOf_z h] at this
    by_contra hr
    have hr2 : 2 ≤ r := by omega
    have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
    omega
  have hexp : Monoid.exponent ↥(Subgroup.zpowers z) ∣ 2 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    apply Subtype.ext
    show (z ^ k) ^ 2 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have hz2 : z ^ (2 : ℤ) = 1 := by
      rw [zpow_ofNat, pow_two]; exact h.sq_eq_one
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hz2, one_zpow]
  have hmem : (1 : ℕ) ∈ {r : ℕ | ∃ A : Subgroup E, IsElementaryAbelian 2 ↥A ∧
      Nat.card ↥A = 2 ^ r} :=
    ⟨Subgroup.zpowers z, { exponent_dvd_p := hexp },
      by rw [Nat.card_zpowers, orderOf_z h]; norm_num⟩
  show sSup {r : ℕ | ∃ A : Subgroup E, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r} = 1
  exact le_antisymm (csSup_le ⟨1, hmem⟩ (fun r hr => hbound r hr))
    (le_csSup ⟨1, fun r hr => hbound r hr⟩ hmem)

omit [Finite E] in
theorem sign_autPerm_of_not_inner (h : IsDoubleCoverA7 π z) (φ : MulAut E)
    (hout : φ ∉ innOf E) : Perm.sign (h.autPerm φ) = -1 := by
  by_contra hs
  have h1 : Perm.sign (h.autPerm φ) = 1 := by
    rcases Int.units_eq_one_or (Perm.sign (h.autPerm φ)) with h2 | h2
    · exact h2
    · exact absurd h2 hs
  have hmem : h.autPerm φ ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.2 h1
  obtain ⟨q, hq⟩ := h.surjective ⟨_, hmem⟩
  apply hout
  have : MulAut.conj q = φ := by
    apply h.autPerm_injective
    rw [autPerm_conj, hq]
  exact ⟨q, this⟩

omit [Finite E] in
theorem outer_involution_cases (h : IsDoubleCoverA7 π z) (φ : MulAut E) (hφ2 : φ * φ = 1)
    (hout : φ ∉ innOf E) :
    (h.autPerm φ).IsSwap ∨ (h.autPerm φ).cycleType = {2, 2, 2} := by
  have hs := sign_autPerm_of_not_inner h φ hout
  have hσ2 : (h.autPerm φ) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hφ2, map_one]
  have hne : h.autPerm φ ≠ 1 := by
    intro h1
    rw [h1, map_one] at hs
    exact absurd hs (by decide)
  rcases CFSG.GH74.GLS.IVK.A7.involution_cycleType _ hσ2 hne with h1 | h1 | h1
  · exact Or.inl (Equiv.Perm.isSwap_iff_cycleType.2 h1)
  · exfalso
    have := Equiv.Perm.sign_of_cycleType (h.autPerm φ)
    rw [h1, hs] at this
    exact absurd this (by decide)
  · exact Or.inr h1

end Main

end CFSG.GH74.KGroups.TwoA7
