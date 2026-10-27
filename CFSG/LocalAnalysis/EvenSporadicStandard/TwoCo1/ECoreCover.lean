module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECore
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreClasses

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Sporadic.Co1.Cover CFSG.Monster.Schur CFSG.Monster.GMS CFSG.Blueprint

theorem sq_eq_one_of_isConj_eps
    {C : Type} [Group C] (π : C →* NativeSporadic.Co1) (ζ : C) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers ζ) (hζc : ζ ∈ Subgroup.center C) (hζo : orderOf ζ = 2)
    {c : C} {x : Multiplicative (Fin 11 → ZMod 2)} (h : IsConj (π c) (epsHom x)) :
    c ^ 2 = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  obtain ⟨ĝ, hĝ⟩ := hπ g
  have hmem : π (ĝ * c * ĝ⁻¹) ∈ epsHom.range := by
    rw [map_mul, map_mul, map_inv, hĝ, hg]
    exact ⟨x, rfl⟩
  have h1 := (eps_preimage_comm_and_sq π ζ hπ hker hζc hζo).2 _ hmem
  rw [pow_two]
  calc c * c = ĝ⁻¹ * (ĝ * c * ĝ⁻¹ * (ĝ * c * ĝ⁻¹)) * ĝ := by group
    _ = 1 := by rw [h1]; group

theorem sq_eq_one_of_not_isCo1TwoB
    {C : Type} [Group C] (π : C →* NativeSporadic.Co1) (ζ : C) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers ζ) (hζc : ζ ∈ Subgroup.center C) (hζo : orderOf ζ = 2)
    {c : C} (hc : orderOf (π c) = 2) (hB : ¬ IsCo1TwoB (π c)) : c ^ 2 = 1 := by
  obtain ⟨x, hx⟩ := exists_isConj_eps hc hB
  exact sq_eq_one_of_isConj_eps π ζ hπ hker hζc hζo hx

theorem mem_ker_iff_eq_one_or_eq {C G : Type*} [Group C] [Group G] (π : C →* G) (ζ : C)
    (hker : π.ker = Subgroup.zpowers ζ) (hζo : orderOf ζ = 2) {y : C} :
    y ∈ π.ker ↔ y = 1 ∨ y = ζ := by
  rw [hker, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have h := zpow_mod_orderOf ζ k
    rw [hζo] at h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← h]
      simp [h0]
    · right
      rw [← h]
      simp [h1]
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

theorem not_isCo1TwoB_of_sq_eq_one
    {C : Type} [Group C] [Group.IsPerfect C] (π : C →* NativeSporadic.Co1) (ζ : C)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers ζ)
    (hζc : ζ ∈ Subgroup.center C) (hζo : orderOf ζ = 2) {c : C} (hc : c * c = 1) :
    ¬ IsCo1TwoB (π c) := by
  intro h2B
  obtain ⟨K, hK⟩ := co1DoubleCoverTwoB C π ζ hπ hker hζc hζo ⟨c, hc, h2B⟩
  have h2 : Nat.card π.ker = 2 := by rw [hker, Nat.card_zpowers, hζo]
  have : Finite NativeSporadic.Co1 := CFSG.Sporadic.Co1.Module.finite_co1
  refine false_of_odd_index_complement π h2 (H := ⊤) (D := K)
    (by rw [Subgroup.index_top]; exact odd_one) ?_ ?_
  · rw [eq_bot_iff]
    rintro x ⟨hxK, hxker⟩
    have h1 : π x = 1 := hxker
    have h3 : (⟨x, hxK⟩ : K) = ⟨1, K.one_mem⟩ :=
      hK.1 (show π x = π 1 by rw [h1, map_one])
    exact congrArg Subtype.val h3
  · rw [eq_top_iff]
    intro y _
    obtain ⟨k, hk⟩ := hK.2 (π y)
    have hk' : (k : C)⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : π (k : C) = π y := hk
      rw [this, inv_mul_cancel]
    have e : y = (k : C) * ((k : C)⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem_sup k.2 hk'

theorem isConj_epsA_or_epsC_of_sq_eq_one
    {C : Type} [Group C] [Group.IsPerfect C] (π : C →* NativeSporadic.Co1) (ζ : C)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers ζ)
    (hζc : ζ ∈ Subgroup.center C) (hζo : orderOf ζ = 2) {y : C} (hy : y * y = 1) (h1 : y ≠ 1)
    (hζ : y ≠ ζ) :
    IsConj (π y) (epsMask eMaskA) ∨ IsConj (π y) (epsMask eMaskC) := by
  have hne : π y ≠ 1 := fun h => by
    rcases (mem_ker_iff_eq_one_or_eq π ζ hker hζo).1 h with h | h
    · exact h1 h
    · exact hζ h
  have hord : orderOf (π y) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, hy, map_one]) hne
  exact isConj_epsA_or_epsC hord (not_isCo1TwoB_of_sq_eq_one π ζ hπ hker hζc hζo hy)

end CFSG.EvenSporadicStandard.TwoCo1
