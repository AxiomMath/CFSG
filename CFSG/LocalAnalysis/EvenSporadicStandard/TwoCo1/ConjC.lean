module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Assemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ConjCCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreCentralizers

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Blueprint

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem typeC_data
    {C : Type} [Group C] [Finite C] [Group.IsPerfect C] (π : C →* NativeSporadic.Co1) (ζ : C)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers ζ)
    (hζc : ζ ∈ Subgroup.center C) (hζo : orderOf ζ = 2) {y : C}
    (hy : InvType (⊤ : Subgroup C) ζ co0C3 y) :
    IsConj (π y) (epsMask eMaskC) ∧ ∃ c : C, c * y * c⁻¹ = ζ * y := by
  obtain ⟨-, hyo, hyz, -, hycard⟩ := hy
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hyo] at h
    rw [← pow_two]
    exact h
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hyo
    omega
  have htop : centIn (⊤ : Subgroup C) y = Subgroup.centralizer ({y} : Set C) := top_inf_eq _
  have hcard : Nat.card (Subgroup.centralizer ({y} : Set C)) = 389283840 := by
    rw [← htop, hycard]
    rfl
  rcases isConj_epsA_or_epsC_of_sq_eq_one π ζ hπ hker hζc hζo hy2 hy1 hyz with hA | hC
  · exfalso
    have hK : Nat.card (Subgroup.centralizer ({π y} : Set NativeSporadic.Co1)) = 89181388800 :=
      (card_centralizer_eq_of_isConj hA).trans card_centralizer_epsA
    by_cases hf : ∃ c : C, c * y * c⁻¹ = ζ * y
    · obtain ⟨c, hc⟩ := hf
      rw [card_centralizer_eq_of_fused π hπ ζ hker hζc hζo hc, hK] at hcard
      omega
    · have hf' : ∀ c : C, c * y * c⁻¹ ≠ ζ * y := fun c hc => hf ⟨c, hc⟩
      rw [card_centralizer_eq_two_mul_of_not_fused π hπ ζ hker hζc hζo hf', hK] at hcard
      omega
  · refine ⟨hC, ?_⟩
    by_contra hf
    have hf' : ∀ c : C, c * y * c⁻¹ ≠ ζ * y := fun c hc => hf ⟨c, hc⟩
    have hK : Nat.card (Subgroup.centralizer ({π y} : Set NativeSporadic.Co1)) = 389283840 :=
      (card_centralizer_eq_of_isConj hC).trans card_centralizer_epsC
    rw [card_centralizer_eq_two_mul_of_not_fused π hπ ζ hker hζc hζo hf', hK] at hcard
    omega

theorem conj_typeC_of_cover
    {C : Type} [Group C] [Finite C] (π : C →* NativeSporadic.Co1) (ζ : C)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers ζ)
    (hζc : ζ ∈ Subgroup.center C) (hζo : orderOf ζ = 2) (hperf : Group.IsPerfect C) {y y' : C}
    (hy : InvType (⊤ : Subgroup C) ζ co0C3 y) (hy' : InvType (⊤ : Subgroup C) ζ co0C3 y') :
    ∃ h ∈ (⊤ : Subgroup C), h * y' * h⁻¹ = y := by
  have := hperf
  obtain ⟨hcy, c, hc⟩ := typeC_data π ζ hπ hker hζc hζo hy
  obtain ⟨hcy', -⟩ := typeC_data π ζ hπ hker hζc hζo hy'
  obtain ⟨g, hg⟩ := isConj_iff.1 (hcy'.trans hcy.symm)
  obtain ⟨ĝ, hĝ⟩ := hπ g
  have hmem : ĝ * y' * ĝ⁻¹ * y⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hĝ]
    rw [hg, mul_inv_cancel]
  rcases (mem_ker_iff_eq_one_or_eq π ζ hker hζo).1 hmem with h1 | h1
  · exact ⟨ĝ, Subgroup.mem_top _, mul_inv_eq_one.1 h1⟩
  · refine ⟨c⁻¹ * ĝ, Subgroup.mem_top _, ?_⟩
    have h2 : ĝ * y' * ĝ⁻¹ = ζ * y := mul_inv_eq_iff_eq_mul.1 h1
    calc c⁻¹ * ĝ * y' * (c⁻¹ * ĝ)⁻¹ = c⁻¹ * (ĝ * y' * ĝ⁻¹) * c := by group
      _ = c⁻¹ * (ζ * y) * c := by rw [h2]
      _ = c⁻¹ * (c * y * c⁻¹) * c := by rw [hc]
      _ = y := by group

end CFSG.EvenSporadicStandard.TwoCo1
