module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.TranspositionGraph

public section

namespace CFSG.EvenSporadicStandard.YS14

open Subgroup

variable {G : Type*} [Group G]

theorem fourClassesLarge_of_witness {K : Subgroup G} [Finite K] (C Q : Set G)
    (hCsq : ∀ u ∈ C, u * u = 1) (hCK : ∀ x ∈ K, ∀ u ∈ C, x * u * x⁻¹ ∈ C) (hQC : Q ⊆ C)
    (hPK : evenSub Q ≤ K) (hP : evenSub Q ≤ ⁅evenSub Q, evenSub Q⁆) {q₀ : G} (hq₀ : q₀ ∈ Q)
    (hcover : ∀ p ∈ C, p ≠ q₀ → ∃ q ∈ Q, q * q₀ * p ∉ C)
    (hleaf : CFSG.ComponentClassification.M12Cover.FourClassesLarge
      ↥(K ⊓ Subgroup.centralizer ({q₀} : Set G))) :
    CFSG.ComponentClassification.M12Cover.FourClassesLarge ↥K := by
  classical
  refine CFSG.EvenSporadicStandard.HypOne.Fi23.fourClassesLarge_of_perfect_few hPK hP ?_
  intro x hxK hxP hx4 hfew
  by_contra hx2
  have hxK' : x⁻¹ ∈ K := K.inv_mem hxK
  have hq₀C : q₀ ∈ C := hQC hq₀
  have hpC : x⁻¹ * q₀ * x ∈ C := by
    have := hCK x⁻¹ hxK' q₀ hq₀C
    simpa using this
  have hcomm : ∀ q ∈ Q, x⁻¹ * (q * q₀) * x = q * q₀ := by
    intro q hq
    have h := hxP (q * q₀) (mul_mem_evenSub hq hq₀)
    calc x⁻¹ * (q * q₀) * x = x⁻¹ * ((q * q₀) * x) := by group
      _ = x⁻¹ * (x * (q * q₀)) := by rw [h]
      _ = q * q₀ := by group
  have hconj : ∀ q ∈ Q, x⁻¹ * q * x = q * q₀ * (x⁻¹ * q₀ * x) := by
    intro q hq
    have h1 := hcomm q hq
    have h2 : q₀ * q₀ = 1 := hCsq q₀ hq₀C
    calc x⁻¹ * q * x = (x⁻¹ * (q * q₀) * x) * (x⁻¹ * q₀ * x) := by
          calc x⁻¹ * q * x = x⁻¹ * (q * (q₀ * q₀)) * x := by rw [h2, mul_one]
            _ = (x⁻¹ * (q * q₀) * x) * (x⁻¹ * q₀ * x) := by group
      _ = q * q₀ * (x⁻¹ * q₀ * x) := by rw [h1]
  have hpq : x⁻¹ * q₀ * x = q₀ := by
    by_contra hne
    obtain ⟨q, hq, hnot⟩ := hcover _ hpC hne
    apply hnot
    have := hCK x⁻¹ hxK' q (hQC hq)
    rw [show x⁻¹ * q * x⁻¹⁻¹ = x⁻¹ * q * x by simp, hconj q hq] at this
    exact this
  have hxC : x ∈ Subgroup.centralizer ({q₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * q₀ = x * (x⁻¹ * q₀ * x) := by rw [hpq]
      _ = q₀ * x := by group
  have hxL : x ∈ K ⊓ Subgroup.centralizer ({q₀} : Set G) := ⟨hxK, hxC⟩
  have hx4' : (⟨x, hxL⟩ : ↥(K ⊓ Subgroup.centralizer ({q₀} : Set G))) ^ 4 = 1 :=
    Subtype.ext (by simpa using hx4)
  have hx2' : (⟨x, hxL⟩ : ↥(K ⊓ Subgroup.centralizer ({q₀} : Set G))) ^ 2 ≠ 1 := fun h =>
    hx2 (by simpa using congrArg Subtype.val h)
  have h5 := hleaf ⟨x, hxL⟩ hx4' hx2'
  apply hfew
  let ι : ↥(K ⊓ Subgroup.centralizer ({q₀} : Set G)) →* ↥K :=
    Subgroup.inclusion inf_le_left
  refine h5.trans (Nat.card_le_card_of_injective
    (fun y => (⟨ι y, ι.map_isConj y.2⟩ : {y : ↥K // IsConj (⟨x, hxK⟩ : ↥K) y})) ?_)
  intro y z h
  have h1 : ι y.1 = ι z.1 := congrArg Subtype.val h
  exact Subtype.ext (Subgroup.inclusion_injective _ h1)

end CFSG.EvenSporadicStandard.YS14
