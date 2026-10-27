module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RY0B
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem OuterBetaFor.inv {Y : Type*} [Group Y] {β : Y} (h : OuterBetaFor Y β) :
    OuterBetaFor Y β⁻¹ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr, hrβ⟩ := h.fix
    exact ⟨r, hr, by rw [map_inv, hrβ]⟩
  · intro r hr1 hrβ
    refine h.noInv r hr1 ?_
    have := congrArg (fun y => y⁻¹) hrβ
    simpa [map_inv] using this

theorem outerBetaFor_of_class {X : Type*} [Group X] [Finite X] (hB : BetaDataSqBO X) {t β : X}
    (ht2 : orderOf t = 2) (hsq : ∃ g : X, g * g = t)
    (hcard : Nat.card ↥(centralizer ({t} : Set X)) = 1920)
    (hβt : β ∈ centralizer ({t} : Set X)) (hβ3 : orderOf β = 3) : OuterBetaFor X β := by
  obtain ⟨B', β', hB't, -, hβ'B', hβ', hO'⟩ := hB t ht2 hsq
  have hβ'3 : orderOf β' = 3 := hβ'.1
  have hβ't : β' ∈ centralizer ({t} : Set X) := hB't hβ'B'
  obtain ⟨c, hc⟩ := exists_conj_order_three (C := ↥(centralizer ({t} : Set X))) hcard
    (a := ⟨β', hβ't⟩) (b := ⟨β, hβt⟩) (by rw [← Subgroup.orderOf_coe]; exact hβ'3)
    (by rw [← Subgroup.orderOf_coe]; exact hβ3)
  have hO'' : OuterBetaFor X ((c : X) * β' * (c : X)⁻¹) := hO'.conj c
  rcases hc with hc | hc
  · have h1 : (c : X) * β' * (c : X)⁻¹ = β := congrArg Subtype.val hc
    rwa [h1] at hO''
  · have h1 : (c : X) * β' * (c : X)⁻¹ = β⁻¹ := congrArg Subtype.val hc
    rw [h1] at hO''
    simpa using hO''.inv

end CFSG.EvenSporadicStandard.Fin76b
