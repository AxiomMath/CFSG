module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KstAsm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N
open CFSG.LocalAnalysis.EvenBN.Tits.N.P4

theorem kstruct {Γ : Type*} [Group Γ] [Finite Γ] {U K : Subgroup Γ} {x v t : Γ}
    (hF : IsF20 U x v) (htt : t * t = 1) (htnU : t ∉ U)
    (htU : ∀ u ∈ U, t * u = u * t) (htx : t * x = x * t) (htv : t * v = v * t)
    (hCK : zpowers t ⊔ IsF20.Pgrp U x v ≤ K)
    (hKN : K ≤ normalizer ((U ⊔ zpowers t : Subgroup Γ) : Set Γ))
    (hCt : ∀ k ∈ K, k * t = t * k → k ∈ zpowers t ⊔ IsF20.Pgrp U x v)
    (hΔ : ∀ k ∈ K, ∃ u ∈ U, k * t * k⁻¹ = t * u)
    (hne : ∃ u ∈ U, ∀ k ∈ K, k * t * k⁻¹ ≠ t * u)
    (h7 : ∃ u ∈ U, u ≠ 1 ∧ ∃ k ∈ K, k * t * k⁻¹ = t * u) :
    (∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) ∧
    (∀ E : Subgroup Γ, E ≤ K → IsElemAbelian 2 E →
      Nat.card E ≤ 32 ∧ (Nat.card E = 32 → E = U ⊔ zpowers t)) ∧
    (∀ y ∈ K, y * y = 1 → y ∉ U ⊔ zpowers t →
      Nat.card ↥⁅U, zpowers y⁆ = 4 ∧ Nat.card ↥(U ⊓ centralizer ({y} : Set Γ)) = 4) ∧
    (∀ B : Subgroup Γ, B ≤ K → IsElemAbelian 2 B →
      4 ≤ (B ⊓ (U ⊔ zpowers t)).relIndex B →
      ∃ y ∈ B, y ∉ U ⊔ zpowers t ∧
        ∃ k ∈ K, (k * y * k⁻¹) * x * (k * y * k⁻¹)⁻¹ = x⁻¹) ∧
    (∀ N : Subgroup (MulAut ↥U), N ≤ imgIn U K →
      (∀ h ∈ imgIn U K, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → actFun U x ∈ N → Even (Nat.card N)) ∧
    (∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 → ∃ k ∈ K, k * a * k⁻¹ = b) := by
  have h : Kst.KSetup U K x v t :=
    ⟨hF, htt, htnU, htU, htx, htv, hCK, hKN, hCt, hΔ, hne, h7⟩
  exact ⟨h.part1, h.part2, h.part3, h.part4, h.part5, h.part6⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
