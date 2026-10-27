module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabBasic
public import CFSG.ClassicalInvolution.Asc77.AscMuTabGroup

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8W

section Reps

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem no_three_reps_E4E
    (hmul : ∀ ρ : Rep Ω W, MuTab.muTabElt ρ * MuTab.muTabElt ρ = 1)
    (hiff : ∀ ρ σ : Rep Ω W, (MuTab.muTabElt ρ = MuTab.muTabElt σ ↔ ρ.K = σ.K))
    (hcommiff : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K →
      (MuTab.muTabElt ρ * MuTab.muTabElt σ = MuTab.muTabElt σ * MuTab.muTabElt ρ ↔
        σ.K ∈ omegaNbr Ω ρ.K))
    (hnemul : ∀ ρ₁ ρ₂ ρ₃ : Rep Ω W, ρ₃.K ∈ omegaNbr Ω ρ₁.K → ρ₃.K ∈ omegaNbr Ω ρ₂.K →
      MuTab.muTabElt ρ₃ ≠ MuTab.muTabElt ρ₁ * MuTab.muTabElt ρ₂)
    (hW : W ∈ WSet Ω) (hE : MuIsoE4 Ω W)
    (ρ₁ ρ₂ ρ₃ : Rep Ω W) (h12 : ρ₁.K ≠ ρ₂.K) (h13 : ρ₁.K ≠ ρ₃.K) (h23 : ρ₂.K ≠ ρ₃.K) :
    False := by
  obtain ⟨φ⟩ := hE
  have hcomm : ∀ x y : ↥(muGroup Ω W), x * y = y * x := by
    intro x y
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hsq : ∀ ρ : Rep Ω W, MuTab.muTabElt ρ * MuTab.muTabElt ρ = 1 := hmul
  have hne1 : ∀ ρ : Rep Ω W, MuTab.muTabElt ρ ≠ 1 := fun ρ =>
    muDelta_ne_one hW (MuTab.muTabElt_mem ρ)
  have hdne : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K → MuTab.muTabElt ρ ≠ MuTab.muTabElt σ :=
    fun ρ σ h e => h ((hiff ρ σ).mp e)
  have hnbr : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K → σ.K ∈ omegaNbr Ω ρ.K := fun ρ σ h =>
    (hcommiff ρ σ h).mp (hcomm _ _)
  have h13' := hnbr ρ₁ ρ₃ h13
  have h23' := hnbr ρ₂ ρ₃ h23
  exact MuTab.not_indep3_klein φ (a := MuTab.muTabElt ρ₁) (b := MuTab.muTabElt ρ₂)
    (c := MuTab.muTabElt ρ₃) ⟨hsq ρ₁, hsq ρ₂, hsq ρ₃, hne1 ρ₁, hne1 ρ₂, hne1 ρ₃,
      hcomm _ _, hcomm _ _, hcomm _ _, hdne ρ₁ ρ₂ h12, (hdne ρ₁ ρ₃ h13).symm,
      (hdne ρ₂ ρ₃ h23).symm, hnemul ρ₁ ρ₂ ρ₃ h13' h23'⟩

theorem exists_rep_ne_E4E
    (hiff : ∀ ρ σ : Rep Ω W, (MuTab.muTabElt ρ = MuTab.muTabElt σ ↔ ρ.K = σ.K))
    (hmul : ∀ ρ : Rep Ω W, MuTab.muTabElt ρ * MuTab.muTabElt ρ = 1)
    (hE : MuIsoE4 Ω W) (ρ : Rep Ω W) : ∃ σ : Rep Ω W, σ.K ≠ ρ.K := by
  by_contra hcon
  push Not at hcon
  obtain ⟨φ⟩ := hE
  have h2 : MuTab.muTabElt ρ * MuTab.muTabElt ρ = 1 := hmul ρ
  have hall : ∀ d ∈ muDelta Ω W, d = MuTab.muTabElt ρ := by
    intro d hd
    obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
    rw [hiff, hcon σ]
  have hcl : (Subgroup.closure (muDelta Ω W) : Subgroup ↥(muGroup Ω W)) = ⊤ :=
    closure_muDelta_eq_top Ω W
  have hsub : (Subgroup.closure (muDelta Ω W) : Subgroup ↥(muGroup Ω W)) ≤
      Subgroup.zpowers (MuTab.muTabElt ρ) := by
    rw [Subgroup.closure_le]
    intro d hd
    rw [hall d hd]
    exact Subgroup.mem_zpowers _
  rw [hcl] at hsub
  have hcard : Nat.card (Subgroup.zpowers (MuTab.muTabElt ρ)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2))
  have h4 : Nat.card ↥(muGroup Ω W) = 4 := by
    rw [Nat.card_congr φ.toEquiv]
    simp
  have : Nat.card ↥(muGroup Ω W) ≤ Nat.card (Subgroup.zpowers (MuTab.muTabElt ρ)) := by
    have := Subgroup.card_le_of_le hsub
    simpa using this
  omega

end Reps

end T8W

end CFSG.ClassicalInvolution.Asc77
