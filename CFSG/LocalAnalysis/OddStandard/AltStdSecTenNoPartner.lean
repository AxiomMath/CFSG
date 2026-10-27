module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSkel
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreath
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSymSym

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput LieOrderFormulasInput)
open CFSG.OddStandard.AltStdSec.SwapPattern

section Main


theorem shapeTwoTenNoSwapPartnerNoCentralStdHS_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hL44 : ShapeTwoTenL44Excl) : ShapeTwoTenNoSwapPartnerNoCentralStdHS := by
  classical
  intro G _ _ L Q z u h d T e hP hC
  have hz2 : z * z = 1 := d.mul_self
  have hτ₀sw : (τ₀ : Perm (Fin 10)).IsSwap := ⟨8, 9, by decide, rfl⟩
  set x₁ : G := (swapIota h d T e τ₀ : G) with hx₁
  have hx₁C : x₁ ∈ centralizer ({z} : Set G) := swapIota_mem_centralizer h d T e τ₀
  have hx₁π : permOf h d e hx₁C = τ₀ := permOf_swapIota h d T e τ₀
  have hx₂C : z * x₁ ∈ centralizer ({z} : Set G) :=
    mul_mem (mem_centralizer_singleton_iff.2 rfl) hx₁C
  have hx₂π : permOf h d e hx₂C = τ₀ := by
    rw [permOf_mul h d e (mem_centralizer_singleton_iff.2 rfl) hx₁C hx₂C, permOf_self, one_mul,
      hx₁π]
  have hz₁ : z ∈ centralizer ({x₁} : Set G) := by
    rw [mem_centralizer_singleton_iff]; exact (mem_centralizer_singleton_iff.1 hx₁C).symm
  have hz₂ : z ∈ centralizer ({z * x₁} : Set G) := by
    rw [mem_centralizer_singleton_iff]; exact (mem_centralizer_singleton_iff.1 hx₂C).symm
  have hfus₁ : ¬ IsConj z (z * x₁) := hP _ hx₂C (by rw [hx₂π]; exact hτ₀sw)
  have hfus₂ : ¬ IsConj z (z * (z * x₁)) := by
    rw [← mul_assoc, hz2, one_mul]
    exact hP _ hx₁C (by rw [hx₁π]; exact hτ₀sw)
  have key : ∀ (x : G) (hxC : x ∈ centralizer ({z} : Set G)), permOf h d e hxC = τ₀ →
      ¬ IsConj z (z * x) → ∀ hzx : z ∈ centralizer ({x} : Set G),
      (∃ K : Subgroup G, CFSG.EvenSporadicStandard.StdHyp G K ∧ IsSporadic (K ⧸ center K) .HS) ∨
        SymOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) 8 := by
    intro x hxC hxπ hfus hzx
    have hsw : (permOf h d e hxC).IsSwap := by rw [hxπ]; exact hτ₀sw
    rcases twoSec_cases_ten hGLS hO h d T e hxC hsw hfus hzx with h1 | h1 | h1 | h1 | h1
    · exact (hC x hxC hsw h1).elim
    · exact (false_of_wreathOutcome_exact h d T e hxC hxπ hP hzx h1).elim
    · exact Or.inr h1
    · exact Or.inl (exists_stdHyp_of_hsOutcome h (orderOf_eq_prime (by
        rw [pow_two]; exact (swap_elt_facts h d T e hxC hsw).1)
        (swap_elt_facts h d T e hxC hsw).2.2) h1)
    · exact (hL44 G L Q z u h d T e x hxC hsw hfus hzx h1).elim
  rcases key x₁ hx₁C hx₁π hfus₁ hz₁ with hHS | hS₁
  · exact hHS
  rcases key (z * x₁) hx₂C hx₂π hfus₂ hz₂ with hHS | hS₂
  · exact hHS
  exfalso
  have hC0 := centData_swapIotaHom h d T e
  have hN0 := noSwapConj_swapIotaHom h d T e hP
  obtain ⟨π₁, hOS₁⟩ := oneSided_of_symOutcome (ι := swapIotaHom h d T e) (x := x₁) rfl hz₁ hS₁
  obtain ⟨ι', hC', h1, h2⟩ := hC0.exists_twist
  have hx₂ι' : z * x₁ = ι' τ₀ := by rw [h2 τ₀ sign_τ₀]; rfl
  obtain ⟨π₂, hOS₂⟩ := oneSided_of_symOutcome (ι := ι') hx₂ι' hz₂ hS₂
  haveI := h.std.simple
  exact false_of_symSym h.std.nonab hC0 hN0 hOS₁ h1 h2 hOS₂

end Main

end CFSG.OddStandard.AltStdSec
