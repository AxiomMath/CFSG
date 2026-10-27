module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLTwoRoots
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLCenter
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLTwoGrp

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Elt

variable {τ : Tag} {K : Type} [Field K] [Finite K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}

theorem excTL_two_comm_elt (hτ : τ ≠ .G2) (hK : Nat.card K = 2) {α β γ : Fin τ.rank → ℤ}
    {h : ℤ} (hα : α ∈ componentRoots χ i) (hβ : β ∈ componentRoots χ i)
    (hγ : γ ∈ componentRoots χ i) (nα : iform α α = 2 * h) (nβ : iform β β = 2 * h)
    (hαβ : iform α β = -h) (hsum : α + β = γ) :
    ⁅excTLElt hα (1 : K), excTLElt hβ (1 : K)⁆ = excTLElt hγ (1 : K) := by
  refine Subtype.ext ?_
  have := excTL_two_comm_pinnedX hτ hK ((isRootComponent_componentRoots i).isRoot α hα)
    ((isRootComponent_componentRoots i).isRoot β hβ) nα nβ hαβ hsum (1 : K) 1
  rw [one_mul] at this
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, excTLElt_coe] using this

theorem excTL_two_commute_elt_pos (hτ : τ ≠ .G2) {α β : Fin τ.rank → ℤ} {h : ℤ}
    (hα : α ∈ componentRoots χ i) (hβ : β ∈ componentRoots χ i) (nα : iform α α = 2 * h)
    (nβ : iform β β = 2 * h) (hab : iform α β = h) (s t : K) :
    Commute (excTLElt hα s) (excTLElt hβ t) :=
  Subtype.ext (excTL_commute_pinnedX_pos hτ ((isRootComponent_componentRoots i).isRoot α hα)
    ((isRootComponent_componentRoots i).isRoot β hβ) nα nβ hab s t).eq

theorem excTL_two_commute_elt_orth (hτ : τ ≠ .G2) (hK : Nat.card K = 2)
    {α β : Fin τ.rank → ℤ} {h : ℤ} (hα : α ∈ componentRoots χ i) (hβ : β ∈ componentRoots χ i)
    (nα : iform α α = 2 * h) (nβ : iform β β = 2 * h) (hab : iform α β = 0) (s t : K) :
    Commute (excTLElt hα s) (excTLElt hβ t) :=
  Subtype.ext (excTL_two_commute_orth hτ hK ((isRootComponent_componentRoots i).isRoot α hα)
    ((isRootComponent_componentRoots i).isRoot β hβ) nα nβ hab s t).eq

theorem excTL_two_false_of_chain (hτ : τ ≠ .G2) (hK : Nat.card K = 2) {F : Type} [Field F]
    (φ : (↥(componentRootSpan K χ i) ⧸ Subgroup.center ↥(componentRootSpan K χ i)) ≃*
      StatedProj (StatedSL 2 F))
    {a₁ a₂ a₃ : Fin τ.rank → ℤ} {h : ℤ} (h1 : a₁ ∈ componentRoots χ i)
    (h2 : a₂ ∈ componentRoots χ i) (h3 : a₃ ∈ componentRoots χ i) (n1 : iform a₁ a₁ = 2 * h)
    (n2 : iform a₂ a₂ = 2 * h) (n3 : iform a₃ a₃ = 2 * h) (p12 : iform a₁ a₂ = -h)
    (p23 : iform a₂ a₃ = -h) (p13 : iform a₁ a₃ = 0) : False := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have r1 := hΨ.isRoot a₁ h1
  have r2 := hΨ.isRoot a₂ h2
  have r3 := hΨ.isRoot a₃ h3
  have hh := excTL_h_cases hτ r1 n1
  have p21 : iform a₂ a₁ = -h := by rw [iform_comm]; exact p12
  have p32 : iform a₃ a₂ = -h := by rw [iform_comm]; exact p23
  have p31 : iform a₃ a₁ = 0 := by rw [iform_comm]; exact p13
  have s12 := (excTL_a2_of_iform hτ r1 r2 n1 n2 p12).1
  have m12 : a₁ + a₂ ∈ componentRoots χ i := hΨ.add_mem _ h1 _ h2 s12
  have s23 := (excTL_a2_of_iform hτ r2 r3 n2 n3 p23).1
  have m23 : a₂ + a₃ ∈ componentRoots χ i := hΨ.add_mem _ h2 _ h3 s23
  have n12 : iform (a₁ + a₂) (a₁ + a₂) = 2 * h := by
    simp only [iform_add_left, iform_add_right, n1, n2, p12, p21]
    omega
  have n23 : iform (a₂ + a₃) (a₂ + a₃) = 2 * h := by
    simp only [iform_add_left, iform_add_right, n2, n3, p23, p32]
    omega
  have q : iform a₁ (a₂ + a₃) = -h := by
    simp only [iform_add_right, p12, p13]
    omega
  have s123 := (excTL_a2_of_iform hτ r1 s23 n1 n23 q).1
  have m123 : a₁ + (a₂ + a₃) ∈ componentRoots χ i := hΨ.add_mem _ h1 _ m23 s123
  have n123 : iform (a₁ + (a₂ + a₃)) (a₁ + (a₂ + a₃)) = 2 * h := by
    simp only [iform_add_left, iform_add_right, n1, n2, n3, p12, p13, p21, p23, p31, p32]
    omega
  have q' : iform (a₁ + a₂) a₃ = -h := by
    simp only [iform_add_left, p13, p23]
    omega
  have hz : excTLElt m123 (1 : K) ∉ Subgroup.center ↥(componentRootSpan K χ i) :=
    excTL_elt_not_central m123 (hΨ.neg_mem _ m123) one_ne_zero
  have e12 := excTL_two_comm_elt hτ hK h1 h2 m12 n1 n2 p12 rfl
  have e23 := excTL_two_comm_elt hτ hK h2 h3 m23 n2 n3 p23 rfl
  refine excTL_false_of_A3 φ (u₁ := excTLElt h1 (1 : K)) (u₂ := excTLElt h2 (1 : K))
    (u₃ := excTLElt h3 (1 : K)) hz ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact excTL_two_commute_elt_pos hτ h1 m123 n1 n123
      (by simp only [iform_add_right, n1, p12, p13]; omega) 1 1
  · exact excTL_two_commute_elt_orth hτ hK h2 m123 n2 n123
      (by simp only [iform_add_right, p21, n2, p23]; omega) 1 1
  · exact excTL_two_commute_elt_pos hτ h3 m123 n3 n123
      (by simp only [iform_add_right, p31, p32, n3]; omega) 1 1
  · rw [e12]
    exact excTL_two_commute_elt_pos hτ m12 m123 n12 n123
      (by simp only [iform_add_left, iform_add_right, n1, n2, p12, p21, p13, p23]; omega) 1 1
  · rw [e23]
    exact excTL_two_commute_elt_pos hτ m23 m123 n23 n123
      (by simp only [iform_add_left, iform_add_right, n2, n3, p21, p31, p23, p32]; omega) 1 1
  · rw [e23]
    exact excTL_two_comm_elt hτ hK h1 m23 m123 n1 n23 q rfl
  · rw [e12]
    exact excTL_two_comm_elt hτ hK m12 h3 m123 n12 n3 q' (add_assoc _ _ _)
  · rw [e23]
    exact excTL_two_commute_elt_pos hτ h3 m23 n3 n23
      (by simp only [iform_add_right, p32, n3]; omega) 1 1

end Elt

end CFSG.HardMathSupport.Dickson.Sec6.I1431
