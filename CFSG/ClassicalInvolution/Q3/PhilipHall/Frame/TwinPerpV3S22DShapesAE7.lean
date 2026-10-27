module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22DShapes
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf61AE7Tail
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

section Shape


theorem shapeNoRootAE7_of_certs : ShapeNoRootAE7 := by
  intro X _ _ Φ hS htrans hI A B x₀ hA hB hxA hxB hnc α hα4 hperm hfixA hfixB hroot
  obtain ⟨I⟩ := hI
  have hn5 : 5 ≤ 7 := by norm_num
  have F := AE5.q8Fam_of_aeIdent_n hn5 hS I
  have hgen := F.gen
  have hψ4 : ∀ y : ↥(pSpan Φ), autOfTop hgen α (autOfTop hgen α (autOfTop hgen α
      (autOfTop hgen α y))) = y := by
    intro y
    apply Subtype.ext
    simp only [autOfTop_coe]
    have := congrArg (fun f : MulAut X => f (y : X)) hα4
    simpa [MulAut.mul_apply] using this
  have hk := AE5.psi_sq_trichotomy7 F I (autOfTop hgen α) (autOfTop_perm hgen α hperm) hψ4
    hA hB.1 hB.2.1.symm hxA hxB (fun y hy => Subtype.ext (hfixA _ hy))
    (fun y hy => Subtype.ext (hfixB _ hy))
  have hcomm : ∀ q : X, (α * α) q = q → x₀ * q = q * x₀ := by
    intro q hq
    have h1 : (α * α) q = x₀ * q * x₀⁻¹ := by
      rw [hroot]
      rfl
    rw [h1] at hq
    calc x₀ * q = (x₀ * q * x₀⁻¹) * x₀ := by group
      _ = q * x₀ := by rw [hq]
  rcases hk with h1 | h1
  · apply hnc
    rw [Subgroup.mem_center_iff]
    intro g
    have hα1 : α * α = 1 := by
      ext a
      exact congrArg Subtype.val (h1 ⟨a, mem_pSpan_of_top hgen _⟩)
    exact (hcomm g (by rw [hα1]; rfl)).symm
  · apply hnc
    rw [Subgroup.mem_center_iff]
    intro g
    set x₀' : ↥(pSpan Φ) := ⟨x₀, le_pSpan hA hxA.mem⟩ with hx₀'
    have hsub : {y : ↥(pSpan Φ) | (autOfTop hgen α * autOfTop hgen α) y = y} ⊆
        {y : ↥(pSpan Φ) | x₀' * y = y * x₀'} := by
      intro y hy
      have hy' : (α * α) (y : X) = (y : X) := congrArg Subtype.val hy
      exact Subtype.ext (hcomm _ hy')
    have hU : ({y : ↥(pSpan Φ) | (autOfTop hgen α * autOfTop hgen α) y = y} ∪
        {y : ↥(pSpan Φ) | x₀' * y = y * x₀'}) =
        ((Subgroup.centralizer ({x₀'} : Set ↥(pSpan Φ)) : Subgroup ↥(pSpan Φ)) : Set ↥(pSpan Φ)) := by
      ext y
      constructor
      · rintro (hy | hy)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hsub hy).symm
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hy.symm
      · intro hy
        exact Or.inr (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
    rw [hU, Subgroup.closure_eq] at h1
    have hmem : (⟨g, mem_pSpan_of_top hgen g⟩ : ↥(pSpan Φ)) ∈ Subgroup.centralizer ({x₀'} : Set ↥(pSpan Φ)) := by
      rw [h1]; exact Subgroup.mem_top _
    have := Subgroup.mem_centralizer_singleton_iff.mp hmem
    exact congrArg Subtype.val this

end Shape

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
