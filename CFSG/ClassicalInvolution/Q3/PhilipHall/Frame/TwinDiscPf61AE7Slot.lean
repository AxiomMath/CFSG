module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf58Shapes
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf61AE7Tail

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.AE

section Shape


theorem sqTriShape_ae7 : SqTriShape (shapeAE 7) := by
  intro X _ _ Φ hS htrans hI A B x₀ hA hB hxA hxB α hα4 hperm hfixA hfixB
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
  rcases hk with h1 | h1
  · left
    ext a
    exact congrArg Subtype.val (h1 ⟨a, mem_pSpan_of_top hgen _⟩)
  · right
    right
    have hT : ({q | (α * α) q = q} ∪ {q | x₀ * q = q * x₀} : Set X) =
        (pSpan Φ).subtype '' ({y : ↥(pSpan Φ) | (autOfTop hgen α * autOfTop hgen α) y = y} ∪
          {y : ↥(pSpan Φ) | (⟨x₀, le_pSpan hA hxA.mem⟩ : ↥(pSpan Φ)) * y =
            y * (⟨x₀, le_pSpan hA hxA.mem⟩ : ↥(pSpan Φ))}) := by
      ext q
      constructor
      · rintro (hq | hq)
        · refine ⟨⟨q, mem_pSpan_of_top hgen q⟩, Or.inl (Subtype.ext ?_), rfl⟩
          exact hq
        · refine ⟨⟨q, mem_pSpan_of_top hgen q⟩, Or.inr (Subtype.ext ?_), rfl⟩
          exact hq
      · rintro ⟨y, hy | hy, rfl⟩
        · exact Or.inl (congrArg Subtype.val hy)
        · exact Or.inr (congrArg Subtype.val hy)
    rw [hT, ← MonoidHom.map_closure, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hgen]

end Shape

section Slot


theorem discUZetaTriAt_ae7 {n : ℕ} : DiscUZetaTriAt n (shapeAE 7) :=
  discUZetaTriAt_of_sqTriShape sqTriShape_ae7

end Slot

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
