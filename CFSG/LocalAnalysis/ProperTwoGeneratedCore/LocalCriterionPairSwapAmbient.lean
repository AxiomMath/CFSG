module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem isInvolution_coe_iff (K : Subgroup G) (x : K) :
    IsInvolution (x : G) ↔ IsInvolution x := by
  constructor
  · intro hx
    constructor
    · intro h
      exact hx.ne_one (congrArg Subtype.val h)
    · apply Subtype.ext
      exact hx.sq_eq_one
  · intro hx
    constructor
    · intro h
      exact hx.ne_one (Subtype.ext h)
    · exact congrArg Subtype.val hx.sq_eq_one

theorem conjugacyWithin_top_eq_conjugatesOf (z : G) :
    conjugacyWithin (⊤ : Subgroup G) z = conjugatesOf z := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    exact isConj_iff.mpr ⟨(g : G)⁻¹, by simpa only [inv_inv] using hg⟩
  · intro hx
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    exact ⟨⟨g⁻¹, Subgroup.mem_top _⟩, by simpa only [inv_inv] using hg⟩

theorem conjugacyWithin_subgroupOf_image
    (K D : Subgroup G) (hDK : D ≤ K) (z : K) :
    K.subtype '' conjugacyWithin (D.subgroupOf K) z = conjugacyWithin D (z : G) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, ⟨d, hd⟩, rfl⟩
    exact ⟨⟨(d : K), d.property⟩, congrArg (fun k : K => (k : G)) hd⟩
  · rintro x ⟨d, hd⟩
    let dK : K := ⟨d, hDK d.property⟩
    let y : K := dK⁻¹ * z * dK
    refine ⟨y, ⟨⟨dK, d.property⟩, rfl⟩, ?_⟩
    exact hd

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap
