module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bDict

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section A6glue

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


variable [Fact (∀ a b : ↥d.s56V, a * b = b * a)] [Fact (∀ a : ↥d.s56V, a * a = 1)]

theorem node23b_A6 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hinv : d.S56Z0Inv)
    (hcard : Nat.card d.s56V = 2 ^ 10)
    (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    {h₀ : G} (hh₀ : h₀ ∈ Hg d) (hh : star d (h₀ * d.t * h₀⁻¹) = star d (d.t * d.pv 2))
    (hWimg : img d (Wg d z₀) = Ws d)
    (hWnorm : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (hWel : IsElemAbelian 2 (Ws d)) (hWJ : Ws d ≤ img d (Jg d))
    (hcomm : ∀ w ∈ Wg d z₀, ∀ v ∈ d.s56V, w * v * w⁻¹ * v⁻¹ ∈ Zz d z₀)
    [hN : ((Ws d).subgroupOf (img d (Jg d))).Normal]
    (e : ↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃* alternatingGroup (Fin 6))
    (core : A6CoreStmt) : N23bA6 d z₀ := by
  have hc : ∀ a b : ↥d.s56V, a * b = b * a := Fact.out
  have hs : ∀ a : ↥d.s56V, a * a = 1 := Fact.out
  have hcG : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩)
  have hsG : ∀ a ∈ d.s56V, a * a = 1 := fun a ha => congrArg Subtype.val (hs ⟨a, ha⟩)
  have M := mdata_d h49 hd hz hinv hcard hh₀ hh
  haveI hWbN : ((Ws d).subgroupOf (Hs d)).Normal := Wb_normal hWnorm
  have hW2 : ∀ w ∈ (Ws d).subgroupOf (Hs d), w * w = 1 := by
    intro w hw
    have := hWel.2 (w : MulAut ↥d.s56V) (Subgroup.mem_subgroupOf.1 hw)
    exact Subtype.ext (by simpa [pow_two] using this)
  have hWJb := Wb_le_Jb h49 hd hWJ
  obtain ⟨eb⟩ := jb_quot_equiv h49 hd hWJ _ e
  obtain ⟨V₁, V₂, hZ1, hZ2, hsup, hinf, hst1, hst2, hV2, hr1, hr2, hirr1, hirr2, hfa1, hfa2⟩ :=
    A6_branch (hB := map_Zv_eq hZH) M ((Ws d).subgroupOf (Hs d)) hW2 hWJb ⟨eb⟩
      (fun H hA => core _ H hA)
  have hZv := Zv_map h49 hd hz
  refine ⟨jp_quot_equiv hz hWimg _ e, V₁.map d.s56V.subtype, V₂.map d.s56V.subtype, ?_,
    Subgroup.map_subtype_le _, ?_, Subgroup.map_subtype_le _, ?_, ?_, inv_transfer h49 hd hst1,
    inv_transfer h49 hd hst2, ?_, ?_, ?_, irr_transfer h49 hd hz hZ1 hirr1,
    irr_transfer h49 hd hz hZ2 hirr2, ?_, ?_⟩
  · rw [← hZv]; exact Subgroup.map_mono hZ1
  · rw [← hZv]; exact Subgroup.map_mono hZ2
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]
  · rw [← Subgroup.map_inf _ _ _ (Subgroup.subtype_injective _), hinf, hZv]
  · rw [hV2]; exact conj_transfer (t_mem_H h49 hd) V₁
  · have := isElemAbQuot_map d.s56V hcG hsG hZ1 hr1
    rwa [hZv] at this
  · have := isElemAbQuot_map d.s56V hcG hsG hZ2 hr2
    rwa [hZv] at this
  · exact cent_transfer h49 hd hz hcG hZH hWimg hWJ hcomm
      (fun σ hσ hv => Subgroup.mem_subgroupOf.1 (hfa1 σ hσ hv))
  · exact cent_transfer h49 hd hz hcG hZH hWimg hWJ hcomm
      (fun σ hσ hv => Subgroup.mem_subgroupOf.1 (hfa2 σ hσ hv))

end A6glue

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
