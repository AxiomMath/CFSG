module

public import CFSG.GH74.GLS.IVK.Prod32.BF
public import CFSG.GH74.GLS.IVK.Prod32.PglQuot
public import CFSG.GH74.GLS.IVK.Prod32.IClasses
public import CFSG.GH74.GLS.IVK.Prod32.LangTransport
public import CFSG.GH74.GLS.IVK.Prod32.CjPart

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem ivk_3_2_abstract_thm (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7) :
    IVK_3_2_abstract := by
  intro H _ _ K₁ K₂ z T a h
  have hCa := Prod3.prod3_Ca h2A7 h
  refine ⟨hCa, fun hP₁ hP₂ => ?_⟩
  obtain ⟨Y, A, r, F, _, _, e₁, e₂, σ, hO⟩ := Prod3.prod3_bf h h2A7 hP₂
  have hPK : Prod3.P T K₁ K₂ ≤ K₁ ⊔ K₂ := inf_le_right
  have hc : ∀ y ∈ Y, ⁅y, a⁆ ∈ K₁ ⊔ K₂ := fun y hy => hPK (hO.Ce.1 y hy a hO.Cd.1)
  have hCgh := Prod3.prod3_Cg_Ch hO.lang hO.three_le hO.card (fun hne => by
    obtain ⟨y, hy, h1, h2, -, h3⟩ := hO.diag hne
    exact ⟨y, hy, h1, h2, h3⟩) hc
  have hCi := Prod3.prod3_Ci h (fun g => (hO.Ce.2 g).2) hCgh.1.1
  have hCc : Prod3.Cc T K₁ K₂ Y r := by
    refine ⟨hO.Y_norm, hO.Y_index, fun hidx => ?_⟩
    have hne : Prod3.P T K₁ K₂ ≠ Y := by
      intro heq
      rw [heq, Subgroup.relIndex_self] at hidx
      omega
    obtain ⟨y, -, h1, h2, h3, hYeq⟩ := hO.diag hne
    have hpgl := Prod3.prod3_Cc_pgl h.setting e₁ e₂ hO.card hO.card hO.Cb.2.1 h1 h2 h3
    have hsup : K₁ ⊔ K₂ ⊔ Y = K₁ ⊔ K₂ ⊔ zpowers y := by
      rw [hYeq, ← sup_assoc, sup_eq_left.mpr hPK]
    rw [hsup]
    exact hpgl
  have hCj := Prod3.prod3_Cj_of_Cb h hP₁ hP₂ hCa.2.1 hCa.2.2.1 hO.Cb
  exact ⟨Y, A, r, hO.Y_le, hO.A_le, hO.prod, hO.inter, hO.Cb, hCc, hO.Cd, hO.Ce, hO.Cf, hCgh.1,
    hCgh.2, hCi, hCj⟩

end CFSG.GH74.GLS.IVK
