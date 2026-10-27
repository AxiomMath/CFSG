module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1

@[expose] def B_thm1_FmemberF : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2 G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      ∀ T : Subgroup G, Setup1D x K T → ∀ f : G, IsFMember x K T f → P34.InducesFAutL2A7 f K

theorem thm1_fusion_of
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hL1 : B_thm1_P31_comp) (hL3 : B_thm1_FmemberF) : B_thm1_fusion := by
  intro G _ _ hG hV x y K T f h𝒰 hT hfm z hz hz2 hzc u hu hu2
  have hshape := C3.Layer1.Thm1.kBar_model_of_U2 hG h102 hL34 h𝒰
  obtain ⟨hKN, -⟩ := hL1 G hG hV x y K h𝒰 hshape
  have hKC : K ≤ centralizer ({x} : Set G) := h𝒰.1.1.2.1
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.1 (hKC hk)).symm
  have hQ2 := C3.Layer1.Thm1.card_le_two_of_noV2 hV h𝒰
  obtain ⟨hcen, hAut⟩ := C3.Layer1.Thm1.kBar_autData h2hb hV h𝒰 hshape
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    C3.Layer1.Thm1.exists_E₁ hT.sylowT (by rw [h𝒰.2.2.1.2, hG.pRank_eq_four])
  have hfind := hL3 G hG hV x y K h𝒰 hshape hKN T hT f hfm
  obtain ⟨hfN, hF⟩ := hfind
  have hfinn : ∀ hfC : f ∈ centralizer ({x} : Set G),
      Back.actHom hKN ⟨f, hfC⟩ ∉ IVK.innAut (kBar K) := fun hfC =>
    C3.Layer1.Thm1.not_mem_innAut_of_isFAutL2A7 hF
  exact C3.Layer1.Thm1.transport_fusion_G hKC hKN hT.sylowT hcen hAut hE₁T hE₁ hE₁16 hQ2
    hfm.1 hfm.2.1 hfm.2.2.1 hfinn hz hz2 hzc u hu hu2

end CFSG.GH74.GLS
