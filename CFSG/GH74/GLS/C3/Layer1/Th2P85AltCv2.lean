module

public import CFSG.GH74.GLS.C3.Layer1.Th2P88bRows
public import CFSG.GH74.GLS.C3.Layer1.Th2P85AltSE

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85

@[expose] def B_thm2_p85_alt_cv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x y : G) (K T S M L : Subgroup G),
    P85Struct x y K T S M L → Ivk73Alt (imgM M K) (imgM M L) → centralizer ({x} : Set G) ≤ M →
      ∀ W : Subgroup G, IsSylowOf 2 W M → T ⊓ M ≤ W → ∀ v ∈ W, orderOf v = 2 →
        (∀ w ∈ W, v * w = w * v) → centralizer ({v} : Set G) ≤ M

theorem centralizer_le_M_both
    (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) {G : Type} [Group G] [Finite G] {x y : G}
    {K T S M L : Subgroup G} (hstruct : P85Struct x y K T S M L) :
    centralizer ({x} : Set G) ≤ M := by
  by_cases hterm : IsTerminalPair 2 x K
  · have hstd : Th2Std x y K T S := hstruct.choice.std
    rcases hstruct.choice with hM1 | ⟨ρ, B, hM2⟩
    · have hgam := Th2.CaseI.gammaK_le_normalizer_of_standard hM1.standard hM1.sylowQ
      exact ((C3.Layer1.U1a.centralizer_le_gammaK (Q := T ⊓ CxK x K)
        ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩ hstd.orderOf_x).trans hgam).trans hM1.le_M
    · exact absurd hterm hM2.nonterminal
  · exact Th2.P88b.centralizer_le_M_of_struct hL34 h82 hstruct hterm

theorem b_thm2_p85_alt_cent_of_cv
    (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) (h : B_thm2_p85_alt_cv) :
    B_thm2_p85_alt_cent := by
  intro G _ _ x y K T S M L hstruct halt
  have hCx := centralizer_le_M_both hL34 h82 hstruct
  exact ⟨fun _ => hCx, fun W hW hTW v hv hv2 hvc =>
    h G x y K T S M L hstruct halt hCx W hW hTW v hv hv2 hvc⟩

theorem b_thm2_p85_alt_of_cv
    (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) (h : B_thm2_p85_alt_cv) : B_thm2_p85_alt :=
  b_thm2_p85_alt_of_cent (b_thm2_p85_alt_cent_of_cv hL34 h82 h)

end CFSG.GH74.GLS
