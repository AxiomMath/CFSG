module

public import CFSG.GH74.GLS.C3.Layer1.Th2L625Rank

public section

namespace CFSG.GH74.GLS

@[expose] def NoV2Fine (G : Type) [Group G] : Prop :=
  ∀ (x y : G) (K : Subgroup G), IsV2Triple x y K → HasL2Model (kBar K) (fun q => q = 5)

@[expose] def S_thm1_rank4_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      HasL2Model (kBar K) (fun q => q = 5)

theorem s_thm1_rank4_of_rel (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hrel : S_thm1_rank4_rel) : S_thm1_rank4 := by
  intro G _ _ hG ⟨x, y, K, hU⟩
  by_contra hno
  have hNo : NoV2Fine G := fun a b L hv => absurd ⟨a, b, L, hv⟩ hno
  have h5 : HasL2Model (kBar K) (fun q => q = 5) := hrel G hG hNo x y K hU
  have h4 : twoPartCard K = 4 := Th2.L625.twoPartCard_of_l2_five h5
  have hr : 2 ≤ pRank 2 ↥(CxK x K) := b_625_rank_of h102 hL34 G hG x y K hU h4
  exact hno ⟨x, y, K, ⟨hU.1, hU.2.1, Or.inl hr, fun _ => hU⟩⟩

theorem noV2Fine_of_ctx
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hfm : Th2.L625.ClassFM9)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G} {K : Subgroup G}
    (hV : IsV2StarTriple x y K) (hK5 : HasL2Model (kBar K) (fun q => q = 5)) : NoV2Fine G :=
  fun _ _ _ hv => Th2.L625.lemma625a_of h102 hL34 hfm hG hV hK5 hv

theorem b_thm1_four_of_rel
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hfm : Th2.L625.ClassFM9)
    (hrel : S_thm1_rank4_rel) : B_thm1_four := by
  intro G _ _ hG x y K hV hK5 x' y' K' hU'
  exact Th2.L625.twoPartCard_of_l2_five
    (hrel G hG (noV2Fine_of_ctx h102 hL34 hfm hG hV hK5) x' y' K' hU')

theorem not_good_of_u2_not_five {G : Type} [Group G] (hNo : NoV2Fine G) {x y : G}
    {K : Subgroup G} (hU : Is2TerminalU2Triple x y K)
    (h : ¬ HasL2Model (kBar K) (fun q => q = 5)) :
    ¬ (2 ≤ pRank 2 ↥(CxK x K) ∨ IsExceptionalA7Triple x y K) :=
  fun hd => h (hNo x y K ⟨hU.1, hU.2.1, hd, fun _ => hU⟩)

end CFSG.GH74.GLS
