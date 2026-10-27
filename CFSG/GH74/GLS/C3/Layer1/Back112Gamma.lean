module

public import CFSG.GH74.GLS.C3.Layer1.Back91Core

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem inf_CMK_eq_bot_of_not_mem {x : G} {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q)
    (hG : IsKProperSimple G) (h81 : B_iv2_8_1) (h92 : B_lemma92)
    (hlist : HasL2Model (kBar L) Odd ∨ Nonempty (kBar L ≃* alternatingGroup (Fin 7)))
    {g : G} (hgM : g ∉ M) {V : Subgroup G} (hVQ : V ≤ conjugate Q g) (hVM : V ≤ M) (hV0 : V ≠ ⊥)
    (hV2 : 2 ≤ pRank 2 ↥V) : V ⊓ CMK M L = ⊥ := by
  have hQ2 : IsPGroup 2 ↥Q := hh.sylowQ.isPGroup
  have hVp : IsPGroup 2 ↥V := (isPGroup_conjugate' hQ2 g).to_le hVQ
  have hLg : ¬ L ≤ conjugate M g := by
    intro hLM
    refine hgM (h81 G hG M L Q hh.maximal hh.L_comp hh.L_normal.2 hh.sylowQ hh.gamma g ?_ hLM)
    intro h0
    apply hV0
    rw [eq_bot_iff]
    intro y hy
    have hy' : y ∈ conjugate Q g ⊓ M := ⟨hVQ hy, hVM hy⟩
    rw [h0] at hy'
    exact hy'
  have hΓ : gammaIn L V ≠ L := by
    intro hL
    apply hLg
    rw [← hL]
    refine iSup₂_le fun E hEV => iSup_le fun hE1 => ?_
    exact inf_le_of_left_le (normalizer_le_conjugate hh.gamma (hEV.trans hVQ) hE1)
  exact (h92 G L M V hh.L_normal.1 hh.L_normal.2 hlist hVp hVM hV2 hΓ).2.2.2

end CFSG.GH74.GLS.C3.Layer1.Back
