module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Types
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourJNative

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace L246

variable {G : Type} [Group G] [Finite G]

namespace BlockData

variable {X T L : Subgroup G} {m : ℕ} (D : BlockData X T L m)

include D

theorem chiOrExc_of_A57 (h : AsB42A57) : IsChiBlock X L ∨ IsExcA7Block L := by
  obtain ⟨A, hA, hAc⟩ := D.exists_offender
  have Hs := D.secHyp hA hAc
  have hFF := D.isFFStarOffender hA hAc
  have hV2 : ∀ v : IntMod (VZ T X) D.elem, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hA2 : ∀ a ∈ autI D.elem A, a ^ 2 = 1 := hFF.2.2.1.2
  have C : Bridge.Alt57.Ctx
      (autSec (autI D.elem L ⊔ autI D.elem A) (intSub D.elem (blockU L)) (intSub D.elem (blockZ L)))
      (autSec (autI D.elem L) (intSub D.elem (blockU L)) (intSub D.elem (blockZ L))) m :=
    ⟨D.m_cases, Hs.iso_autSec, (Hs.genFitting_eq hA2 hV2).symm, Hs.sqG hA2⟩
  have hodd : Odd m := by
    rcases D.m_cases with h | h
    · exact ⟨2, by omega⟩
    · exact ⟨3, by omega⟩
  have hm3 : 3 ≤ m := by rcases D.m_cases with h | h <;> omega
  obtain ⟨A₂, hA₂⟩ := ((B1_4_5 (Bridge.sec_sq_eq_one hV2 _ _)
    (autSec (autI D.elem L ⊔ autI D.elem A) (intSub D.elem (blockU L))
      (intSub D.elem (blockZ L)))).out 1 2).1 (Hs.isFFModule hFF)
  rcases h _ (Bridge.sec_sq_eq_one hV2 _ _) _ _ A₂ m C Hs.isIrrSec hA₂ with
    ⟨-, hSL⟩ | halt | ⟨hm7, hcard⟩
  · obtain ⟨K, hKf, hKfin, hKcard, π, hπ⟩ := hSL
    have hπinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful _)
    exact Or.inl ⟨D.block, Or.inl ⟨2, by norm_num,
      D.trData.isLin2Type_of_nat hKcard Hs.secRestrict_injective D.hpc hπ hπinj⟩⟩
  · obtain ⟨π, hπ⟩ := halt
    have := Hs.isSimple_autSec
    have : IsSimpleGroup (alternatingGroup (Fin m)) := Bridge.alt_isSimple Hs.five_le
    have hπinj : Function.Injective π :=
      Bridge.injective_of_surjective_of_simple (Γ := ↥(alternatingGroup (Fin m))) π hπ.1
    exact Or.inl ⟨D.block, Or.inr ⟨m, hodd, hm3,
      D.trData.isAltType_of_altDn hodd Hs.secRestrict_injective D.hpc hπ hπinj⟩⟩
  · subst hm7
    obtain ⟨e⟩ := Hs.iso_autSec
    exact Or.inr (D.trData.isExcA7Block_of_card Hs.secRestrict_injective D.hpc e hcard)

end BlockData

theorem altBlock_of_odd_of_A57 (h : AsB42A57) {X T L : Subgroup G}
    (hX : CharTwo X) (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2)
    (hT : IsSylowTwoOf T X) (hL : IsBlock2 X L) (hUV : blockU L ≤ VZ T X)
    (hJN : thompsonJ T ≤ Subgroup.normalizer (L : Set G))
    (hnot : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G)) {m : ℕ} (hm : Odd m)
    (hm3 : 3 ≤ m) (halt : IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m) :
    IsChiBlock X L ∨ IsExcA7Block L := by
  obtain ⟨α, hαs, hαk⟩ := exists_alt_pCore hX hT hL hUV halt
  by_cases h3 : m = 3
  · subst h3
    refine Or.inl ⟨hL, Or.inr ⟨3, ⟨1, rfl⟩, le_rfl, isAltType_three hL.1 ?_⟩⟩
    rw [card_quotient_pCore_of_alt α hαs hαk, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  by_cases h5 : m = 5 ∨ m = 7
  · exact (BlockData.mk hX hT hL hJN hUV hnot halt h5).chiOrExc_of_A57 h
  · exfalso
    have hm9 : 9 ≤ m := by
      obtain ⟨k, rfl⟩ := hm
      omega
    have h3L : 3 ≤ CFSG.Open.pRank 3 L := three_le_pRank_of_alt hm9 α hαs hαk
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h4 : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 X :=
      CFSG.SectionRank.pRank_mono (by norm_num) hL.2.1
    have h6 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 3 X :=
      pRank_top_subtype (p := 3) X
    omega

end L246

namespace L238

variable {G : Type} [Group G] [Finite G]

theorem altBlockStatementJCat_of_asB42A57 (h : AsB42A57) : AltBlockStatementJCat (G := G) := by
  intro X T L hX hSQ hT hL hUV hJN hnot ⟨m, hm, hm3, halt⟩
  exact L246.altBlock_of_odd_of_A57 h hX
    (rank_le_of_isSQTKCat hSQ Nat.prime_three (by norm_num)) hT hL hUV hJN hnot hm hm3 halt

end L238

end CFSG.QuasithinUnique
