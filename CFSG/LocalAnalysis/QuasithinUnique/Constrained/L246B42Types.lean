module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A3Type
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace L246

variable {G : Type} [Group G] [Finite G]

namespace BlockData

variable {X T L : Subgroup G} {m : ℕ} (D : BlockData X T L m)

include D

theorem trData : TrData (VZ T X) L D.elem := ⟨D.block.1, D.LN, D.uV⟩

theorem hpc : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer (VZ T X : Set G) ↔ l ∈ CFSG.pCore 2 ↥L :=
  fun l => by
    rw [← centralizer_subgroupOf_eq_pCore D.charTwo D.sylow D.block D.uV, Subgroup.mem_subgroupOf]

theorem chiOrExc {KP : ∀ (Y : Type) [Group Y], Prop} (hK : Bridge.KClosed KP)
    (h42 : Bridge.AsB42With KP) (facts : Bridge.Alt57ModelFacts) (hKX : KP ↥X) :
    IsChiBlock X L ∨ IsExcA7Block L := by
  obtain ⟨A, hA, hAc⟩ := D.exists_offender
  have Hs := D.secHyp hA hAc
  have hFF := D.isFFStarOffender hA hAc
  have hV2 : ∀ v : IntMod (VZ T X) D.elem, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hKG : KP ↥(autI D.elem X) :=
    hK.of_hom_surjective hKX (rho1 D.elem D.XN) (rho1_surjective D.elem D.XN)
  have hLA : autI D.elem L ⊔ autI D.elem A ≤ autI D.elem X :=
    sup_le (autI_mono D.elem D.LX) (autI_mono D.elem (hA.1.trans D.TX))
  have hm8 : m ≤ 8 := by rcases D.m_cases with h | h <;> omega
  obtain ⟨hHyp, A₂, hA₂⟩ := Hs.b4Hyp hK hV2 hFF hKG hLA hm8
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
  rcases Bridge.Alt57.classification h42 facts (Bridge.sec_sq_eq_one hV2 _ _) C hHyp hA₂ with
    ⟨-, hSL⟩ | halt | ⟨hm7, -, hcard⟩
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

theorem altBlock_of_odd {KP : ∀ (Y : Type) [Group Y], Prop} (hK : Bridge.KClosed KP)
    (h42 : Bridge.AsB42With KP) (facts : Bridge.Alt57ModelFacts) {X T L : Subgroup G}
    (hX : CharTwo X) (hKX : KP ↥X) (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2)
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
  · exact (BlockData.mk hX hT hL hJN hUV hnot halt h5).chiOrExc hK h42 facts hKX
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

end CFSG.QuasithinUnique
