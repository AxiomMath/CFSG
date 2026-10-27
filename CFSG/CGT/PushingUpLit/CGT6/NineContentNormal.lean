module

public import CFSG.CGT.PushingUpLit.CGT6.SixSixteenNormal
public import CFSG.CGT.PushingUpLit.CGT6.SixFourSixStep
public import CFSG.CGT.PushingUpLit.Glue.NineContentGlue
public import CFSG.CGT.PushingUpLit.Glue.BlockInteract
public import CFSG.CGT.PushingUpLit.NineContent

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneRel CFSG.CGT.PushingUpLit.Nine CFSG.CGT.PushingUpLit.Glue
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inClassXG_of_maximal_pair_normal (h616 : AschbacherSixSixteenNormal)
    (hK : KProper InCatalog G) (hchar : CFSG.Assembly.IsCharTwoType G) (T : Sylow 2 G)
    {I H S : Subgroup G}
    (hc : NineChoice (characteristicCoreStar (T : Subgroup G)) I H S) {Y L : Subgroup G}
    (hY : NinePair (characteristicCoreStar (T : Subgroup G)) I Y L)
    (hmax : ∀ Y' L' : Subgroup G, NinePair (characteristicCoreStar (T : Subgroup G)) I Y' L' →
      Nat.card Y' ≤ Nat.card Y) : InClassXG Y := by
  have hY2 : InClassX ↥Y := hY.inClassX
  have hI2 : IsPGroup 2 I := hc.isPGroup
  have hLN : L = Subgroup.normalizer (oTwoIn L : Set G) :=
    le_antisymm (Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn L)) hY.closed
  have hOLN : oTwoIn L ≤ Subgroup.normalizer (Y : Set G) :=
    oTwoIn_le_normalizer_of_subnormal hY.Y_le hY.subnormal hY2.1
  have hIO2 : IsPGroup 2 (oTwoIn L ⊔ I : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_oTwoIn L) hI2
      (hY.I_le.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn L)))
  obtain ⟨Q₀, hQ₀, hQ₀sup⟩ := exists_isSylowOf_ge hIO2 (sup_le hOLN hY.le_normalizer)
  have hIQ₀ : I ≤ Q₀ := le_sup_right.trans hQ₀sup
  have hOQ₀ : oTwoIn L ≤ Q₀ := le_sup_left.trans hQ₀sup
  have hQ₀2 : IsPGroup 2 Q₀ := hQ₀.2.1
  obtain ⟨R, hR, hQ₀R, -⟩ := exists_isSylowOf_normalized hQ₀2
    (hQ₀.1.trans (normalizer_le_normalizer_centralizerModCore Y))
  have hOYR : oTwoIn Y ≤ R := oTwoIn_le_of_isSylowOf_centralizerModCore hR
  have hRne : R ≠ ⊥ := fun hb =>
    ThreeFromEight.oTwoIn_ne_bot_of_isShortGroup hY2.1 (le_bot_iff.1 (hb ▸ hOYR))
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_of_isSylowOf_centralizerModCore hR
  have hKloc : IsPLocal 2 (Subgroup.normalizer (R : Set G)) := ⟨R, hRne, hR.2.1, rfl⟩
  have hKchar : IsCharacteristicP 2 ↥(Subgroup.normalizer (R : Set G)) :=
    isCharacteristicP_of_isPLocal hchar hKloc
  have hIK : I ≤ Subgroup.normalizer (R : Set G) := hIQ₀.trans hQ₀R
  have hKM : ¬ Subgroup.normalizer (R : Set G) ≤ characteristicCoreStar (T : Subgroup G) :=
    fun hle => hY.not_le (hYR.trans hle)
  obtain ⟨T', hT', hQ₀T'⟩ := exists_isSylowOf_ge hQ₀2 hQ₀R
  have hJT' : jIn T' = I := (hc.sylow_jIn _ T' hKchar hIK hKM hT' (hIQ₀.trans hQ₀T')).1
  have hT'Y : T' ⊓ Subgroup.normalizer (Y : Set G) = Q₀ :=
    le_antisymm (le_of_isSylowOf_of_le hQ₀ (hT'.2.1.to_le inf_le_left) (le_inf hQ₀T' hQ₀.1)
      inf_le_right) (le_inf hQ₀T' hQ₀.1)
  have hZ : ⁅omegaOneCenterIn T', Y⁆ ≠ ⊥ := by
    rw [Subgroup.commutator_comm]
    exact nine_five hchar T hc hY.not_le hKchar hYR hIK hT' (hIQ₀.trans hQ₀T')
  have hLeq : Subgroup.normalizer (oTwoIn L : Set G) = L := hLN.symm
  have hU : ⁅oTwoIn Y, Y⁆ ≤ oTwoIn L :=
    (blockU_le_oTwoIn Y).trans (ThreeFromEight.oTwoIn_le_oTwoIn_of_isSubnormal hY.Y_le hY.subnormal)
  have hYU : Y ≤ Subgroup.normalizer (oTwoIn L : Set G) :=
    hY.Y_le.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn L))
  have hYUs : (Y.subgroupOf (Subgroup.normalizer (oTwoIn L : Set G) ⊓
      Subgroup.normalizer (R : Set G))).IsSubnormal := by
    rw [hLeq]
    exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le inf_le_left hY.subnormal
  have hYT : Y = ⁅jIn T', Y⁆ := by
    rw [hJT', Subgroup.commutator_comm]
    exact hY.commutator_eq.symm
  have hRsyl : IsSylowOf 2 R (centralizerModCore Y ⊓ Subgroup.normalizer (R : Set G)) :=
    isSylowOf_of_le hR (le_inf hR.1 Subgroup.le_normalizer) inf_le_left
  have hSsyl : IsSylowOf 2 T' (Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (R : Set G)) := by
    rw [inf_idem]
    exact hT'
  have hSY : IsSylowOf 2 (T' ⊓ Subgroup.normalizer (Y : Set G))
      (Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (R : Set G)) := by
    rw [hT'Y]
    exact isSylowOf_of_le hQ₀ (le_inf hQ₀.1 hQ₀R) inf_le_left
  have hOK : oTwoIn (Subgroup.normalizer (R : Set G)) = R :=
    AschbacherSixSixteenPR.rel aschbacherSixSixteenPR_holds hK hKchar hYR hY2 hT' hYT hRsyl le_rfl
      hU (hOQ₀.trans hQ₀T') hYU hYUs hSsyl hSY hZ
  obtain ⟨X, hYX, hXK, hXsub, hXcl⟩ := AschbacherSixSixteenNormal.rel h616 hK hKchar hYR hY2 hT'
    hYT hRsyl le_rfl hU (hOQ₀.trans hQ₀T') hYU hYUs hSsyl hSY hZ
  have hINX : I ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_contains hKchar ⟨hXK, hXsub, hXcl⟩ hY2 hYX hIK hY.le_normalizer
  have hpair : NinePair (characteristicCoreStar (T : Subgroup G)) I X
      (Subgroup.normalizer (R : Set G)) :=
    { inClassX := hXcl
      not_le := fun hle => hY.not_le (hYX.trans hle)
      le_normalizer := hINX
      commutator_eq := commutator_eq_of_contains hXcl hY2 hYX hINX hY.commutator_eq
      I_le := hIK
      Y_le := hXK
      subnormal := hXsub
      oTwo_ne_bot := by rw [hOK]; exact hRne
      closed := by rw [hOK] }
  have hXY : Y = X := Subgroup.eq_of_le_of_card_ge hYX (hmax X _ hpair)
  have h1 : Y ≤ Subgroup.normalizer (R : Set G) ∧
      (Y.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal :=
    ⟨hYR, hXY ▸ hXsub⟩
  have h2 : Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ := by
    have hIJ : I ≤ jIn (Subgroup.normalizer (Y : Set G)) :=
      le_jIn_of_isSylowOf hQ₀ hQ₀T' hJT' hIQ₀ hc.jIn_self
    refine le_antisymm ?_ ?_
    · calc Y = ⁅Y, I⁆ := hY.commutator_eq.symm
        _ ≤ ⁅Y, jIn (Subgroup.normalizer (Y : Set G))⁆ := Subgroup.commutator_mono le_rfl hIJ
        _ = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ := Subgroup.commutator_comm _ _
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.1 ((jIn_le _).trans le_rfl)
  exact inClassXG_of_sylow hY2 hR h1 (Or.inl h2)

theorem aschbacherNineContent_of_bhs_normal (hbhs : BHS.BHSLocalCStar)
    (h616 : AschbacherSixSixteenNormal) : AschbacherNineContent := by
  intro G _ _ hK hchar T I H S hc
  obtain ⟨Y₀, hY₀⟩ := exists_base_pair hbhs hchar T hc
  obtain ⟨Y, L, hY, hmax⟩ := exists_extremal_pair _ _ ⟨Y₀, H, hY₀⟩
  exact ⟨Y, inClassXG_of_maximal_pair_normal h616 hK hchar T hc hY hmax⟩

theorem aschbacherNineContent_of_sixFourNormal_noSixThree
    (hbhs : CFSG.CGT.PushingUpLit.BHS.BHSLocalCStar) (hN : AschbacherSixFourNormal) :
    AschbacherNineContent :=
  aschbacherNineContent_of_bhs_normal hbhs (aschbacherSixSixteenNormal_of_sixFourNormal hN)

theorem aschbacherNineContent_of_sixFourCore_noSixThree
    (hbhs : CFSG.CGT.PushingUpLit.BHS.BHSLocalCStar) (hc : AschbacherSixFourCore) :
    AschbacherNineContent :=
  aschbacherNineContent_of_sixFourNormal_noSixThree hbhs (aschbacherSixFourNormal_of_core hc)

end CFSG.CGT.PushingUpLit.CGT6
