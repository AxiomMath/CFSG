module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OrthConcl
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Omega4MinusOfOrth
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Alt5OfOrth
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FaithfulA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Short2OfA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M3
public import CFSG.Quasithin.Background.C35NatFF
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.EmptyFaithful.S152He9A5
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNaturalD
public import CFSG.Quasithin.Background.Omega4AutOn

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4.E443 CFSG.GH74.QTGen4.DSGen4
open scoped IsMulCommutative

theorem isNaturalSection_of_isLin2Type_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : IsLin2Type L 2) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ 2 ∧
      IsNaturalSection L (blockU L) (blockZ L) (CFSG.pCore 2 ↥L) (StatedSL 2 F) := by
  obtain ⟨F, hFld, hFintype, hFcard, α, hαs, hαker, β, hβs, hβker, hβeq⟩ := h
  letI := hFld
  letI := hFintype
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
  refine ⟨F, hFld, hFintype, hFcard, CFSG.QuasithinUnique.C1.le_normalizer_blockU L,
    e.toMonoidHom.comp α, e.surjective.comp hαs, ?_, β, hβs, hβker, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change e (α x) = 1 ↔ x ∈ CFSG.pCore 2 ↥L
    rw [e.map_eq_one_iff, ← MonoidHom.mem_ker, hαker]
  · intro a u v huv
    rw [hβeq a u v huv]
    rfl

theorem KConfig.conclK_of_sixteen_a5
    {G : Type} [Group G] [Finite G] {L V MK : Subgroup G}
    (h : KConfig G L V MK) (hV : Nat.card V = 16) (hO : CFSG.Open.pCoreOf 2 L = V)
    (hC : Subgroup.centralizer (V : Set G) ≤ V)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 5)) : ConclK G L V MK := by
  classical
  have he : IsElemAbelian 2 (CFSG.Open.pCoreOf 2 L) := hO ▸ h.elemAbelian
  have hn : Nat.card (CFSG.Open.pCoreOf 2 L) = 16 := hO ▸ hV
  have hc : CharTwo L := by
    unfold CharTwo
    rw [hO]
    exact inf_le_right.trans hC
  obtain ⟨ePSL⟩ := CFSG.Quasithin.He9.nonempty_psl2_gf4_mulEquiv_alternating
  let eSP := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
    (GaloisField 2 2)
  have hq : IsL2Quot 2 (oTwoQuot ↥L) := ⟨e.trans ePSL.symm⟩
  have hpsl : IsPSL 2 2 2 (ModO2 L) :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by norm_num, by norm_num⟩,
      GaloisField 2 2, inferInstance, inferInstance,
      by rw [GaloisField.card 2 2 (by norm_num)],
      ⟨e.trans (ePSL.symm.trans eSP)⟩⟩
  have hcardQ : Nat.card (ModO2 L) = 60 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.QuasithinUnique.A5.Delta5.a5_card
  have hQ : CFSG.IsQuasisimple (ModO2 L) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl (by rw [hcardQ]; norm_num)
      (by rw [hcardQ]; norm_num)
  have hshape : Shape443 (ModO2 L) :=
    Or.inl ⟨2, by norm_num, Or.inl ⟨by decide, hpsl⟩⟩
  have hpre : A5Pre L L (CFSG.Open.pCoreOf 2 L) ⊥ := omega_a5Pre_self hq hc he hn
  rcases hpre.exists_model' with ⟨hNatSec, ⟨M⟩⟩ | ⟨hNotNatSec, ⟨M⟩⟩
  ·
    have hlin : IsLin2Type L 2 := Lin2D.isLin2Type_of_natural hq hc he hn hNatSec
    obtain ⟨F, hFld, hFintype, hFcard, hsec⟩ := isNaturalSection_of_isLin2Type_two hlin
    letI := hFld
    letI := hFintype
    have h2n : (2 : F) ^ 2 = 0 := by
      have h := FiniteField.cast_card_eq_zero F
      rw [hFcard] at h
      norm_num at h ⊢
      exact h
    have h2 : (2 : F) = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 h2n
    have hU : blockU L = CFSG.Open.pCoreOf 2 L := blockU_eq_pCoreOf a5Facts a5Facts.groupN hpre M
    have hUV : blockU L = V := hU.trans hO
    have hV2 : ∀ v ∈ blockU L, v ^ 2 = 1 := by
      intro v hv
      rw [hU] at hv
      exact he.2 v hv
    have hW : blockZ L ≤ Subgroup.centralizer (L : Set G) := by
      unfold blockZ
      exact inf_le_right
    have hEq : (CFSG.pCore 2 ↥L).map L.subtype = CFSG.Open.pCoreOf 2 L :=
      rfl
    have hN : (CFSG.pCore 2 ↥L).map L.subtype ≤ Subgroup.centralizer (blockU L : Set G) := by
      rw [hEq, hU, hO]
      simpa [hO] using h.pCoreOf_le
    haveI : IsMulCommutative ↥(blockU L) := by
      rw [hU]
      exact he.1
    have hFFL : IsFFModule (V := ↥(blockU L)) (autOn L (blockU L)) :=
      isFFModule_autOn_of_isNaturalSection_two h2 hV2 hW hN hsec
    have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) :=
      CFSG.QuasithinUnique.C1.le_normalizer_blockU L
    have hFF' : IsFFModule (V := ↥(blockU L))
        (autOn (Subgroup.normalizer (blockU L : Set G)) (blockU L)) :=
      CFSG.Quasithin.H13.Prop329.isFFModule_of_le
        (CFSG.Quasithin.AutOn.autOn_mono hLU) hFFL
    letI : IsMulCommutative ↥V := h.elemAbelian.1
    have hFF : IsFFModule (V := ↥V) (autOn (Subgroup.normalizer (V : Set G)) V) :=
      hUV ▸ hFF'
    have hCL : ConclKLeft G L V MK :=
      ⟨hQ, hshape, Or.inl ⟨⟨h.elemAbelian.1, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
    exact hCL.conclK
    ·
      intro h3
      have h1 := LieModel.card_psl_three_two h3
      rw [hcardQ] at h1
      norm_num at h1
    ·
      intro h4
      have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
        (h4.statedClassicalModel (by decide))
      rw [hcardQ] at h1
      norm_num at h1
    ·
      rintro ⟨-, hcent, -⟩
      rw [CFSG.Quasithin.F420.center_eq_bot_of_statedPSL hpsl] at hcent
      rw [Subgroup.card_bot] at hcent
      norm_num at hcent
    ·
      intro _ h64
      rw [hV] at h64
      norm_num at h64
  ·
    have hU : blockU L = CFSG.Open.pCoreOf 2 L := blockU_eq_pCoreOf a5Facts a5Facts.groupO hpre M
    have hUV : blockU L = V := hU.trans hO
    have hZ : blockZ L = ⊥ := blockZ_eq_bot (fixZero_HO a5Facts) M hU
    haveI : DSLeaf LeafFaithfulA5 := ⟨leafFaithfulA5⟩
    haveI : DSLeaf LeafShort2OfA5 := ⟨leafShort2OfA5⟩
    haveI : DSLeaf LeafM3 := ⟨leafM3⟩
    haveI : DSLeaf LeafAlt5OfOrth := ⟨leafAlt5OfOrth⟩
    haveI : DSLeaf LeafOmega4MinusOfOrth := ⟨leafOmega4MinusOfOrth⟩
    have hIso : IsOmega4MinusType L 1 := omega4_minus_of_orth hq hc he hn hNotNatSec
    have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := by
      rw [hU, hO]
      exact h.le_normalizer
    have hQU : CFSG.Open.pCoreOf 2 L ≤ Subgroup.centralizer (blockU L : Set G) := by
      rw [hU, hO]
      simpa [hO] using h.pCoreOf_le
    haveI : IsMulCommutative ↥(blockU L) := by
      rw [hU]
      exact he.1
    have hO' : BinaryOrthogonalFour (V := ↥(blockU L)) (autOn L (blockU L)) ⊤ ⊥ 1 :=
      CFSG.Quasithin.IsOmega4MinusType.binaryOrthogonalFour_autOn hIso hZ hLU hQU
    exact (hUV ▸ conclKLeft_of_binaryOrthogonalFour (m := 1) le_rfl hpsl hO').conclK

end CFSG.SectionRank.QTK.Insp443

end
