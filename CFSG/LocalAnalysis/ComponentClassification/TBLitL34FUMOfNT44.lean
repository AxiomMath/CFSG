module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUStep
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TerminalFullCover
public import CFSG.LocalAnalysis.ComponentClassification.GSRankThreeCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU
public import CFSG.GH74.GLS.NT44.TwoTerminalExclusion
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigAmbient

set_option autoImplicit false

public section

namespace CFSG.ComponentClassification.TBLit

section L34CentreSixteen

theorem l34_center_card_sixteen_false {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hnotCat : ¬ CFSG.Blueprint.Catalog G)
    (x : G) (hx : orderOf x = 2)
    {L : Subgroup G}
    (hL : CFSG.ComponentClassification.FooteLit.IsTwoComponentIn L
      (Subgroup.centralizer ({x} : Set G)))
    (hLie : CFSG.Blueprint.LieModel (↥L ⧸ CFSG.Open.fusionZStar ↥L) .PSL 3 2 2)
    (h16 : Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pPrimeCore 2 ↥L)) = 16) :
    False := by
  classical
  have hNoncentral : ∀ z : G, orderOf z = 2 → z ∉ Subgroup.center G := by
    have hZ : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    intro z hz hzc
    rw [hZ, Subgroup.mem_bot] at hzc
    rw [hzc, orderOf_one] at hz
    norm_num at hz
  have hRank : ∀ z : G, orderOf z = 2 →
      3 ≤ CFSG.pRank 2 ↥(Subgroup.centralizer ({z} : Set G)) :=
    fun z hz => CFSG.ComponentClassification.GSThmB.three_le_pRank_centralizer_of_not_catalog
      hnonab hnotCat z hz
  have hIL2 : CFSG.GH74.GLS.IsIL2Pair x L := ⟨hx, hL.1, hL.2⟩
  have hperf := CFSG.ComponentClassification.UnbalancedCorr.commutator_eq_of_isPComponent
    hL.1 hL.2
  have hIndex : (CFSG.pPrimeCore 2 ↥L).index = 322560 :=
    (CFSG.ComponentClassification.GrSLit.L34GM.card_center_of_index hperf hLie).mpr h16
  obtain ⟨-, -, t, M, -, -, -, hterm, -, -, hLieM, h16M⟩ :=
    CFSG.ComponentClassification.GrSLit.L34Terminal.exists_twoTerminal_same_full_cover
      G hKP hNoncentral hRank x L hIL2 hLie hIndex
  have hL34M : CFSG.GH74.GLS.IsL34Quotient (CFSG.GH74.GLS.kBar M) :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (CFSG.ComponentClassification.Sol78.coreQuotientCenterEquiv ↥M).symm hLieM
  exact (CFSG.GH74.GLS.NT44.false_of_isTwoTerminal_center_card_sixteen
    G hnonab hKP t M hterm hL34M h16M).elim

theorem l34_zStar_ratio_false {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hnotCat : ¬ CFSG.Blueprint.Catalog G)
    (x : G) (hx : orderOf x = 2)
    {L : Subgroup G}
    (hL : CFSG.ComponentClassification.FooteLit.IsTwoComponentIn L
      (Subgroup.centralizer ({x} : Set G)))
    (hLie : CFSG.Blueprint.LieModel (↥L ⧸ CFSG.Open.fusionZStar ↥L) .PSL 3 2 2)
    (hratio : Nat.card ↥(CFSG.ComponentClassification.GrSLit.zStarIn L) =
      16 * Nat.card ↥(CFSG.ComponentClassification.GrSLit.oddIn L)) :
    False := by
  have hzCard : Nat.card ↥(CFSG.ComponentClassification.GrSLit.zStarIn L) =
      Nat.card ↥(CFSG.Open.fusionZStar ↥L) := by
    rw [CFSG.ComponentClassification.GrSLit.zStarIn,
      Subgroup.card_map_of_injective L.subtype_injective]
  have hoddCard : Nat.card ↥(CFSG.ComponentClassification.GrSLit.oddIn L) =
      Nat.card ↥(CFSG.pPrimeCore 2 ↥L) := by
    rw [CFSG.ComponentClassification.GrSLit.oddIn,
      Subgroup.card_map_of_injective L.subtype_injective]
  have hratio' : Nat.card ↥(CFSG.Open.fusionZStar ↥L) =
      16 * Nat.card ↥(CFSG.pPrimeCore 2 ↥L) := by
    rw [← hzCard, ← hoddCard]
    exact hratio
  have hOpos : 0 < Nat.card ↥(CFSG.pPrimeCore 2 ↥L) := Nat.card_pos
  have hcenter : Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pPrimeCore 2 ↥L)) = 16 := by
    have hcard := CFSG.ComponentClassification.GrSLit.L34GM.card_fusionZStar_eq (↥L)
    have h' : Nat.card ↥(CFSG.pPrimeCore 2 ↥L) *
        Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pPrimeCore 2 ↥L)) =
        Nat.card ↥(CFSG.pPrimeCore 2 ↥L) * 16 := by
      calc
        Nat.card ↥(CFSG.pPrimeCore 2 ↥L) *
            Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pPrimeCore 2 ↥L)) =
            Nat.card ↥(CFSG.Open.fusionZStar ↥L) := hcard.symm
        _ = 16 * Nat.card ↥(CFSG.pPrimeCore 2 ↥L) := hratio'
        _ = Nat.card ↥(CFSG.pPrimeCore 2 ↥L) * 16 := Nat.mul_comm _ _
    exact Nat.eq_of_mul_eq_mul_left hOpos h'
  exact l34_center_card_sixteen_false hnonab hKP hnotCat x hx hL hLie hcenter

end L34CentreSixteen

theorem l34FieldUnitaryMaximalStep_holds
    : L34FieldUnitaryMaximalStep := by
  intro X _ _ _ hnonab hKP hz hU b y v K hTriple hbK hType hCard hUnit hvb hvy hField
  have hnotCat : ¬ CFSG.Blueprint.Catalog X :=
    CFSG.ComponentClassification.GSThmB.not_catalog_of_not_uOutcome
      CFSG.ComponentClassification.FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
      hnonab hz hU
  obtain ⟨hb2, -, -, hKle, hKcomp, -, -⟩ := hTriple
  have h2comp : CFSG.ComponentClassification.FooteLit.IsTwoComponentIn K
      (Subgroup.centralizer ({b} : Set X)) := ⟨hKle, hKcomp⟩
  exact (l34_zStar_ratio_false hnonab hKP hnotCat b hb2 (L := K) h2comp hType hCard).elim

end CFSG.ComponentClassification.TBLit

end
