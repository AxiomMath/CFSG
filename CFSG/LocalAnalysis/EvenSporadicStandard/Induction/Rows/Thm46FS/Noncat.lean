module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenResidual
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenSmallLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.EvenCoverStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpKill
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus

@[expose] def Sol78Thm46SuzEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    Nat.card ↥(center L) = 2 → IsSporadic (↥L ⧸ center ↥L) .Suz → CFSG.Blueprint.Catalog G

@[expose] def SuzCentralTwo : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → IsPGroup 2 (center L) →
    IsSporadic (L ⧸ center L) .Suz → Nat.card (center L) ∣ 2

theorem suzCentralTwo_of_centralTwoBound (h : CentralTwoBound) : SuzCentralTwo :=
  fun L _ _ hq hZ hs => (h L hq hZ .Suz hs).1

section Noncat

theorem catalog_of_oddLieType {X : Type} [Group X] (h : OddLieType X) :
    CFSG.Blueprint.Catalog X := by
  obtain ⟨t, n, p, f, -, -, -, hm⟩ := h
  exact lieModel_catalog X t n p f hm

theorem catalog_of_alt {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (e : X ≃* alternatingGroup (Fin n)) : CFSG.Blueprint.Catalog X :=
  Or.inr (Or.inl ⟨n, hn, ⟨e⟩⟩)

theorem catalog_of_isSporadic {X : Type} [Group X] {s : TauCeti.SporadicName}
    (h : IsSporadic X s) : CFSG.Blueprint.Catalog X :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨s, h⟩)))

theorem catalog_of_evenSporadicOutcome {X : Type} [Group X]
    (h : Recognition.EvenSporadicOutcome X) : CFSG.Blueprint.Catalog X := by
  rcases h with h | h | h | h | h | h | h <;> exact catalog_of_isSporadic h

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem catalog_of_rankTwo (hRK : Outer.RankTwoStdRec)
    (hna : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {P : Subgroup G} (hP : SolStd P) (hPq : CFSG.IsQuasisimple ↥P)
    (hrk : ¬ CFSG.pRank 2 ↥(centralizer (P : Set G)) ≤ 1) : CFSG.Blueprint.Catalog G := by
  have hrk' : 2 ≤ CFSG.Open.pRank 2 (centralizer (P : Set G)) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    omega
  rcases hRK G hna hkp P (standardComponentIsStandard_of_solStd hP hPq) hrk' with
    ⟨n, hn, ⟨e⟩⟩ | h | h | h | h | h
  · exact catalog_of_alt (by omega) e
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h

theorem catalog_of_genQuaternion (thm24_1 : Sol78Thm24_1Use) (hna : ∃ a b : G, a * b ≠ b * a)
    (hord : ¬ Nat.card G ∣ 95040) {P : Subgroup G} (hP : SolStd P)
    (S : Sylow 2 ↥(centralizer (P : Set G))) (hq : IsGenQuaternion ↥S) :
    CFSG.Blueprint.Catalog G := by
  have hfs := fStarSimple_top G hna
  have hodd := thm24_1 G ⊤ hfs (by rwa [Subgroup.card_top]) P hP ⟨S, hq⟩
  exact CFSG.SectionRank.catalog_of_mulEquiv Subgroup.topEquiv.symm (catalog_of_oddLieType hodd)

theorem isCyclic_sylow_of_noncat (hRK : Outer.RankTwoStdRec) (thm24_1 : Sol78Thm24_1Use)
    (hna : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hnc : ¬ CFSG.Blueprint.Catalog G) {P : Subgroup G} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P) (hord : ¬ Nat.card G ∣ 95040)
    (S : Sylow 2 ↥(centralizer (P : Set G))) :
    IsCyclic ↥(S : Subgroup ↥(centralizer (P : Set G))) := by
  by_cases hrk : CFSG.pRank 2 ↥(centralizer (P : Set G)) ≤ 1
  · have hrS : CFSG.pRank 2 ↥(S : Subgroup ↥(centralizer (P : Set G))) ≤ 1 :=
      (pRank_two_le_of_injective (S : Subgroup ↥(centralizer (P : Set G))).subtype
        (S : Subgroup ↥(centralizer (P : Set G))).subtype_injective).trans hrk
    rcases isCyclic_or_genQuaternion_of_pRank_le_one S.isPGroup' hrS with hc | hq
    · exact hc
    · exact (hnc (catalog_of_genQuaternion thm24_1 hna hord hP S hq)).elim
  · exact (hnc (catalog_of_rankTwo hRK hna hkp hP hPq hrk)).elim

theorem sporadicRep_of_even_cyclic
    (hCTE : CTEvenResidualStatement)
    (hSmall : CTEvenSmallLieStatement) (hna : ∃ a b : G, a * b ≠ b * a)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hnc : ¬ CFSG.Blueprint.Catalog G)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 ↥(centralizer (L : Set G)))
    (hS : IsCyclic ↥(S : Subgroup ↥(centralizer (L : Set G))))
    (htype : Recognition.Exact.EvenStandardType (↥L ⧸ center ↥L))
    (hexc : ¬ Recognition.Exact.EvenStandardException (↥L ⧸ center ↥L)) :
    SporadicRep (↥L ⧸ center ↥L) := by
  have hres := hCTE G hna hkp L hL hcore S hS htype hexc
  rcases hres.2 with hA | hB | hC | hD
  · exact hA.1
  · exact (hnc (catalog_of_evenSporadicOutcome
      (hSmall G hna hkp L hL hcore S hS htype hexc hres (Or.inl hB)))).elim
  · exact (hnc (catalog_of_evenSporadicOutcome
      (hSmall G hna hkp L hL hcore S hS htype hexc hres (Or.inr (Or.inl hC))))).elim
  · exact (hnc (catalog_of_evenSporadicOutcome
      (hSmall G hna hkp L hL hcore S hS htype hexc hres (Or.inr (Or.inr hD))))).elim

theorem not_card_dvd_95040_of_gt {P : Subgroup G} (h : 95040 < Nat.card (↥P ⧸ center ↥P)) :
    ¬ Nat.card G ∣ 95040 := by
  have h2 : Nat.card (↥P ⧸ center ↥P) ∣ Nat.card ↥P := Subgroup.card_quotient_dvd_card _
  have h3 : Nat.card ↥P ∣ Nat.card G := Subgroup.card_subgroup_dvd_card P
  have h4 : Nat.card (↥P ⧸ center ↥P) ≤ Nat.card G :=
    Nat.le_of_dvd Nat.card_pos (h2.trans h3)
  exact not_dvd_95040_of_lt (lt_of_lt_of_le h h4)

end Noncat

end CFSG.EvenSporadicStandard.Induction
