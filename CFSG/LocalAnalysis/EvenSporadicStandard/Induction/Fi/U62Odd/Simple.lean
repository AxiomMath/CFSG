module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ReduceHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm24OneCIT
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpRankTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.EvenCoverStd
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Complete
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAut
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutCaseInput

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.U62Odd

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.EvenSmallLie

private theorem center_eq_bot_of_solStd_odd {G : Type} [Group G] [Finite G]
    {P : Subgroup G} (hP : SolStd P) (hodd : Odd (Nat.card ↥(center ↥P)))
    (hcore : ∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) :
    center ↥P = ⊥ := by
  obtain ⟨t, ht2, hcomp⟩ := hP.exists_involution
  have htC : t ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro p hp
    exact mem_centralizer_singleton_iff.mp (hcomp.le hp)
  let C : Subgroup G := centralizer ({t} : Set G)
  have hle : P ≤ C := hcomp.le
  have hCnorm : C ≤ normalizer (P : Set G) := hP.centralizer_le_normalizer htC ht2
  have hPnorm : (P.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hCnorm
  let Pc : Subgroup ↥C := P.subgroupOf C
  let Zc : Subgroup ↥C := (Subgroup.center ↥Pc).map Pc.subtype
  have hZnorm : Zc.Normal :=
    CFSG.OrderReductions.OddCore.characteristic_subgroup_map_normal Pc (Subgroup.center ↥Pc)
  let e : ↥Pc ≃* ↥P := Subgroup.subgroupOfEquivOfLe hle
  have hcenter_map : Subgroup.map (e : ↥Pc →* ↥P) (Subgroup.center ↥Pc) = Subgroup.center ↥P :=
    Subgroup.map_center_eq e
  have hZodd : Odd (Nat.card ↥Zc) := by
    have hcard : Nat.card ↥Zc = Nat.card ↥(Subgroup.center ↥P) := by
      change Nat.card ↥((Subgroup.center ↥Pc).map Pc.subtype) = Nat.card ↥(Subgroup.center ↥P)
      rw [Subgroup.card_map_of_injective Pc.subtype_injective]
      calc Nat.card ↥(Subgroup.center ↥Pc)
          = Nat.card ↥(Subgroup.map (e : ↥Pc →* ↥P) (Subgroup.center ↥Pc)) :=
            (Subgroup.card_map_of_injective e.injective).symm
        _ = Nat.card ↥(Subgroup.center ↥P) := by rw [hcenter_map]
    rw [hcard]
    exact hodd
  have hZle : Zc ≤ CFSG.Open.standardComponentOddCore ↥C :=
    le_sSup ⟨hZnorm, hZodd⟩
  have hZbot : Zc = ⊥ :=
    le_bot_iff.mp (hZle.trans (le_of_eq (by simpa [C] using hcore t ht2)))
  have hZcbot : Subgroup.center ↥Pc = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥Pc) Pc.subtype_injective).mp
      (by simpa [Zc] using hZbot)
  have hcenter_bot : Subgroup.center ↥P = ⊥ := by
    have := congrArg (Subgroup.map (e : ↥Pc →* ↥P)) hZcbot
    simpa [hcenter_map] using this
  exact hcenter_bot


theorem false_of_simple_not_catalog (hCIT : CITPart2)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hU : Balance.UHered G)
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hncat : ¬ CFSG.Blueprint.Catalog ↥(⊤ : Subgroup G)) {P : Subgroup G} (hP : SolStd P)
    (hq : CFSG.IsQuasisimple ↥P) (hU62 : IsU62 (↥P ⧸ center ↥P))
    (hodd : Odd (Nat.card ↥(center ↥P))) : False := by
  have hfs : FStarSimple (⊤ : Subgroup G) := fStarSimple_top G hnonab
  have hcore : ∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({t} : Set G)) = ⊥ := by
    intro z hz
    by_contra hne
    have hne' : CFSG.oddCore ↥(centralizer ({z} : Set G)) ≠ ⊥ := by
      intro h
      have hEq : CFSG.Open.standardComponentOddCore ↥(centralizer ({z} : Set G)) =
          CFSG.oddCore ↥(centralizer ({z} : Set G)) := rfl
      exact hne (hEq.trans h)
    exact hncat (Balance.catalog_of_unbalanced_of_uhered hU hfs
      (by simp [Subgroup.index_top]) hkp hz hne')
  have hstd : CFSG.Open.standardComponentIsStandard P :=
    standardComponentIsStandard_of_solStd hP hq
  have hr1 : CFSG.pRank 2 ↥(centralizer (P : Set G)) ≤ 1 := by
    by_contra hr
    have hr2 : 2 ≤ CFSG.Open.pRank 2 (centralizer (P : Set G)) := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
      omega
    have hG : CFSG.Blueprint.Catalog G := by
      rcases CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.rankTwoStdRec_proved G hnonab
          hkp P hstd hr2 with ⟨n, hn, he⟩ | h | h | h | h | h
      · exact Or.inr (Or.inl ⟨n, by omega, he⟩)
      all_goals exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩)))
    exact hncat (CFSG.SectionRank.catalog_of_mulEquiv Subgroup.topEquiv hG)
  have hcyc : ∃ S : Sylow 2 (centralizer (P : Set G)),
      IsCyclic (S : Subgroup (centralizer (P : Set G))) := by
    obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer (P : Set G))) := inferInstance
    refine ⟨S, ?_⟩
    have hrS : CFSG.pRank 2 ↥(S : Subgroup ↥(centralizer (P : Set G))) ≤ 1 :=
      (Hyp.pRank_two_le_of_injective
        (S : Subgroup ↥(centralizer (P : Set G))).subtype
        (S : Subgroup ↥(centralizer (P : Set G))).subtype_injective).trans hr1
    rcases Hyp.isCyclic_or_genQuaternion_of_pRank_le_one S.isPGroup' hrS with hcy | hgq
    · exact hcy
    · exfalso
      have hnd : ¬ Nat.card ↥(⊤ : Subgroup G) ∣ 95040 := by
        intro h
        have h1 : Nat.card (↥P ⧸ center ↥P) ∣ Nat.card ↥P :=
          Subgroup.card_quotient_dvd_card _
        have h2 : Nat.card ↥P ∣ Nat.card ↥(⊤ : Subgroup G) :=
          Subgroup.card_dvd_of_le (le_top : P ≤ ⊤)
        have h3 : 9196830720 ∣ 95040 := by
          rw [isU62_card hU62] at h1
          exact h1.trans (h2.trans h)
        have hle := Nat.le_of_dvd (by norm_num : 0 < 95040) h3
        norm_num at hle
      obtain ⟨t, n, p, f, -, -, -, hm⟩ :=
        sol78Thm24_1Use_of_citPart2 hCIT G ⊤ hfs hnd P hP ⟨S, hgq⟩
      exact hncat (lieModel_catalog _ t n p f hm)
  have hset : StandardSetting G P :=
    { simple := inferInstance
      nonab := hnonab
      kProper := hkp
      standard := hstd
      core := hcore
      cyclic := hcyc }
  have hZ : center ↥P = ⊥ := center_eq_bot_of_solStd_odd hP hodd hcore
  exact UnitarySix.Child5.childU6Centerless_of_hypAut UnitarySix.YamadaHAut.hypAutInput
      UnitarySix.YamadaHAut.caseInput G P hset hZ
    (isU62_lieModel hU62)

end CFSG.EvenSporadicStandard.Induction.Fi.U62Odd
