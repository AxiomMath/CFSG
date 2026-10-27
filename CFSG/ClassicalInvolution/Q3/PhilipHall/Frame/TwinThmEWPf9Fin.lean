module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189b
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf4CentStand
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf4Six
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf8Four
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWRestrict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Fin4

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

theorem MinCexQ8.e18_5 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCexQ8 Ω K S R W H)
    (hT4 : Thm4RTwinBelow 3 (Nat.card G)) : (⨆ J ∈ Ω, J) = ⊤ := by
  by_contra hX
  set Y : Subgroup G := ⨆ J ∈ Ω, J with hYdef
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hEA : EtaAbelian Ω := etaAbelian_of_gen hΩ
  have hEM : EtaMeet Ω := etaMeet_of_gen hΩ
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hK : K ∈ Ω := c.stand.mem
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hKY : K ≤ Y := le_iSup₂_of_le K hK le_rfl
  have hK'Y : K' ≤ Y := le_iSup₂_of_le K' hK'Ω le_rfl
  have hnorm : Y.Normal := omegaGen_normal hΩ.conjInvariant
  have hYtop : Y ≠ ⊤ := hX
  have hRY : R ≤ Y := hRK.trans hKY
  have hR'Y : R' ≤ Y := hR'K'.trans hK'Y
  have hSY : IsSylow2In ((S : Subgroup G) ⊓ Y) Y := by
    refine isSylow2In_inf_of_le_normalizer ?_ le_top ?_
    · exact ⟨le_top, S.isPGroup', fun V' _ hV'2 hSV' => (S.is_maximal' hV'2 hSV')⟩
    · intro x _
      exact mem_normalizer_iff_conjSub_eq.mpr (AscQuot.conjSub_eq_of_normal _ x)
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK
  have hR'syl : IsSylow2In R' K' := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hR' hR'K'
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3Q8 G Ω K S R W H c) c.stand.aEmpty
  have hNH : oddCoreOf Y ≤ H :=
    c.oddCoreOf_le hEA hEM hK'tw hK'ne hR' hR'K' hR'S (sup_le hRY hR'Y)
  have hΛ : HypOmegaGen (restrictFamily Ω Y) := hypOmegaGen_restrict hΩ Y
  have hgen : Y ≤ ⨆ L ∈ restrictFamily Ω Y, L.map Y.subtype := by
    refine iSup₂_le fun J hJ => ?_
    have hJY : J ≤ Y := le_iSup₂_of_le J hJ le_rfl
    refine le_iSup₂_of_le (J.subgroupOf Y) (subgroupOf_mem_restrictFamily hJ hJY) ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJY]
  have hYH : Y ≤ H :=
    c.section_le_H hT4 hYtop hΛ (classicalClause_restrict c.stand.cls Y)
      (q8_restrict c.stand.q8 Y) (two_restrict c.stand.two Y) (AscQuot.sylowOfIsSylow2In' hSY)
      (subgroupOf_mem_restrictFamily hK hKY) (twinSet_subgroupOf hKY hK'Y hK'tw)
      (subgroupOf_ne_of_ne hKY hK'Y hK'ne)
      (mem_RSet_restrict hK hKY hRsyl) (Subgroup.subgroupOf_mono _ hRK)
      (Subgroup.subgroupOf_mono _ (le_inf hRS hRY))
      (mem_RSet_restrict hK'Ω hK'Y hR'syl) (Subgroup.subgroupOf_mono _ hR'K')
      (Subgroup.subgroupOf_mono _ (le_inf hR'S hR'Y)) hNH hgen (c.trans_restrict hKY)
      (exists_W_restrict hΩ c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2 c.hyp.cent
        (S₁ := AscQuot.sylowOfIsSylow2In' hSY)
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := hx
          exact (Subgroup.mem_subgroupOf.mp hy).1)) (restrictGood Ω Y K) ⟨K, hK, hKY, rfl, Relation.ReflTransGen.refl⟩
      (fun L _ L' hL' hg hadj => restrictGood_step hL' hg hadj)
      (fun L _ hg => c.restrictGood_le_H hg)
      (fun _ L hL => by
        obtain ⟨J, hJ, hJY, rfl⟩ := hL
        exact AEmpty.restrict hΩ hJY (hAΩ J hJ))
  obtain ⟨u, huR, hu4⟩ := exists_orderOf_eq_four_of_mem_RSet_gen hΩ hRR
  refine c.proper (eq_top_iff.mpr fun g _ => ?_)
  have hle : conjSub g K ≤ Y :=
    le_iSup₂_of_le (conjSub g K) (hΩ.conjInvariant g K hK) le_rfl
  exact e18_2Q8 G Ω K S R W H c u (hRK huR) hu4 g (hYH (hle (conj_mem_conjSub (hRK huR))))

@[expose] def T4Supply : Prop :=
  ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n

theorem MinCexQ8.t4 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCexQ8 Ω K S R W H) (hT : T4Supply) :
    Thm4RTwinBelow 3 (Nat.card G) :=
  hT _ c.stand.ih.1 c.stand.ih.2

theorem e18_5Q8_of_supply (hT : T4Supply) : E18_5Q8 :=
  fun G _ _ Ω K S R W H c => c.e18_5 (c.t4 hT)

theorem e18_4CQ8_of_supply (hT : T4Supply) : E18_4CQ8 :=
  fun G _ _ Ω K S R W H c K' hK' hne R' hR' hR'K' h2 w hw1 hw2 hRw hw =>
    c.e18_4C (c.t4 hT) hK' hne hR' hR'K' h2 hw1 hw2 hRw hw

theorem e18_6Q8_of_5 (h5 : E18_5Q8) (hO2 : E18_6O2Q8) : E18_6Q8 := by
  intro G _ _ Ω K S R W H c
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hO : classicalInvolutionOddCore G = ⊥ := c.oddCore_eq_bot
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := h5 G Ω K S R W H c
  have htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3Q8 G Ω K S R W H c
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant htrans c.stand.aEmpty
  have hZ2 : IsPGroup 2 ↥(Subgroup.center G) := center_isPGroup_two hO
  have hZH : Subgroup.center G ≤ H := by
    obtain ⟨z', -, hcz'⟩ := c.exists_centralizer_le
    intro x hx
    apply hcz'
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hx z').symm
  have hZbot : Subgroup.center G = ⊥ :=
    c.eq_bot_of_central le_rfl hZ2 hZH
      (fun J hJ => (hO2 G Ω K S R W H c _ inferInstance hZ2).2 J hJ)
  have h2triv : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → Q = ⊥ := by
    intro Q hQn hQ2
    have := (hO2 G Ω K S R W H c Q hQn hQ2).1
    rw [hZbot] at this
    exact le_bot_iff.mp this
  have hsolv := AscThmA.solvable_normal_eq_bot_of_oddCore hO h2triv
  exact ⟨hO, lemma17_3Q8 G Ω hΩ c.stand.cls c.stand.q8 c.stand.two hAΩ c.stand.ih hO hsolv hgen K
    c.stand.mem htrans⟩

theorem e18_6Q8_of_supply (hT : T4Supply) (hO2 : E18_6O2Q8) : E18_6Q8 :=
  e18_6Q8_of_5 (e18_5Q8_of_supply hT) hO2

end Fin4

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
