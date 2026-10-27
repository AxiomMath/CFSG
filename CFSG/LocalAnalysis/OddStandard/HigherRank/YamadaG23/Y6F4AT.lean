module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AK
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AH
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AO
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AV
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AW
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenResidual

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Blueprint CFSG.OddStandard.HigherRank.G2Three CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem y6f4a_false_of_gData
    (hGMS : GMSLinearStandardLayerListKRankOneStatement)
    (hRes : CFSG.EvenSporadicStandard.Induction.CTEvenResidualStatement)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog) (hG : G23Facts)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, Nat.card (Carrier s) = sporOrder s)
    (hG2 : ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
      Nat.card ↥(⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 k,
        CFSG.Blueprint.Chevalley.adjointGroup .G2 k⁆ :
          Subgroup (CFSG.Blueprint.Chevalley.ModGL .G2 k)) = 6048)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper Catalog G)
    (hbal : ∀ z : G, orderOf z = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({z} : Set G)) = ⊥)
    {g t : G} {P M : Subgroup G} (hd : Y6GData g t P M) : False := by
  have hg1 : g ≠ 1 := by
    intro h
    have hg2 : orderOf g = 2 := hd.g_order
    rw [h, orderOf_one] at hg2
    exact absurd hg2 (by norm_num)
  let C : Subgroup G := centralizer ({g} : Set G)
  have hcd : Y6CData (y6f4aG g) (y6f4aT g t hd.comm) (P.subgroupOf C) (M.subgroupOf C) :=
    y6f4a_cData_of_gData hd
  have hne : centralizer ({g} : Set G) ≠ ⊤ := y6f4a_centralizer_ne_top hnonab hg1
  let Y := ↥C ⧸ zpowers (y6f4aG g)
  have hKY : CFSG.SectionRank.IsKGroupCat Y := y6f4a_isKGroupCat_Y hKP hne
  have hOY : CFSG.Open.standardComponentOddCore Y = ⊥ :=
    y6f4a_oddCore_Y hd.g_order (hbal g hd.g_order)
  obtain ⟨J, M', hY⟩ := y6f4a_yData_of_cData hSch hcd
  let E : Subgroup Y := CFSG.layer Y
  have hEchar : E.Characteristic := CFSG.LocalCores.layer_characteristic (G := Y)
  obtain ⟨hE, ⟨a, b, hab⟩, hCE, hperfE, hlie⟩ :=
    y6f4a_layer_of_data hGMS hSch hG hO hKY hOY hY
  have hna : ¬ IsMulCommutative ↥E := fun hc => hab (hc.is_comm.comm a b)
  have hElie : Y6TargetLie ↥E := hlie
  have hEperf : ∀ B : Subgroup Y, Group.IsPerfect ↥B → B ≤ E := hperfE
  let π : ↥C →* Y := QuotientGroup.mk' (zpowers (y6f4aG g))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥C := by
    change (QuotientGroup.mk' (zpowers (y6f4aG g))).ker ≤ Subgroup.center ↥C
    rw [QuotientGroup.ker_mk' (zpowers (y6f4aG g))]
    exact Subgroup.zpowers_le.mpr hcd.g_central
  let K : Subgroup ↥C := ⁅E.comap π, E.comap π⁆
  haveI hKn : K.Normal := y6f4a_lift_normal hπ (inferInstance : E.Normal)
  have hKq : CFSG.Open.IsQuasisimple ↥K := y6f4a_lift_quasisimple hπ hker hE hna
  obtain ⟨eK⟩ := y6f4a_lift_equiv hπ hker hE hna
  have hKc : centralizer (K : Set ↥C) = zpowers (y6f4aG g) := by
    have h := y6f4a_lift_centralizer hπ hker hE hna hCE
    rw [h]
    exact QuotientGroup.ker_mk' (zpowers (y6f4aG g))
  have hperfC : ∀ B : Subgroup ↥C, Group.IsPerfect ↥B → B ≤ K :=
    fun B hB => y6f4a_lift_perfect hEperf hB
  have h4E : 4 ∣ Nat.card ↥E := by
    rcases y6f4a_card_target hO hElie with h | h | h <;> rw [h] <;> norm_num
  have h4K : 4 ∣ Nat.card ↥K := by
    have h1 : 4 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
      rw [Nat.card_congr eK.toEquiv]
      exact h4E
    exact h1.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥K))
  obtain ⟨A, ⟨eQ⟩, hstd, hsyl⟩ :=
    y6f4a_standard_lift hd.g_order hKq hKc hperfC h4K
  let S : Sylow 2 ↥(centralizer (A : Set G)) := default
  have hcyc : IsCyclic (S : Subgroup ↥(centralizer (A : Set G))) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card (p := 2) (hsyl S)
  have hlieA : Y6TargetLie (↥A ⧸ Subgroup.center ↥A) :=
    Y6TargetLie.of_mulEquiv (eQ.trans eK).symm hElie
  have hres : Recognition.Exact.EvenStandardResidual ↥A :=
    hRes G hnonab hKP A hstd hbal S hcyc
      (y6f4a_evenStandardType hlieA)
      (y6f4a_not_exception hO hcard hG2 hlieA)
  exact y6f4a_not_residual hO hcard hlieA hres

end CFSG.OddStandard.HigherRank.YamadaG23
