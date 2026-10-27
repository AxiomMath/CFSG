module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalSpCent
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4F1
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutSp
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutSp
public import CFSG.HardMathSupport.Dickson.Bal207.Rank
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4E

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Dickson.Bal207
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem odd_core_outer_sp4_eight {x : MulAut (StatedProj (StatedSp 2 F8))} (hx : orderOf x = 3)
    (hxout : x ∉ innerAut (StatedProj (StatedSp 2 F8))) :
    Odd (Nat.card (GLAPPrimeCoreOf 3
      (innerAut (StatedProj (StatedSp 2 F8)) ⊓
        Subgroup.centralizer ({x} : Set (MulAut (StatedProj (StatedSp 2 F8))))))) := by
  have hZ : Subgroup.center (StatedProj (StatedSp 2 F8)) = ⊥ :=
    CFSG.QuasithinUnique.Lin2.Five.center_statedProj_eq_bot (F := F8)
  have hxinj := mulAutConj_injective_of_center_eq_bot hZ
  obtain ⟨γ, σ, hσ, hxeq⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.psp_field_descent (r := 2) (by norm_num)
      (K := F8) (p := 2) (f := 3) Nat.prime_two (by norm_num) (by rw [card_F8]; norm_num)
      (by simpa only [hx] using pow_orderOf_eq_one x) hxout
  obtain ⟨-, -, -, -, -, hmem, -, -, hS6, -⟩ :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.symplectic_prime_subfield_fixed_group_and_full_centralizer_odd
      (K := F8) (ℓ := 2) (p := 3) (f := 3) (r := 2) Nat.prime_two Nat.prime_three
      (by norm_num) (by norm_num) (by norm_num) le_rfl (by rw [card_F8]; norm_num) σ hσ
  obtain ⟨⟨e6⟩, -, -⟩ := hS6 ⟨rfl, by norm_num⟩
  set H₀ : Subgroup (StatedProj (StatedSp 2 F8)) :=
    CFSG.RankThree.CASymplecticSubfield.subfieldFixedGroup F8 2 σ with hH₀
  have hfixσ : fixSubgroup (fieldAut 2 F8 σ) = H₀ := by
    ext z
    rw [mem_fixSubgroup]
    exact (hmem z).symm
  have hfix : fixSubgroup x = H₀.map
      (γ : StatedProj (StatedSp 2 F8) →* StatedProj (StatedSp 2 F8)) := by
    rw [hxeq]
    rw [show fixSubgroup (γ * fieldAut 2 F8 σ * γ⁻¹) =
        fixSubgroup (MulAut.congr (γ : StatedProj (StatedSp 2 F8) ≃*
          StatedProj (StatedSp 2 F8)) (fieldAut 2 F8 σ)) from rfl,
      CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr, hfixσ]
    rfl
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNN : NoNormalPPrime 3 (⊤ : Subgroup ↥H₀) :=
    W2.noNormalPPrime_top_of_mulEquiv e6 W2.noNormalPPrime_three_perm_six
  have hOH : GLAPPrimeCoreOf 3 H₀ = ⊥ :=
    W2.core_eq_bot_of_noNormalPPrime Nat.prime_three
      ((W2.noNormalPPrime_top_iff H₀).mp hNN)
  have hOHodd : Odd (Nat.card (GLAPPrimeCoreOf 3 H₀)) := by
    rw [hOH, Subgroup.card_bot]
    exact odd_one
  have hFix : Odd (Nat.card (GLAPPrimeCoreOf 3 (fixSubgroup x))) := by
    rw [hfix, card_gLAPPrimeCoreOf_map_of_injective 3 _ γ.injective H₀]
    exact hOHodd
  rw [innerAut_inf_centralizer_eq_map_eqLocus hZ x]
  change Odd (Nat.card (GLAPPrimeCoreOf 3
    ((fixSubgroup x).map (MulAut.conj : StatedProj (StatedSp 2 F8) →*
      MulAut (StatedProj (StatedSp 2 F8))))))
  rw [card_gLAPPrimeCoreOf_map_of_injective 3 _ hxinj (fixSubgroup x)]
  exact hFix

theorem oddCoreFact_three_statedProj_eight :
    OddCoreFact 3 (StatedProj (StatedSp 2 F8)) := by
  constructor
  · exact CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer
      (CFSG.Quasithin.H13.OutTwoNilp.twoNilpotent_outer_symplectic_two (f := 3)
        (by norm_num) (K := F8) card_F8)
  · intro x hx
    have hZ : Subgroup.center (StatedProj (StatedSp 2 F8)) = ⊥ :=
      CFSG.QuasithinUnique.Lin2.Five.center_statedProj_eq_bot (F := F8)
    by_cases hin : x ∈ innerAut (StatedProj (StatedSp 2 F8))
    ·
      obtain ⟨t, ht⟩ := hin
      subst ht
      have hinj := mulAutConj_injective_of_center_eq_bot hZ
      have htord : orderOf t = 3 := by
        rw [← orderOf_injective (MulAut.conj :
          StatedProj (StatedSp 2 F8) →* MulAut (StatedProj (StatedSp 2 F8))) hinj t]
        exact hx
      rw [innerAut_inf_centralizer_conj hZ t,
        card_gLAPPrimeCoreOf_map_of_injective 3 _ hinj
          (Subgroup.centralizer ({t} : Set (StatedProj (StatedSp 2 F8))))]
      have hNN := noNormalPPrime_three_centralizer_statedProj_eight (r := 2)
        (K := F8) card_F8 (by norm_num) htord
      rw [W2.core_eq_bot_of_noNormalPPrime Nat.prime_three hNN, Subgroup.card_bot]
      exact odd_one
    · exact odd_core_outer_sp4_eight hx hin

theorem oddCoreFact_three_of_B2_eight {S : Type} [Group S] [Finite S]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) (hq : q.card = 8)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩).Group) :
    OddCoreFact 3 S := by
  obtain ⟨eB⟩ := CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E.bridge_B2 q hv hq
  have eP : S ≃* StatedProj (StatedSp 2 F8) := e.trans (eB.trans eQ.symm)
  exact (oddCoreFact_congr (p := 3) eP).mpr oddCoreFact_three_statedProj_eight

end CFSG.LocalAnalysis.GLTheoremA.KD1912
