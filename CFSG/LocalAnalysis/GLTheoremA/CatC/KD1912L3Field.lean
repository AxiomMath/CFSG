module

public import CFSG.GroupTheory.PCore.SelfCentralizing
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldSmall
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Core
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

theorem gLAPPrimeCoreOf_eq_bot_of_not_mem_linearAutGroup
    {K : Type} [Field K] [Finite K] {x : MulAut (projectiveSL 3 K)}
    (hx : x ∉ linearAutGroup 3 K) (hx3 : orderOf x = 3) :
    GLAPPrimeCoreOf 3 (innerAut (projectiveSL 3 K) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (projectiveSL 3 K)))) = ⊥ := by
  classical
  have hxpow : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx3] at h
  obtain ⟨σ, -, H, hxH⟩ := linear_order_three_field_descent (K := K) (n := 3)
    (by norm_num) x hxpow hx
  set c : MulAut (projectiveSL 3 K) := conjAut 3 K H with hc
  set f : MulAut (projectiveSL 3 K) := fieldAut 3 K σ with hf
  have hgx : c⁻¹ * x * c = f := by
    rw [hxH]
    group
  haveI : (innerAut (projectiveSL 3 K)).Normal := ys03_innerAut_normal _
  have hZ : Subgroup.center (projectiveSL 3 K) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := K) (by norm_num)
  have hcoreF : GLAPPrimeCoreOf 3 (innerAut (projectiveSL 3 K) ⊓
      Subgroup.centralizer ({f} : Set (MulAut (projectiveSL 3 K)))) = ⊥ := by
    have hdata : L3BFixData f := by rw [hf]; exact l3bf_fixData_psl (F := K) σ
    have hfix : GLAPPrimeCoreOf 3 (l3bFix f) = ⊥ := by
      have hTn : ((⁅l3bFix f, l3bFix f⁆).subgroupOf (l3bFix f)).Normal := by
        rw [Subgroup.normal_subgroupOf_iff (Subgroup.commutator_le_self (l3bFix f))]
        intro t ht d hd
        have hCmap : (l3bFix f).map (MulAut.conj ht) = l3bFix f :=
          (Subgroup.mem_normalizer_iff_map_conj_eq).1 (Subgroup.le_normalizer hd)
        have hmap : (⁅l3bFix f, l3bFix f⁆).map (MulAut.conj ht) =
            ⁅l3bFix f, l3bFix f⁆ := by
          rw [Subgroup.map_commutator, hCmap]
        have ht' : (MulAut.conj ht) t ∈ (⁅l3bFix f, l3bFix f⁆).map (MulAut.conj ht) :=
          Subgroup.mem_map_of_mem _ d
        rw [hmap] at ht'
        simpa [MulAut.conj_apply] using ht'
      refine CFSG.gLAPPrimeCoreOf_eq_bot_of_normal_simple_of_pow_mem Nat.prime_three
        (T := ⁅l3bFix f, l3bFix f⁆) (X := l3bFix f)
        (Subgroup.commutator_le_self _) hTn hdata.simple hdata.three_dvd ?_
      intro x hx
      exact ⟨1, by simpa using hdata.cube x hx⟩
    have hfixEq : l3bFix f =
        (f : projectiveSL 3 K →* projectiveSL 3 K).eqLocus (MonoidHom.id _) := rfl
    have hbridge : innerAut (projectiveSL 3 K) ⊓
        Subgroup.centralizer ({f} : Set (MulAut (projectiveSL 3 K))) =
        (l3bFix f).map (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) := by
      rw [CFSG.innerAut_inf_centralizer_eq_map_eqLocus hZ, hfixEq]
    have hcard := CFSG.card_gLAPPrimeCoreOf_map_of_injective 3
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K))
      (CFSG.mulAutConj_injective_of_center_eq_bot hZ) (l3bFix f)
    rw [← hbridge, hfix, Subgroup.card_bot] at hcard
    exact Subgroup.eq_bot_of_card_eq _ hcard
  obtain ⟨e⟩ := CFSG.gLAPPrimeCoreOf_inf_centralizer_conj 3
    (innerAut (projectiveSL 3 K)) c⁻¹ x
  have hgx' : c⁻¹ * x * c⁻¹⁻¹ = f := by simpa using hgx
  rw [hgx'] at e
  have hcard : Nat.card (GLAPPrimeCoreOf 3 (innerAut (projectiveSL 3 K) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (projectiveSL 3 K))))) = 1 := by
    calc Nat.card (GLAPPrimeCoreOf 3 (innerAut (projectiveSL 3 K) ⊓
          Subgroup.centralizer ({x} : Set (MulAut (projectiveSL 3 K)))))
        = Nat.card (GLAPPrimeCoreOf 3 (innerAut (projectiveSL 3 K) ⊓
            Subgroup.centralizer ({f} : Set (MulAut (projectiveSL 3 K))))) :=
          (Nat.card_congr e.toEquiv).symm
      _ = 1 := by rw [hcoreF, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq _ hcard

theorem gLAPPrimeCoreOf_eq_bot_of_not_mem_psuConj_range
    {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K) (hn1 : 1 < n)
    {x : MulAut (unitaryPSU h 3)} (hx : x ∉ (psuConj h).range) (hx3 : orderOf x = 3) :
    GLAPPrimeCoreOf 3 (innerAut (unitaryPSU h 3) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (unitaryPSU h 3)))) = ⊥ := by
  classical
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (unitaryPSU h 3) := inferInstance
  have hq2 : 2 < 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hn1
  have hxpow : x ^ 3 = 1 := by
    have h' := pow_orderOf_eq_one x
    rwa [hx3] at h'
  obtain ⟨σ, hσ3, H, hxH⟩ := unitary_order_three_field_descent hq2 x hxpow hx
  set c : MulAut (unitaryPSU h 3) := psuConj h H with hc
  set f : MulAut (unitaryPSU h 3) := psuField h σ with hf
  have hgx : c⁻¹ * x * c = f := by
    rw [hxH]
    group
  haveI : (innerAut (unitaryPSU h 3)).Normal := ys03_innerAut_normal _
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ :=
    center_unitaryPSU_three_eq_bot h hq2
  have hcoreF : GLAPPrimeCoreOf 3 (innerAut (unitaryPSU h 3) ⊓
      Subgroup.centralizer ({f} : Set (MulAut (unitaryPSU h 3)))) = ⊥ := by
    obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ3
    have h₀ : UnitaryFieldData 2 f₀ (CFSG.GH74.GLS.IVK.fixedField σ) :=
      ⟨Nat.prime_two, hf₀, hcard⟩
    have hfix : GLAPPrimeCoreOf 3 (l3bFix f) = ⊥ := by
      by_cases hq0 : 2 ^ f₀ = 2
      · have hf1 : f₀ = 1 := by
          have h2 : 2 ^ f₀ = 2 ^ 1 := by simpa using hq0
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
        subst hf1
        have hn3 : n = 3 := by omega
        subst hn3
        rw [GLAPPrimeCoreOf, l3bUfix_core_small h hσ3 rfl h₀, Subgroup.map_bot]
      · have hdata : L3BFixData f := l3bf_fixData_psu h hf h₀ hq0
        have hTn : ((⁅l3bFix f, l3bFix f⁆).subgroupOf (l3bFix f)).Normal := by
          rw [Subgroup.normal_subgroupOf_iff (Subgroup.commutator_le_self (l3bFix f))]
          intro t ht d hd
          have hCmap : (l3bFix f).map (MulAut.conj ht) = l3bFix f :=
            (Subgroup.mem_normalizer_iff_map_conj_eq).1 (Subgroup.le_normalizer hd)
          have hmap : (⁅l3bFix f, l3bFix f⁆).map (MulAut.conj ht) =
              ⁅l3bFix f, l3bFix f⁆ := by
            rw [Subgroup.map_commutator, hCmap]
          have ht' : (MulAut.conj ht) t ∈ (⁅l3bFix f, l3bFix f⁆).map (MulAut.conj ht) :=
            Subgroup.mem_map_of_mem _ d
          rw [hmap] at ht'
          simpa [MulAut.conj_apply] using ht'
        refine CFSG.gLAPPrimeCoreOf_eq_bot_of_normal_simple_of_pow_mem Nat.prime_three
          (T := ⁅l3bFix f, l3bFix f⁆) (X := l3bFix f)
          (Subgroup.commutator_le_self _) hTn hdata.simple hdata.three_dvd ?_
        intro x hx
        exact ⟨1, by simpa using hdata.cube x hx⟩
    have hfixEq : l3bFix f =
        (f : unitaryPSU h 3 →* unitaryPSU h 3).eqLocus (MonoidHom.id _) := rfl
    have hbridge : innerAut (unitaryPSU h 3) ⊓
        Subgroup.centralizer ({f} : Set (MulAut (unitaryPSU h 3))) =
        (l3bFix f).map (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)) := by
      rw [CFSG.innerAut_inf_centralizer_eq_map_eqLocus hZ, hfixEq]
    have hcard' := CFSG.card_gLAPPrimeCoreOf_map_of_injective 3
      (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3))
      (CFSG.mulAutConj_injective_of_center_eq_bot hZ) (l3bFix f)
    rw [← hbridge, hfix, Subgroup.card_bot] at hcard'
    exact Subgroup.eq_bot_of_card_eq _ hcard'
  obtain ⟨e⟩ := CFSG.gLAPPrimeCoreOf_inf_centralizer_conj 3
    (innerAut (unitaryPSU h 3)) c⁻¹ x
  have hgx' : c⁻¹ * x * c⁻¹⁻¹ = f := by simpa using hgx
  rw [hgx'] at e
  have hcard : Nat.card (GLAPPrimeCoreOf 3 (innerAut (unitaryPSU h 3) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (unitaryPSU h 3))))) = 1 := by
    calc Nat.card (GLAPPrimeCoreOf 3 (innerAut (unitaryPSU h 3) ⊓
          Subgroup.centralizer ({x} : Set (MulAut (unitaryPSU h 3)))))
        = Nat.card (GLAPPrimeCoreOf 3 (innerAut (unitaryPSU h 3) ⊓
            Subgroup.centralizer ({f} : Set (MulAut (unitaryPSU h 3))))) :=
          (Nat.card_congr e.toEquiv).symm
      _ = 1 := by rw [hcoreF, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq _ hcard

end CFSG.LocalAnalysis.GLTheoremA.KD1912
