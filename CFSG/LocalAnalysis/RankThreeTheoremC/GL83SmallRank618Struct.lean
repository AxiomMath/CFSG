module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Comp
import CFSG.Adapters.GeneralizedFitting
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.RankThree.PartOne.D4RC.Burnside
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.Quasithin.Background.Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {Y : Type} [Group Y] [Finite Y] {B Z Y₀ : Subgroup Y}

private theorem s618_eq_of_le_of_card_three {H K : Subgroup Y} (hHK : H ≤ K) (hH : H ≠ ⊥)
    (hK : Nat.card K = 3) : H = K := by
  have hdvd : Nat.card H ∣ 3 := hK ▸ Subgroup.card_dvd_of_le hHK
  have h1 : Nat.card H ≠ 1 := fun h => hH (Subgroup.card_eq_one.mp h)
  have h3 : Nat.card H = 3 := ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left h1
  exact Subgroup.eq_of_le_of_card_ge hHK (by omega)

private theorem s618_ne_bot_of_card_three {G : Type*} [Group G] {H : Subgroup G}
    (hH : Nat.card H = 3) : H ≠ ⊥ := by
  intro h
  rw [h, Subgroup.card_bot] at hH
  omega

private theorem s618_mul_comm (d : Data618 B Z Y₀) {x y : Y} (hx : x ∈ B) (hy : y ∈ B) :
    x * y = y * x := by
  have := d.elem.1
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩)

private theorem s618_commutator_eq {G : Type*} [Group G] {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) : ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hL.2.2.1)

private theorem s618_ne_bot {G : Type*} [Group G] {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) : L ≠ ⊥ :=
  haveI := ((CFSG.Adapters.isComponentOf_top_iff L).mp hL).2.2.1
  (Subgroup.nontrivial_iff_ne_bot L).mp this

private theorem s618_eq_one_of_mem_centralizer {G : Type*} [Group G] {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hs : IsSimpleGroup ↥L) {l : G} (hl : l ∈ L)
    (hlc : l ∈ centralizer (L : Set G)) : l = 1 := by
  have hc : (⟨l, hl⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hlc) g g.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
  · rw [h, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  · have := hL.2.2.2
    exact absurd (QuotientGroup.subsingleton_iff.mpr h) (not_subsingleton _)

private theorem s618_le_centralizer_of_ne {L L' : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hL' : CFSG.Open.IsComponentOf L' ⊤) (hne : L' ≠ L) :
    L' ≤ centralizer (L : Set Y) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.GorensteinWalter.component_commute_of_ne
      ((CFSG.Adapters.isComponentOf_top_iff L').mp hL')
      ((CFSG.Adapters.isComponentOf_top_iff L).mp hL) hne)

private theorem s618_component_eq (hKF1 : KFactSylowNormalizerIrreducible)
    (d : Data618 B Z Y₀) {L L' : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤)
    (hL' : CFSG.Open.IsComponentOf L' ⊤) (hZL : Z ≤ L) (hZL' : Z ≤ L') : L' = L := by
  by_contra hne
  have hc := s618_le_centralizer_of_ne hL hL' hne
  have hs := (component_simple_card hKF1 d hL).1
  apply s618_ne_bot_of_card_three d.card_Z
  rw [eq_bot_iff]
  intro z hz
  exact (Subgroup.mem_bot).mpr (s618_eq_one_of_mem_centralizer hL hs (hZL hz) (hc (hZL' hz)))

private theorem s618_isPGroup_B (d : Data618 B Z Y₀) : IsPGroup 3 B :=
  IsPGroup.of_card (n := 2) (by rw [d.card_B]; norm_num)

theorem eq_component_inf_or_centralizer (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (d : Data618 B Z Y₀) {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) :
    Z = L ⊓ B ∨ Z = B ⊓ centralizer (L : Set Y) := by
  obtain ⟨-, hcard, hidx⟩ := component_simple_card hKF1 d hL
  obtain ⟨-, C, hCdef, hCcard, -, hsup⟩ := component_split hKF1 hKF2 d hL
  rw [← hCdef]
  have hℓp : IsPGroup 3 ↥(L ⊓ B) := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  have hℓc : IsCyclic ↥(L ⊓ B) := isCyclic_of_prime_card hcard
  obtain ⟨t, htL, htℓ, a, haℓ, -, hta⟩ := CFSG.RankThree.PartOne.D4RC.rcb_exists_normalizer_elt
    (p := 3) (by norm_num) (s618_commutator_eq hL) inf_le_left hℓp hidx hℓc
    (s618_ne_bot_of_card_three hcard)
  have hCL : C ≤ centralizer (L : Set Y) := hCdef ▸ inf_le_right
  have htC : t ∈ centralizer (C : Set Y) :=
    Subgroup.mem_centralizer_iff.mpr fun c hc =>
      ((Subgroup.mem_centralizer_iff.mp (hCL hc)) t htL).symm
  have htB : t ∈ normalizer (B : Set Y) := by
    rw [← hsup]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨htℓ, Subgroup.centralizer_le_normalizer _ htC⟩
  have htZ : t ∈ normalizer (Z : Set Y) := d.fix_Z htB
  by_cases hZℓ : Z ⊓ (L ⊓ B) = ⊥
  · right
    refine s618_eq_of_le_of_card_three ?_ (s618_ne_bot_of_card_three d.card_Z) hCcard
    intro z hz
    have hzB : z ∈ (L ⊓ B) ⊔ C := hsup.symm ▸ d.le_B hz
    have hCℓ : C ≤ centralizer ((L ⊓ B : Subgroup Y) : Set Y) :=
      hCL.trans (Subgroup.centralizer_le fun x hx => (Subgroup.mem_inf.mp hx).1)
    obtain ⟨u, hu, v, hv, rfl⟩ := CFSG.GorensteinWalter.mem_sup_decompose_of_centralizes hzB hCℓ
    have hvt : Commute v t := ((Subgroup.mem_centralizer_iff.mp (hCL hv)) t htL).symm
    have hcomm : t * (u * v) * t⁻¹ * (u * v)⁻¹ = t * u * t⁻¹ * u⁻¹ := by
      calc t * (u * v) * t⁻¹ * (u * v)⁻¹ = t * u * (v * t⁻¹) * v⁻¹ * u⁻¹ := by group
        _ = t * u * (t⁻¹ * v) * v⁻¹ * u⁻¹ := by rw [hvt.inv_right.eq]
        _ = t * u * t⁻¹ * u⁻¹ := by group
    have hmemZ : t * (u * v) * t⁻¹ * (u * v)⁻¹ ∈ Z :=
      Z.mul_mem ((Subgroup.mem_normalizer_iff.mp htZ _).mp hz) (Z.inv_mem hz)
    have hmemℓ : t * u * t⁻¹ * u⁻¹ ∈ L ⊓ B :=
      (L ⊓ B).mul_mem ((Subgroup.mem_normalizer_iff.mp htℓ _).mp hu) ((L ⊓ B).inv_mem hu)
    have h1 : t * u * t⁻¹ * u⁻¹ = 1 := by
      have hmem : t * u * t⁻¹ * u⁻¹ ∈ Z ⊓ (L ⊓ B) := ⟨hcomm ▸ hmemZ, hmemℓ⟩
      rw [hZℓ] at hmem
      exact (Subgroup.mem_bot).mp hmem
    have htu : t * u * t⁻¹ = u := mul_inv_eq_one.mp h1
    by_cases hu1 : u = 1
    · subst hu1
      simpa using hv
    · exfalso
      have hzp : zpowers u = L ⊓ B := s618_eq_of_le_of_card_three
        (Subgroup.zpowers_le.mpr hu) (fun h => hu1 (Subgroup.zpowers_eq_bot.mp h)) hcard
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ haℓ)
      apply hta
      rw [← conj_zpow, htu]
  · left
    have h1 := s618_eq_of_le_of_card_three inf_le_left hZℓ d.card_Z
    have h2 := s618_eq_of_le_of_card_three inf_le_right hZℓ hcard
    exact h1.symm.trans h2

set_option linter.unusedVariables false in
theorem exists_component_ge_of_eq_centralizer (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (d : Data618 B Z Y₀) {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hZ : Z = B ⊓ centralizer (L : Set Y)) :
    ∃ L' : Subgroup Y, CFSG.Open.IsComponentOf L' ⊤ ∧ Z ≤ L' := by
  by_contra hno
  have hs := (component_simple_card hKF1 d hL).1
  have hall : ∀ L' : Subgroup Y, CFSG.Open.IsComponentOf L' ⊤ → L' = L := by
    intro L' hL'
    by_contra hne
    apply hno
    refine ⟨L', hL', ?_⟩
    have hc := s618_le_centralizer_of_ne hL hL' hne
    have hle : L' ⊓ B ≤ Z := by
      rw [hZ]
      exact le_inf inf_le_right (inf_le_left.trans hc)
    have hcard' := (component_simple_card hKF1 d hL').2.1
    have heq := s618_eq_of_le_of_card_three hle (s618_ne_bot_of_card_three hcard') d.card_Z
    exact heq ▸ inf_le_left
  have hE : genFittingLayer Y ≤ L := sSup_le fun L' hL' => (hall L' hL').le
  have hcore : CFSG.pPrimeCore 3 Y = ⊥ := sSup_eq_bot.mpr fun N hN => d.core N hN.1 hN.2
  have hFB : genFittingFitting Y ≤ B := by
    have h := CFSG.fitting_pCore_le_sylow ((s618_isPGroup_B d).toSylow d.sylow)
    rw [← CFSG.Fitting_eq_pcore Y 3 hcore] at h
    exact h
  have hLF : L ≤ centralizer (genFittingFitting Y : Set Y) := by
    rcases CFSG.GorensteinWalter.component_le_or_commutator_eq_bot_of_normal
      ((CFSG.Adapters.isComponentOf_top_iff L).mp hL)
      (CFSG.fittingSubgroup_normal : (CFSG.fittingSubgroup Y).Normal) with h | h
    · exfalso
      apply s618_ne_bot hL
      have hLB : L ≤ B := h.trans hFB
      rw [eq_bot_iff, ← s618_commutator_eq hL, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => s618_mul_comm d (hLB hy) (hLB hx)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hFL : genFittingFitting Y ≤ centralizer (L : Set Y) := Subgroup.le_centralizer_iff.mp hLF
  have hZF : Z ≤ genFittingFitting Y := by
    intro z hz
    have hzL : z ∈ centralizer (L : Set Y) := by
      rw [hZ] at hz
      exact hz.2
    have hzF : z ∈ centralizer (genFittingFitting Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun f hf => s618_mul_comm d (hFB hf) (d.le_B hz)
    have hzE : z ∈ centralizer (genFittingLayer Y : Set Y) :=
      Subgroup.centralizer_le (fun x hx => hE hx) hzL
    have hzstar : z ∈ genFittingFStar Y :=
      CFSG.Adapters.generalized_fitting_self_centralizing Y
        (CFSG.GorensteinWalter.fstar_centralizer_of_centralizes_join hzF hzE)
    have hzFL : z ∈ genFittingFitting Y ⊔ L := (sup_le_sup_left hE _) hzstar
    obtain ⟨f, hf, l, hl, rfl⟩ := CFSG.GorensteinWalter.mem_sup_decompose_of_centralizes hzFL hLF
    have hlc : l ∈ centralizer (L : Set Y) := by
      have hmem : f⁻¹ * (f * l) ∈ centralizer (L : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hFL hf)) hzL
      simpa using hmem
    rw [s618_eq_one_of_mem_centralizer hL hs hl hlc, mul_one]
    exact hf
  have hFZ : genFittingFitting Y ≤ Z := by
    rw [hZ]
    exact le_inf hFB hFL
  have hZn : Z.Normal := by
    rw [le_antisymm hZF hFZ]
    exact (CFSG.fittingSubgroup_normal : (CFSG.fittingSubgroup Y).Normal)
  exact d.proper (top_le_iff.mp ((normalizer_eq_top_iff.mpr hZn).symm.le.trans d.cover))

theorem exists_component_ge (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (d : Data618 B Z Y₀) :
    ∃ L : Subgroup Y, CFSG.Open.IsComponentOf L ⊤ ∧ Z ≤ L := by
  obtain ⟨L, hL⟩ := exists_isComponentOf_top d
  rcases eq_component_inf_or_centralizer hKF1 hKF2 d hL with h | h
  · exact ⟨L, hL, h.le.trans inf_le_left⟩
  · exact exists_component_ge_of_eq_centralizer hKF1 hKF2 d hL h

set_option linter.unusedVariables false in
theorem component_ge_normal (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (d : Data618 B Z Y₀) {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hZL : Z ≤ L) : L.Normal := by
  let E : Subgroup Y := CFSG.GorensteinWalter.componentLayerOf ⊤
  have hEn : E.Normal :=
    ⟨fun n hn g => (CFSG.GorensteinWalter.componentLayerOf_isNormalIn ⊤).2 g trivial n hn⟩
  have hLE : L ≤ E := le_sSup ((CFSG.Adapters.isComponentOf_top_iff L).mp hL)
  have hEN : E ≤ normalizer (L : Set Y) := by
    refine sSup_le fun L' hL' => ?_
    have hL'o := (CFSG.Adapters.isComponentOf_top_iff L').mpr hL'
    by_cases hne : L' = L
    · rw [hne]
      exact le_normalizer
    · exact (s618_le_centralizer_of_ne hL hL'o hne).trans (Subgroup.centralizer_le_normalizer _)
  have hZN : normalizer (Z : Set Y) ≤ normalizer (L : Set Y) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hc : CFSG.Open.IsComponentOf (Subgroup.conjBy L n) ⊤ :=
      (CFSG.Adapters.isComponentOf_top_iff _).mpr
        (CFSG.GorensteinWalter.fstar_isComponentOf_conjugateSubgroup_of_mem
          ((CFSG.Adapters.isComponentOf_top_iff L).mp hL) n trivial)
    have hZc : Z ≤ Subgroup.conjBy L n := by
      have hZn := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
      rw [← hZn]
      exact Subgroup.map_mono hZL
    exact s618_component_eq hKF1 d hL hc hZL hZc
  have hSylB : CFSG.ABGLocalTools.IsSylowOf 3 B ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨le_top, s618_isPGroup_B d, by rw [Subgroup.relIndex_top_right]; exact d.sylow⟩
  obtain ⟨P, hP⟩ := hSylB.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr hEn).ge
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hP] at hfr
  have hZQ : Z ≤ B ⊓ E := le_inf d.le_B (hZL.trans hLE)
  have hQ : normalizer ((B ⊓ E : Subgroup Y) : Set Y) ≤ normalizer (Z : Set Y) := by
    obtain ⟨c, hc⟩ : ∃ c, Nat.card ↥(B ⊓ E) = c := ⟨_, rfl⟩
    have h9 : c ∣ 9 := hc ▸ d.card_B ▸ Subgroup.card_dvd_of_le inf_le_left
    have h3 : 3 ∣ c := hc ▸ d.card_Z ▸ Subgroup.card_dvd_of_le hZQ
    have hc' : c = 3 ∨ c = 9 := by
      have := Nat.le_of_dvd (by norm_num) h9
      interval_cases c <;> omega
    rcases hc' with h | h
    · rw [← s618_eq_of_le_of_card_three hZQ (s618_ne_bot_of_card_three d.card_Z) (hc.trans h)]
    · have hBE : B ⊓ E = B :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [d.card_B, hc, h])
      rw [hBE]
      exact d.fix_Z
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hfr]
  exact sup_le (hQ.trans hZN) hEN

theorem not_le_of_component_ge (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (d : Data618 B Z Y₀) {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hZL : Z ≤ L) : ¬ L ≤ Y₀ := by
  intro hLY
  have := component_ge_normal hKF1 hKF2 d hL hZL
  obtain ⟨-, hcard, hidx⟩ := component_simple_card hKF1 d hL
  have hZeq : Z = L ⊓ B :=
    s618_eq_of_le_of_card_three (le_inf hZL d.le_B) (s618_ne_bot_of_card_three d.card_Z) hcard
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [d.card_Z, pow_one])
  have hSylZ : CFSG.ABGLocalTools.IsSylowOf 3 Z L :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hZL, hZp, by rw [hZeq]; exact hidx⟩
  obtain ⟨P, hP⟩ := hSylZ
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hP] at hfr
  apply d.proper
  rw [eq_top_iff, ← hfr]
  exact sup_le d.cover hLY

theorem exists_normal_component (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (d : Data618 B Z Y₀) :
    ∃ L : Subgroup Y, L.Normal ∧ CFSG.Open.IsComponentOf L ⊤ ∧ IsSimpleGroup ↥L ∧
      Nat.card (L ⊓ B : Subgroup Y) = 3 ∧ ¬ 3 ∣ (L ⊓ B).relIndex L ∧ Z ≤ L ∧ ¬ L ≤ Y₀ ∧
      ∃ b ∈ B, b ∉ Z ∧ ∀ l ∈ L, b * l = l * b := by
  obtain ⟨L, hL, hZL⟩ := exists_component_ge hKF1 hKF2 d
  obtain ⟨hs, hcard, hidx⟩ := component_simple_card hKF1 d hL
  obtain ⟨-, C, hCdef, hCcard, hdisj, -⟩ := component_split hKF1 hKF2 d hL
  obtain ⟨b, hbC, hb1⟩ := (Subgroup.bot_or_exists_ne_one C).resolve_left
    (s618_ne_bot_of_card_three hCcard)
  have hbC' : b ∈ B ⊓ centralizer (L : Set Y) := hCdef ▸ hbC
  have hbZ : b ∉ Z := by
    intro hbZ
    apply hb1
    have hmem : b ∈ (L ⊓ B) ⊓ C := ⟨⟨hZL hbZ, d.le_B hbZ⟩, hbC⟩
    rw [hdisj] at hmem
    exact (Subgroup.mem_bot).mp hmem
  refine ⟨L, component_ge_normal hKF1 hKF2 d hL hZL, hL, hs, hcard, hidx, hZL,
    not_le_of_component_ge hKF1 hKF2 d hL hZL, b, hbC'.1, hbZ, fun l hl => ?_⟩
  exact ((Subgroup.mem_centralizer_iff.mp hbC'.2) l hl).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
