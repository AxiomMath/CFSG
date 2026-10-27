module

public import CFSG.GH74.Uniqueness.Section7Stage2Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.Lemma311
public import CFSG.GH74.Uniqueness.Section5ZStar
public import CFSG.GH74.Uniqueness.Section6Basic
public import CFSG.GH74.Uniqueness.Section6ZJ
public import CFSG.GH74.Uniqueness.Theorem1Final
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise commutatorElement

section Generic

private theorem sevenD_nontrivial_pCore_quotient_action
    {H A : Type*} [Group H] [Finite H] [Group A] [Finite A]
    [MulDistribMulAction A H]
    (p : ℕ) [Fact p.Prime]
    (hsolv : Group.IsSolvable H)
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card H))
    (hcomm : commutatorAction (A := A) (G := H) = ⊤)
    {W : Subgroup H} (hWp : IsPGroup p W) (hWne : W ≠ ⊥) :
    let K : Subgroup H := pPrimeCore p H
    letI : IsInvariant A H K := isInvariant_of_characteristic K
    letI : MulDistribMulAction A (H ⧸ K) :=
      quotientMulDistribMulAction (A := A) (G := H) K
        (isInvariant_of_characteristic K)
    letI : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
      isInvariant_of_characteristic _
    ¬ ActsTrivially (A := A) (G := pCore p (H ⧸ K)) := by
  dsimp only
  let : Group.IsSolvable H := hsolv
  let K : Subgroup H := pPrimeCore p H
  let : IsInvariant A H K := isInvariant_of_characteristic K
  let : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K
      (isInvariant_of_characteristic K)
  let : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
    isInvariant_of_characteristic _
  intro htrivP
  have hsolvQ : Group.IsSolvable (H ⧸ K) :=
    inferInstance
  have hcoreQ : pPrimeCore p (H ⧸ K) = ⊥ := by
    simpa [K] using
      (_root_.CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := H) (p := p))
  have hfitQ : fittingSubgroup (H ⧸ K) = pCore p (H ⧸ K) :=
    Fitting_eq_pcore (H ⧸ K) p hcoreQ
  have hcoprimeQ : Nat.Coprime (Nat.card A) (Nat.card (H ⧸ K)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_quotient_dvd_card K) hcoprime
  have htrivQ : ActsTrivially (A := A) (G := H ⧸ K) := by
    intro a q
    exact section8_element_actsTrivially_of_centralizes_fitting_of_coprime
      hsolvQ hcoprimeQ a (fun f => by
        have hfP : (f : H ⧸ K) ∈ pCore p (H ⧸ K) := by
          rw [← hfitQ]
          exact f.property
        have hf := htrivP a ⟨(f : H ⧸ K), hfP⟩
        exact congrArg Subtype.val hf) q
  have hcomm_le : commutatorAction (A := A) (G := H) ≤ K := by
    rw [commutatorAction_eq_closure (G := H) (A := A)]
    refine (Subgroup.closure_le (K := K)).2 ?_
    rintro x ⟨a, g, rfl⟩
    apply (QuotientGroup.eq_one_iff (N := K) (x := g⁻¹ * (a • g))).mp
    change QuotientGroup.mk' K (g⁻¹ * (a • g)) = 1
    rw [map_mul, map_inv]
    have hmk : QuotientGroup.mk' K (a • g) = QuotientGroup.mk' K g := by
      calc
        QuotientGroup.mk' K (a • g) = a • QuotientGroup.mk' K g := by
          simpa only [QuotientGroup.mk'_apply] using
            (MulAction.Quotient.smul_mk K a g).symm
        _ = QuotientGroup.mk' K g := htrivQ a _
    rw [hmk]
    simp
  have hKtop : K = ⊤ := by
    rw [hcomm] at hcomm_le
    exact top_unique hcomm_le
  have hpW : p ∣ Nat.card W := by
    rcases hWp.card_eq_or_dvd with hWcard | hpW
    · exact False.elim (hWne (Subgroup.card_eq_one.mp hWcard))
    · exact hpW
  have hpH : p ∣ Nat.card H :=
    dvd_trans hpW (by
      simpa using
        (Subgroup.card_dvd_of_le (show W ≤ (⊤ : Subgroup H) from le_top)))
  have hcoprimeCore := pPrimeCore_coprime_card (G := H) (p := p)
  have hcoprimeH : Nat.Coprime p (Nat.card H) := by
    rw [show pPrimeCore p H = ⊤ from hKtop] at hcoprimeCore
    simpa using hcoprimeCore
  exact
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hcoprimeH) hpH

private theorem sevenD_p_dvd_commutator_card
    {X : Type*} [Group X] [Finite X]
    (p : ℕ) [Fact p.Prime] (E A : Subgroup X)
    (hA_norm_E : A ≤ Subgroup.normalizer (E : Set X)) :
    letI : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
    let H : Subgroup E := commutatorAction (A := A) (G := E)
    letI : IsInvariant A E H := commutatorAction_isInvariant
    let K : Subgroup H := pPrimeCore p H
    letI : IsInvariant A H K := isInvariant_of_characteristic K
    letI : MulDistribMulAction A (H ⧸ K) :=
      quotientMulDistribMulAction (A := A) (G := H) K
        (isInvariant_of_characteristic K)
    letI : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
      isInvariant_of_characteristic _
    (∃ a : A, ∃ q : pCore p (H ⧸ K), a • q ≠ q) →
      ∀ S : Sylow p E,
        p ∣ Nat.card (⁅A, (S : Subgroup E).map E.subtype⁆ : Subgroup X) := by
  classical
  dsimp only
  let : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
  let H : Subgroup E := commutatorAction (A := A) (G := E)
  let : H.Normal := commutatorAction_normal
  let : IsInvariant A E H := commutatorAction_isInvariant
  let K : Subgroup H := pPrimeCore p H
  let : IsInvariant A H K := isInvariant_of_characteristic K
  let : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K
      (isInvariant_of_characteristic K)
  let : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
    isInvariant_of_characteristic _
  intro hnontriv S
  let qH : H →* H ⧸ K := QuotientGroup.mk' K
  let T : Sylow p H :=
    CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal S H
  let Tbar : Sylow p (H ⧸ K) :=
    T.mapSurjective (f := qH) (QuotientGroup.mk'_surjective K)
  let U : Subgroup (H ⧸ K) :=
    (Tbar : Subgroup (H ⧸ K)) ⊔ pCore p (H ⧸ K)
  have hsupP : IsPGroup p U := by
    dsimp [U]
    exact IsPGroup.to_sup_of_normal_right Tbar.isPGroup'
      (pCore_isPGroup (G := H ⧸ K) (p := p))
  have hsupEq : U = (Tbar : Subgroup (H ⧸ K)) :=
    Tbar.is_maximal' hsupP (by
      dsimp [U]
      exact le_sup_left)
  have hpcore_le_Tbar : pCore p (H ⧸ K) ≤ Tbar := by
    calc
      pCore p (H ⧸ K) ≤ U := by
        dsimp [U]
        exact le_sup_right
      _ = Tbar := hsupEq
  obtain ⟨a, q, hqmove⟩ := hnontriv
  have hqTbar : (q : H ⧸ K) ∈ (Tbar : Subgroup (H ⧸ K)) :=
    hpcore_le_Tbar q.property
  have hqmap : (q : H ⧸ K) ∈ (T : Subgroup H).map qH := by
    simpa [Tbar] using hqTbar
  rcases hqmap with ⟨t, htT, hqt⟩
  have hqmoveVal : a • (q : H ⧸ K) ≠ (q : H ⧸ K) := by
    intro hfix
    apply hqmove
    exact Subtype.ext hfix
  have htmove : a • qH t ≠ qH t := by
    simpa [hqt] using hqmoveVal
  let c : H := t⁻¹ * (a • t)
  have hqc : qH c = (qH t)⁻¹ * (a • qH t) := by
    simp [c, qH]
  have hqc_ne : qH c ≠ 1 := by
    intro hc1
    apply htmove
    have hinv : (qH t)⁻¹ * (a • qH t) = 1 := by
      simpa [hqc] using hc1
    exact (eq_of_inv_mul_eq_one hinv).symm
  have hqtP : qH t ∈ pCore p (H ⧸ K) := by
    rw [hqt]
    exact q.property
  have haqtP : a • qH t ∈ pCore p (H ⧸ K) :=
    (IsInvariant.invariant (A := A) (G := H ⧸ K)
      (H := pCore p (H ⧸ K)) a (qH t)).1 hqtP
  have hqcP : qH c ∈ pCore p (H ⧸ K) := by
    rw [hqc]
    exact (pCore p (H ⧸ K)).mul_mem
      ((pCore p (H ⧸ K)).inv_mem hqtP) haqtP
  let cP : pCore p (H ⧸ K) := ⟨qH c, hqcP⟩
  have hcP_ne : cP ≠ 1 := by
    intro hcP
    exact hqc_ne (congrArg Subtype.val hcP)
  obtain ⟨n, hn⟩ :=
    (IsPGroup.iff_orderOf.mp
      (pCore_isPGroup (G := H ⧸ K) (p := p))) cP
  have hn_ne : n ≠ 0 := by
    intro hn0
    subst n
    have hcP_order : orderOf cP = 1 := by simpa using hn
    exact hcP_ne (orderOf_eq_one_iff.mp hcP_order)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
  have hp_order_cP : p ∣ orderOf cP := by
    rw [hn]
    simp [pow_succ]
  have hp_order_qc : p ∣ orderOf (qH c) := by
    rw [show orderOf (qH c) = orderOf cP from Subgroup.orderOf_coe cP]
    exact hp_order_cP
  have hp_order_c : p ∣ orderOf c :=
    dvd_trans hp_order_qc (orderOf_map_dvd qH c)
  have htS : (t : E) ∈ (S : Subgroup E) := by
    simpa [T, CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe,
      Subgroup.mem_subgroupOf] using htT
  have htSX : (t : X) ∈ (S : Subgroup E).map E.subtype :=
    Subgroup.mem_map_of_mem E.subtype htS
  have hcComm : (c : X) ∈
      ⁅(S : Subgroup E).map E.subtype, A⁆ := by
    have hgen : ⁅(t : X)⁻¹, (a : X)⁆ ∈
        ⁅(S : Subgroup E).map E.subtype, A⁆ :=
      Subgroup.commutator_mem_commutator
        (H₁ := (S : Subgroup E).map E.subtype) (H₂ := A)
        (((S : Subgroup E).map E.subtype).inv_mem htSX) a.property
    have hsmul : ((a • t : H) : X) =
        (a : X) * (t : X) * (a : X)⁻¹ := by
      change ((a • (t : E) : E) : X) =
        (a : X) * (t : X) * (a : X)⁻¹
      exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
        A E a (t : E)
    change (t : X)⁻¹ * ((a • t : H) : X) ∈
      ⁅(S : Subgroup E).map E.subtype, A⁆
    rw [hsmul]
    simpa [commutatorElement_def, mul_assoc] using hgen
  have hp_order_cX : p ∣ orderOf (c : X) := by
    simpa only [Subgroup.orderOf_coe] using hp_order_c
  let C : Subgroup X := ⁅(S : Subgroup E).map E.subtype, A⁆
  let cComm : C := ⟨(c : X), hcComm⟩
  have hp_card_comm : p ∣ Nat.card C := by
    apply dvd_trans hp_order_cX
    have horder : orderOf (c : X) = orderOf cComm := by
      simp [cComm]
    rw [horder]
    exact orderOf_dvd_natCard cComm
  simpa only [C, Subgroup.commutator_comm] using hp_card_comm

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem commutator_zpowers_le_self {B : Subgroup X} {z : X} (hzB : z ∈ normalizer (B : Set X)) :
    ⁅B, zpowers z⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  intro b hb g hg
  have hgB : g ∈ normalizer (B : Set X) := (Subgroup.zpowers_le.mpr hzB) hg
  rw [commutatorElement_def]
  have h1 : g * b⁻¹ * g⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp hgB b⁻¹).mp (B.inv_mem hb)
  have e : b * g * b⁻¹ * g⁻¹ = b * (g * b⁻¹ * g⁻¹) := by group
  rw [e]
  exact B.mul_mem hb h1

theorem p_dvd_card_commutator_zpowers_of_odd_normalized {p : ℕ} (hp : p.Prime) {B : Subgroup X}
    {z : X} (hz : orderOf z = 2) (hBodd : Odd (Nat.card B)) (hzB : z ∈ normalizer (B : Set X))
    {W : Subgroup X} (hWp : IsPGroup p W) (hWne : W ≠ ⊥) (hWcomm : W ≤ ⁅B, zpowers z⁆)
    {S : Subgroup X} (hS : ABGLocalTools.IsSylowOf p S B) : p ∣ Nat.card ↥⁅zpowers z, S⁆ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let A : Subgroup X := zpowers z
  have hA_norm_B : A ≤ normalizer (B : Set X) := by
    rw [Subgroup.zpowers_le]
    exact hzB
  let : Subgroup.Normalizes A B := ⟨hA_norm_B⟩
  let H : Subgroup B := commutatorAction (A := A) (G := B)
  let : IsInvariant A B H := commutatorAction_isInvariant
  let K : Subgroup H := pPrimeCore p H
  let : IsInvariant A H K := isInvariant_of_characteristic K
  let : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K
      (isInvariant_of_characteristic K)
  let : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
    isInvariant_of_characteristic _
  have hAcard : Nat.card A = 2 := by
    simp [A, Nat.card_zpowers, hz]
  have hcopAB : Nat.Coprime (Nat.card A) (Nat.card B) := by
    rw [hAcard]
    exact hBodd.coprime_two_left
  have hBsolv : Group.IsSolvable B := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hBodd
  have hHsolv : Group.IsSolvable H := subgroup_solvable_of_solvable H
  have hcopAH : Nat.Coprime (Nat.card A) (Nat.card H) :=
    Nat.Coprime.of_dvd_right (by
      simpa using
        (Subgroup.card_dvd_of_le (show H ≤ (⊤ : Subgroup B) from le_top))) hcopAB
  have hsat : commutatorAction₂ (A := A) (G := B) = H := by
    simpa [H] using
      (commutatorAction₂_eq_commutatorAction_of_solvable_coprime
        (G := B) (A := A) hBsolv hcopAB)
  have hcommTop : commutatorAction (A := A) (G := H) = ⊤ := by
    apply (Subgroup.map_injective H.subtype_injective)
    rw [commutatorAction_map_subtype_eq_commutatorAction₂]
    rw [hsat]
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
  have hWB : W ≤ B := hWcomm.trans (commutator_zpowers_le_self hzB)
  let WB : Subgroup B := W.subgroupOf B
  have hmapComm : H.map B.subtype = ⁅B, A⁆ := by
    simpa [H] using
      (commutatorAction_subgroup_conj_map_eq_commutator B A hA_norm_B)
  have hWBleH : WB ≤ H := by
    intro w hw
    have hwW : (w : X) ∈ W := by
      simpa [WB, Subgroup.mem_subgroupOf] using hw
    have hwComm : (w : X) ∈ ⁅B, A⁆ := hWcomm hwW
    rw [← hmapComm] at hwComm
    rcases hwComm with ⟨y, hy, hyw⟩
    have hywE : (y : B) = w := B.subtype_injective hyw
    simpa [hywE] using hy
  let WH : Subgroup H := WB.subgroupOf H
  have hWBp : IsPGroup p WB := hWp.comap_subtype
  have hWHp : IsPGroup p WH :=
    hWBp.of_equiv (Subgroup.subgroupOfEquivOfLe hWBleH).symm
  have hWBne : WB ≠ ⊥ := by
    intro hbot
    exact hWne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hWB)
  have hWHne : WH ≠ ⊥ := by
    intro hbot
    exact hWBne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hWBleH)
  have hnot := sevenD_nontrivial_pCore_quotient_action
    (H := H) (A := A) p hHsolv hcopAH hcommTop hWHp hWHne
  have hnontriv : ∃ a : A, ∃ q : pCore p (H ⧸ K), a • q ≠ q := by
    apply Classical.byContradiction
    intro hex
    apply hnot
    intro a q
    by_contra hne
    exact hex ⟨a, q, hne⟩
  obtain ⟨SB, hSB⟩ := hS
  have hpmap := sevenD_p_dvd_commutator_card p B A hA_norm_B hnontriv SB
  simpa [A, hSB] using hpmap

theorem p_dvd_card_commutator_zpowers_of_odd_normal {p : ℕ} (hp : p.Prime) {E B : Subgroup X}
    {z : X} (hz : orderOf z = 2) (hBE : B ≤ E) (hEB : E ≤ normalizer (B : Set X))
    (hBodd : Odd (Nat.card B)) (hzB : z ∈ normalizer (B : Set X)) {W : Subgroup X}
    (hWp : IsPGroup p W) (hWne : W ≠ ⊥) (hWcomm : W ≤ ⁅B, zpowers z⁆) {S' : Subgroup X}
    (hS' : ABGLocalTools.IsSylowOf p S' E) : p ∣ Nat.card ↥⁅zpowers z, S'⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 := p_dvd_card_commutator_zpowers_of_odd_normalized hp hz hBodd hzB hWp hWne hWcomm
    (hS'.inf_of_le_normalizer hBE hEB)
  exact h1.trans (Subgroup.card_dvd_of_le (Subgroup.commutator_mono le_rfl inf_le_left))

end Generic

section StageE

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem stage2E_le_inf (M β : Subgroup X) (z : X) : stage2E M β z ≤ M ⊓ β :=
  inf_le_left

omit [Finite X] in
theorem mem_normalizer_stage2E (hZ : IsInvariantInvolutionSet Z) {z : X} (hz : z ∈ Z)
    (hzM : z ∈ M) (β : Subgroup X) : z ∈ normalizer (stage2E M β z : Set X) := by
  have hF : z ∈ normalizer ((β ⊓ conjugate β z : Subgroup X) : Set X) :=
    mem_normalizer_inf_conjugate (M := β) (hZ.mul_self_eq_one hz)
  unfold stage2E
  rw [inf_assoc]
  exact mem_normalizer_inf (Subgroup.le_normalizer hzM) hF

theorem IsProductDisconnected.exists_mul_centralizer_stage2E (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {β : Subgroup X}
    (hβ : β ∈ omega M) (hβM : β ≠ M) {e : X} (he : e ∈ stage2E M β z) :
    ∃ b ∈ pPrimeCoreIn (stage2E M β z),
      ∃ c ∈ stage2E M β z ⊓ centralizer ({z} : Set X), e = b * c := by
  have hD := (h.prop38d hZ hz hzM hβ hβM).1
  have heD : e ∈ M ⊓ β := stage2E_le_inf M β z he
  have hmem : e ∈ ((pPrimeCoreIn (M ⊓ β) : Subgroup X) : Set X) *
      (((M ⊓ β) ⊓ centralizer ({z} : Set X) : Subgroup X) : Set X) := by
    rw [← hD]
    exact heD
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.mp hmem
  have hcD : c ∈ M ⊓ β := (Subgroup.mem_inf.mp hc).1
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
  have hcE : c ∈ stage2E M β z := by
    refine Subgroup.mem_inf.mpr ⟨hcD, mem_conjugate_iff.mpr ?_⟩
    have e1 : z * c * z⁻¹ = c := by rw [← hcz]; group
    rw [e1]
    exact (Subgroup.mem_inf.mp hcD).2
  have haE : a ∈ stage2E M β z := by
    have := (stage2E M β z).mul_mem he ((stage2E M β z).inv_mem hcE)
    simpa using this
  refine ⟨a, ?_, c, Subgroup.mem_inf.mpr ⟨hcE, (Subgroup.mem_inf.mp hc).2⟩, rfl⟩
  have hle : pPrimeCoreIn (M ⊓ β) ⊓ stage2E M β z ≤ pPrimeCoreIn (stage2E M β z) := by
    apply le_pPrimeCoreIn inf_le_right
    · intro x hx
      exact mem_normalizer_inf (pPrimeCoreIn_normalizes (M ⊓ β) (stage2E_le_inf M β z hx))
        (Subgroup.le_normalizer hx)
    · exact Odd.of_dvd_nat (odd_card_pPrimeCoreIn _) (Subgroup.card_dvd_of_le inf_le_left)
  exact hle ⟨ha, haE⟩

theorem commutator_zpowers_stage2E_le (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {β : Subgroup X}
    (hβ : β ∈ omega M) (hβM : β ≠ M) :
    ⁅zpowers z, stage2E M β z⁆ ≤ ⁅pPrimeCoreIn (stage2E M β z), zpowers z⁆ := by
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  rw [Subgroup.commutator_le]
  intro g hg e he
  rcases eq_one_or_eq_of_mem_zpowers hz2 hg with hg1 | hgz
  · rw [hg1]
    simp
  · rw [hgz]
    obtain ⟨b, hb, c, hc, rfl⟩ := h.exists_mul_centralizer_stage2E hZ hz hzM hβ hβM he
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    have hcz' : c * z⁻¹ = z⁻¹ * c := (show Commute c z from hcz).inv_right.eq
    have e1 : ⁅z, b * c⁆ = ⁅z, b⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc z * (b * c) * z⁻¹ * (b * c)⁻¹ = z * b * (c * z⁻¹) * c⁻¹ * b⁻¹ := by group
        _ = z * b * (z⁻¹ * c) * c⁻¹ * b⁻¹ := by rw [hcz']
        _ = z * b * z⁻¹ * b⁻¹ := by group
    have e2 : ⁅z, b⁆ = ⁅b, z⁆⁻¹ := (commutatorElement_inv b z).symm
    rw [e1, e2]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hb (Subgroup.mem_zpowers z))

theorem IsProductDisconnected.sevenD (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) : SevenDStmt Z M := by
  intro z p W hcand β hβ hβM S' hS'
  have hz := hcand.mem_Z
  have hzM := hcand.mem_M
  have hz2 : orderOf z = 2 := hZ.1 z hz
  obtain ⟨hβΩ, hWβ⟩ := h.mem_omegaFix_iff.mp hβ
  have hWD : W ≤ M ⊓ β := le_inf hcand.le_M hWβ
  have hWE : W ≤ stage2E M β z := prop38a hWD hcand.normalizes
  have hzE : z ∈ normalizer (stage2E M β z : Set X) := mem_normalizer_stage2E hZ hz hzM β
  have hWcomm : W ≤ ⁅pPrimeCoreIn (stage2E M β z), zpowers z⁆ :=
    calc W = ⁅zpowers z, W⁆ := hcand.comm_eq.symm
      _ ≤ ⁅zpowers z, stage2E M β z⁆ := Subgroup.commutator_mono le_rfl hWE
      _ ≤ ⁅pPrimeCoreIn (stage2E M β z), zpowers z⁆ :=
        commutator_zpowers_stage2E_le hZ h hz hzM hβΩ hβM
  exact p_dvd_card_commutator_zpowers_of_odd_normal hcand.prime hz2 (pPrimeCoreIn_le _)
    (pPrimeCoreIn_normalizes _) (odd_card_pPrimeCoreIn _) (mem_normalizer_pPrimeCoreIn hzE)
    hcand.pgroup hcand.ne_bot hWcomm hS'

theorem ZDSetup.sevenD (S : ZDSetup X Z M) : SevenDStmt Z M :=
  S.prodDisc.sevenD S.invariant

end StageE

end CFSG.GH74.Uniqueness
