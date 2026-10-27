module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMovedPerfect
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Sporadic.Fi24.Edge
public import CFSG.Sporadic.Fi24.Involutions
public import CFSG.Sporadic.Fi24.Local
public import CFSG.Sporadic.Fi24.ExtFi23
public import CFSG.Sporadic.Fi24.ExtOuter
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi24
public import CFSG.Sporadic.FischerOddCore.Fi24TJComp
public import CFSG.Sporadic.FischerOddCore.Fi24R2Comp
public import CFSG.Sporadic.FischerOddCore.Fi24Block
public import CFSG.Sporadic.Fi23.Fischer
public import CFSG.Sporadic.Fi23.Simple
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Fischer.Polar.Facts
public import CFSG.Sporadic.Fi23.InvCover
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1007
public import Certificates.Certificate1008
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1014
public import Certificates.Certificate1015
public import Certificates.Certificate1016
public import Certificates.Certificate1017
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate2075
public import Certificates.Certificate3166
public import Certificates.Certificate6098
public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl
public import CFSG.Monster.Code.Weights

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.Sporadic.Fi24
open scoped commutatorElement

local notation "LEdge" => CFSG.Sporadic.Fi24.LE

@[expose] noncomputable def zR :
    R :=
  jR CFSG.Sporadic.FischerOddCore.fi24R2

@[expose] noncomputable def PB :
    Subgroup R :=
  centDer JR zR

@[expose] def TranspositionOrderFour :
    Prop :=
  ∃ y ∈ MR, 4 ∣ orderOf y

@[expose] def TwoAOrderFour :
    Prop :=
  ∃ y ∈ LEdge, 4 ∣ orderOf y

@[expose] def TwoACentralizer :
    Prop :=
  ∀ c : R, c * c = 1 → c ∈ centralizer (LEdge : Set R) → c ∈ zpowers (tR * xb) ∨ c ∈ D24

@[expose] def TwoBPerfect :
    Prop :=
  ⁅PB, PB⁆ = PB

@[expose] def TwoBQ
    (Q : Subgroup R) : Prop :=
  Q ≤ PB ∧ ∀ p ∈ PB, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q

@[expose] def TwoBIrreducible
    (Q : Subgroup R) : Prop :=
  ∀ N : Subgroup R, N ≤ Q → (∀ p ∈ PB, ∀ y ∈ N, p * y * p⁻¹ ∈ N) → N ≤ zpowers zR ∨ N = Q

@[expose] def TwoBFaithful
    (Q : Subgroup R) : Prop :=
  ∀ x ∈ PB, (∀ q ∈ Q, ⁅x, q⁆ ∈ zpowers zR) → x ∈ Q

@[expose] def TwoBOrderFour
    (Q : Subgroup R) : Prop :=
  ∃ y ∈ Q, 4 ∣ orderOf y

@[expose] def TwoBCentralizer :
    Prop :=
  ∀ c : R, c * c = 1 → c ∈ centralizer (PB : Set R) → c ∈ zpowers zR

theorem fi24AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Fi24Prime) ↥R JR :=
  RankTwoSporadic.Cert.autModel_of_conj J_le_R fi24EquivJ.symm
    (MulEquiv.ofBijective conjJ ⟨conjJ_injective, CFSG.Sporadic.FischerOddCore.conjJ_surjective⟩)
    fun x p => by
      change ((conjJ x p : J) : GL (Fin 781) (ZMod 3)) = _
      rw [coe_conjJ, Subgroup.coe_inv]

theorem JR_inf_centralizer_tR :
    JR ⊓ centralizer {tR} = MR := by
  have hc : ∀ m ∈ MR, tR * m = m * tR := fun m hm =>
    (mem_centralizer_iff.mp (zpowers_tR_le_centralizer_MR (mem_zpowers tR)) m hm).symm
  apply le_antisymm
  · rintro x ⟨hxJ, hxC⟩
    rw [centralizer_tR] at hxC
    obtain ⟨k, m, hm, rfl⟩ := exists_zpow_mul_of_mem_sup hc hxC
    rcases eq_one_or_eq_of_mem_zpowers (by rw [sq]; exact tR_mul_tR) (zpow_mem_zpowers tR k)
      with h | h
    · rw [h, one_mul]
      exact hm
    · exfalso
      apply tR_not_mem_JR
      rw [h] at hxJ
      have := JR.mul_mem hxJ (JR.inv_mem (MR_le_JR hm))
      rwa [mul_inv_cancel_right] at this
  · exact le_inf MR_le_JR (by rw [centralizer_tR]; exact le_sup_right)

theorem isSimpleGroup_MR :
    IsSimpleGroup ↥MR :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 fi23EquivMR

theorem exists_not_commute_MR :
    ∃ a b : ↥MR, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hcard : Nat.card ↥MR = 4089470473293004800 := by
    rw [Nat.card_congr fi23EquivMR.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
  have : IsMulCommutative ↥MR := ⟨⟨hcon⟩⟩
  have hs := isSimpleGroup_MR
  have hp := Group.is_simple_iff_prime_card.1 hs
  rw [hcard] at hp
  norm_num at hp

theorem perfect_center_MR :
    commutator ↥MR = ⊤ ∧ center ↥MR = ⊥ := by
  have hs := isSimpleGroup_MR
  obtain ⟨a, b, hab⟩ := exists_not_commute_MR
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥MR) with h | h
    · exfalso
      apply hab
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← mem_bot, ← h]
        exact commutator_mem_commutator (mem_top a) (mem_top b)
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥MR) with h | h
    · exact h
    · have hb : b ∈ center ↥MR := by rw [h]; exact mem_top b
      exact absurd (mem_center_iff.mp hb a) hab

theorem yWitness_tR
    (h1 : TranspositionOrderFour) {E : Subgroup R} (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) (ht : tR ∈ E) : YWitness JR E := by
  have hc : ∀ m ∈ MR, tR * m = m * tR := fun m hm =>
    (mem_centralizer_iff.mp (zpowers_tR_le_centralizer_MR (mem_zpowers tR)) m hm).symm
  obtain ⟨b, hbE, hbz⟩ := exists_not_mem_zpowers_of_isElemAbelian hE4
    (by rw [sq]; exact tR_mul_tR)
  have hbt : b * tR = tR * b := mul_comm_of_isElemAbelian hE hbE ht
  obtain ⟨hperf, hcen⟩ := perfect_center_MR
  have : Group.IsPerfect ↥MR := Group.isPerfect_def.mpr hperf
  have hs := isSimpleGroup_MR
  have hq : CFSG.Open.IsQuasisimple ↥MR := Quasisimple.simple_of_perfect ↥MR
  have hcd : centDer JR tR = MR := by
    rw [centDer, JR_inf_centralizer_tR, commutator_self_of_commutator_eq_top hperf]
  have hbN : b ∈ normalizer (JR : Set R) := by
    rw [normalizer_eq_top_iff.mpr normal_JR]
    exact mem_top b
  refine yWitness_of_perfect ht tR_ne_one hbE (P := MR)
    hcd.ge (commutator_self_of_commutator_eq_top hperf) (fourProp_of_quasisimple hq h1)
    (hcd ▸ mem_normalizer_centDer hbN hbt) fun hbc => hbz ?_
  have hbC : b ∈ zpowers tR ⊔ MR := by
    rw [← centralizer_tR]
    exact mem_centralizer_singleton_iff.mpr hbt
  obtain ⟨m₀, hm₀, hb⟩ := exists_mem_eq_or_eq_mul_of_mem_sup hc tR_mul_tR hbC
  have hcen' : ∀ m ∈ MR, (∀ y ∈ MR, y * m = m * y) → m = 1 := by
    intro m hm hy
    have hmem : (⟨m, hm⟩ : ↥MR) ∈ center ↥MR := by
      rw [mem_center_iff]
      exact fun y => Subtype.ext (hy y y.2)
    rw [hcen, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  rcases hb with rfl | rfl
  · rw [hcen' b hm₀ fun y hy => (mem_centralizer_iff.mp hbc) y hy]
    exact one_mem _
  · rw [hcen' m₀ hm₀ fun y hy => by
      have h := (mem_centralizer_iff.mp hbc) y hy
      have h2 := hc y hy
      calc y * m₀ = tR⁻¹ * (y * (tR * m₀)) := by
            rw [← mul_assoc y, ← h2]; group
        _ = tR⁻¹ * (tR * m₀ * y) := by rw [h]
        _ = m₀ * y := by group, mul_one]
    exact mem_zpowers tR

theorem yWitness_of_mem_D24
    (h1 : TranspositionOrderFour) {E : Subgroup R} (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) {d : R} (hdE : d ∈ E) (hd : d ∈ D24) : YWitness JR E :=
  yWitness_of_isConj_mem normal_JR (fun _ hE' hE4' ht => yWitness_tR h1 hE' hE4' ht) hE hE4
    hdE hd

theorem centDer_tJ :
    centDer JR (tR * xb) = LEdge := by
  have hperf : ⁅LEdge, LEdge⁆ = LEdge := commutator_self_of_commutator_eq_top commutator_LE
  have hCE : JR ⊓ centralizer {tR * xb} = CE := inf_comm _ _
  rw [centDer, hCE]
  refine le_antisymm
    (commutator_le_of_relIndex_two CFSG.Sporadic.FischerOddCore.fi24_index_LE) ?_
  calc LEdge = ⁅LEdge, LEdge⁆ := hperf.symm
    _ ≤ ⁅CE, CE⁆ := commutator_mono inf_le_left inf_le_left

theorem fourProp_LE
    (h2 : TwoAOrderFour) : FourProp LEdge := by
  rw [LE_eq_map, fourProp_map_iff fromFi23 fromFi23_injective]
  obtain ⟨-, h1, -⟩ := CFSG.Sporadic.Fi23.localStructureAt_of_mem sb_mem_D23
  obtain ⟨hcomm, -, -, ⟨e⟩⟩ := h1 rfl
  refine fourProp_of_quasisimple
    ⟨hcomm, @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e⟩ ?_
  obtain ⟨y, hy, h4⟩ := h2
  rw [LE_eq_map] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨y', hy', by rwa [orderOf_injective fromFi23 fromFi23_injective] at h4⟩

theorem yWitness_tJ
    (h1 : TranspositionOrderFour) (h2 : TwoAOrderFour) (h3 : TwoACentralizer)
    {E : Subgroup R} (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (ht : tR * xb ∈ E) :
    YWitness JR E := by
  obtain ⟨b, hbE, hbz⟩ := exists_not_mem_zpowers_of_isElemAbelian hE4
    (by rw [sq]; exact tR_mul_xb_sq)
  have hbt : b * (tR * xb) = (tR * xb) * b :=
    mul_comm_of_isElemAbelian hE hbE ht
  have hbN : b ∈ normalizer (JR : Set R) := by
    rw [normalizer_eq_top_iff.mpr normal_JR]
    exact mem_top b
  by_cases hbc : b ∈ centralizer (LEdge : Set R)
  · rcases h3 b (by rw [← sq]; exact hE.2 b hbE) hbc with h | h
    · exact absurd h hbz
    · exact yWitness_of_mem_D24 h1 hE hE4 hbE h
  · have ht1 : tR * xb ≠ 1 := fun h => by
      have hx : xb = tR⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [tR_inv] at hx
      exact tR_ne_xb hx.symm
    refine yWitness_of_perfect ht ht1 hbE (P := LEdge)
      centDer_tJ.ge (commutator_self_of_commutator_eq_top commutator_LE) (fourProp_LE h2)
      (centDer_tJ ▸ mem_normalizer_centDer hbN hbt) hbc

theorem yWitness_zR
    (hP : TwoBPerfect) {Q : Subgroup R} (hQ : TwoBQ Q) (hirr : TwoBIrreducible Q)
    (hfaith : TwoBFaithful Q) (h4 : TwoBOrderFour Q) (hC : TwoBCentralizer)
    {E : Subgroup R} (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (ht : zR ∈ E) :
    YWitness JR E := by
  have hz2 : zR ^ 2 = 1 := hE.2 zR ht
  obtain ⟨b, hbE, hbz⟩ := exists_not_mem_zpowers_of_isElemAbelian hE4 hz2
  have hbt : b * zR = zR * b := mul_comm_of_isElemAbelian hE hbE ht
  have hbN : b ∈ normalizer (JR : Set R) := by
    rw [normalizer_eq_top_iff.mpr normal_JR]
    exact mem_top b
  have hPC : ∀ p ∈ PB, p * zR = zR * p := by
    intro p hp
    have h := (Subgroup.mem_inf.mp (centDer_le JR zR hp)).2
    rw [mem_centralizer_singleton_iff] at h
    exact h
  have hfour : FourProp PB :=
    fourProp_of_constrained hQ.1 hQ.2
      (fun z hz p hp => commute_of_mem_zpowers (hPC p hp) hz) hirr hfaith h4
  have hz1 : zR ≠ 1 := fun h =>
    CFSG.Sporadic.FischerOddCore.fi24R2_ne_one (jR_injective (h.trans (map_one jR).symm))
  refine yWitness_of_perfect ht hz1 hbE (P := PB) le_rfl
    hP hfour (mem_normalizer_centDer hbN hbt) fun hbc => hbz ?_
  exact hC b (by rw [← sq]; exact hE.2 b hbE) hbc

theorem fi24_yCensus
    (h1 : TranspositionOrderFour) (h2 : TwoAOrderFour) (h3 : TwoACentralizer)
    (hP : TwoBPerfect) {Q : Subgroup R} (hQ : TwoBQ Q) (hirr : TwoBIrreducible Q)
    (hfaith : TwoBFaithful Q) (h4 : TwoBOrderFour Q) (hC : TwoBCentralizer) :
    YCensus JR (fun _ => False) := by
  intro E hE hE4 _
  obtain ⟨t, htE, htJ, ht1⟩ :=
    exists_mem_inf_ne_one_of_index_dvd_two normal_JR (by rw [index_JR]) hE4
  set s : J := ⟨(t : GL (Fin 781) (ZMod 3)), mem_subgroupOf.mp htJ⟩ with hs
  have hst : jR s = t := Subtype.ext rfl
  have hs2 : s * s = 1 := by
    apply jR_injective
    rw [map_mul, hst, map_one, ← sq]
    exact hE.2 t htE
  have hs1 : s ≠ 1 := fun h => ht1 (by rw [← hst, h, map_one])
  rcases isConj_tJ_or_r2 CFSG.Fischer.polarFacts CFSG.Sporadic.Fi23.d1_mem_localClass
      CFSG.Sporadic.Fi23.involution_cover hs2 hs1 with h | h
  · have hc : IsConj (tR * xb) t := by
      rw [← jR_tJ, ← hst]
      exact (MonoidHom.map_isConj jR h).symm
    exact yWitness_of_isConj_mem normal_JR (fun _ hE' hE4' ht' => yWitness_tJ h1 h2 h3 hE' hE4' ht')
      hE hE4 htE hc
  · have hc : IsConj zR t := by
      rw [← hst]
      exact (MonoidHom.map_isConj jR (h.trans CFSG.Sporadic.FischerOddCore.isConj_t2_fi24R2)).symm
    exact yWitness_of_isConj_mem normal_JR
      (fun _ hE' hE4' ht' => yWitness_zR hP hQ hirr hfaith h4 hC hE' hE4' ht') hE hE4 htE hc

theorem sporadicCaseOdd_Fi24Prime_of_facts
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    (h1 : TranspositionOrderFour) (h2 : TwoAOrderFour) (h3 : TwoACentralizer)
    (hP : TwoBPerfect) {Q : Subgroup R} (hQ : TwoBQ Q) (hirr : TwoBIrreducible Q)
    (hfaith : TwoBFaithful Q) (h4 : TwoBOrderFour Q) (hC : TwoBCentralizer) :
    SporadicCaseOdd .Fi24Prime :=
  sporadicCaseOdd_of_yCensus h32 h33 fi24AutModel
    (fi24_yCensus h1 h2 h3 hP hQ hirr hfaith h4 hC)

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
