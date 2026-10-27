module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneInnerAction
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34SylowStructure
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoSL34
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VSylow
import CFSG.Quasithin.EmptyFaithful.SzN31SmD6GrpB
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.DedekindNormalizer
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.SwappedFactorsOffenders
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.Quasithin.SteinbergBKPairedCentralSeeds
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M H E Q J : Subgroup G}

abbrev FourteenTwoConcl (Q J : Subgroup G) : Prop :=
  (Nat.card Q = 3 ^ 5 ∧ (∀ x ∈ Q, x ^ 3 = 1) ∧
      ⁅Q, Q⁆ = (Subgroup.center ↥Q).map Q.subtype ∧
      Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3) ∧
    ∃ Q₀ : Subgroup G, Q₀ ≤ Q ∧ Nat.card Q₀ = 27 ∧ ⁅Q₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J ∧
      (Subgroup.center ↥Q).map Q.subtype ≤ Q₀

private theorem inf_starCentralizer_eq_oTwoZStar (J : Subgroup G) :
    J ⊓ starCentralizer J = oTwoZStar J := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxJ, hxS⟩
    obtain ⟨hxN, hact⟩ := (mem_starCentralizer_iff).mp hxS
    have hj : jStarAct J ⟨x, Subgroup.le_normalizer hxJ⟩ = 1 := by
      have hsub : (⟨x, Subgroup.le_normalizer hxJ⟩ :
          ↥(Subgroup.normalizer (J : Set G))) = ⟨x, hxN⟩ := Subtype.ext rfl
      rw [hsub, hact]
    rw [jStarAct_of_mem hxJ] at hj
    have hcenter : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨x, hxJ⟩ ∈
        Subgroup.center (threeStar J) := (CFSG.QuasithinUnique.Setup.Layer.conj_eq_one_iff _).mp hj
    rw [oTwoZStar]
    exact Subgroup.mem_map.mpr ⟨⟨x, hxJ⟩, Subgroup.mem_comap.mpr hcenter, rfl⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyJ : (y : G) ∈ J := y.2
    have hcenter : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) y ∈
        Subgroup.center (threeStar J) := Subgroup.mem_comap.mp hy
    have hxJ : x ∈ J := hyx ▸ hyJ
    refine Subgroup.mem_inf.mpr ⟨hxJ, ?_⟩
    refine (mem_starCentralizer_iff).mpr ⟨Subgroup.le_normalizer hxJ, ?_⟩
    have hsub : (⟨x, Subgroup.le_normalizer hxJ⟩ :
        ↥(Subgroup.normalizer (J : Set G))) =
        ⟨(y : G), Subgroup.le_normalizer hyJ⟩ := Subtype.ext hyx.symm
    rw [hsub, jStarAct_of_mem hyJ]
    exact (CFSG.QuasithinUnique.Setup.Layer.conj_eq_one_iff _).mpr hcenter

private theorem sup_inf_eq_of_le_sup {K E Q : Subgroup G} (hQ : Q ≤ K ⊔ E) (hEQ : E ≤ Q)
    (hEN : E ≤ Subgroup.normalizer (K : Set G)) : Q = (Q ⊓ K) ⊔ E := by
  have h := CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer (S := E) (T := K) (U := Q)
    hEQ hEN
  rw [sup_comm E K, inf_eq_left.mpr hQ] at h
  rwa [sup_comm E (Q ⊓ K)] at h

theorem commutator_eq_center_map_of_card_27 {P : Subgroup G}
    (hP : Nat.card P = 27) (hna : ∃ a b : ↥P, a * b ≠ b * a) :
    ⁅P, P⁆ = (Subgroup.center ↥P).map P.subtype := by
  have h := CFSG.HardMathSupport.Solomon.Coordinator.i112v_commutator_eq_center
    (R := ↥P) hP hna
  rw [← h, _root_.commutator_def, Subgroup.map_commutator]
  congr 1
  · simpa [MonoidHom.range_eq_map] using (P.range_subtype : P.subtype.range = P).symm
  · simpa [MonoidHom.range_eq_map] using (P.range_subtype : P.subtype.range = P).symm

theorem exists_mul_ne_of_card_center_lt {S : Subgroup G} (hS : Nat.card S = 27)
    (hZ : Nat.card ↥((Subgroup.center ↥S).map S.subtype) = 3) :
    ∃ a b : ↥S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative ↥S := ⟨⟨fun a b => hcon a b⟩⟩
  have htop : Subgroup.center ↥S = ⊤ := Subgroup.center_eq_top
  have h27 : Nat.card ↥(Subgroup.center ↥S) = 27 := by
    rw [htop, Subgroup.card_top]
    exact hS
  have h3 : Nat.card ↥(Subgroup.center ↥S) = 3 := by
    rw [← Subgroup.card_map_of_injective S.subtype_injective]
    exact hZ
  omega

private theorem card_sup_zpowers_center_eq_nine {S : Subgroup G} (hS : Nat.card S = 27)
    {x : G} (hxS : x ∈ S) (hx3 : x ^ 3 = 1)
    (hxnc : ∃ g ∈ S, g * x ≠ x * g) :
    Nat.card ↥(Subgroup.zpowers x ⊔ (Subgroup.center ↥S).map S.subtype) = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Z : Subgroup G := (Subgroup.center ↥S).map S.subtype
  have hnc : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨g, hgS, hgx⟩ := hxnc
    exact ⟨⟨g, hgS⟩, ⟨x, hxS⟩, fun h => hgx (congrArg Subtype.val h)⟩
  have hZcard : Nat.card Z = 3 := by
    rw [show Nat.card Z = Nat.card ↥(Subgroup.center ↥S) from
      Subgroup.card_map_of_injective S.subtype_injective]
    exact CFSG.Quasithin.SzN31.SmD6GrpB.card_center_eq_three hS hnc
  have hcenter_card : Nat.card ↥(Subgroup.center ↥S) = 3 := by
    rw [← Subgroup.card_map_of_injective S.subtype_injective]
    exact hZcard
  have hxZ : x ∉ Z := by
    rintro ⟨z, hz, hzx⟩
    obtain ⟨g, hgS, hgx⟩ := hxnc
    have hcentral : g * (z : G) = (z : G) * g :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨g, hgS⟩ : ↥S))
    exact hgx (by rw [show (z : G) = x from hzx] at hcentral; exact hcentral)
  have hZea : CFSG.Open.IsElemAbelian 3 Z := by
    refine ⟨?_, ?_⟩
    · refine ⟨⟨fun p q => ?_⟩⟩
      obtain ⟨p0, hp0, hp0p⟩ := Subgroup.mem_map.mp p.2
      obtain ⟨q0, hq0, hq0q⟩ := Subgroup.mem_map.mp q.2
      apply Subtype.ext
      change (p : G) * (q : G) = (q : G) * (p : G)
      rw [← hp0p, ← hq0q]
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hp0 q0)).symm
    · rintro z hz
      obtain ⟨z0, hz0, hz0z⟩ := Subgroup.mem_map.mp hz
      rw [← hz0z]
      change ((z0 : ↥S) : G) ^ 3 = 1
      have h := pow_card_eq_one' (x := (⟨z0, hz0⟩ : Subgroup.center ↥S))
      rw [hcenter_card] at h
      have h1 : (z0 : ↥S) ^ 3 = 1 := by
        simpa [Subgroup.coe_pow] using congrArg Subtype.val h
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
        congrArg (fun w : ↥S => (w : G)) h1
  have hZx : ∀ a ∈ Z, a * x = x * a := by
    intro a ha
    obtain ⟨a0, ha0, ha0a⟩ := Subgroup.mem_map.mp ha
    rw [← ha0a]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp ha0 ⟨x, hxS⟩)).symm
  obtain ⟨-, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers
    (p := 3) (A := Z) (y := x) hZea hxZ hx3 hZx
  rw [sup_comm (Subgroup.zpowers x) Z, hcard, hZcard]

private theorem card_inf_centralizer_eq_nine {S : Subgroup G} (hS : Nat.card S = 27)
    {x : G} (hxS : x ∈ S) (hxnc : ∃ g ∈ S, g * x ≠ x * g) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) = 9 := by
  classical
  have hnc : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨g, hgS, hgx⟩ := hxnc
    exact ⟨⟨g, hgS⟩, ⟨x, hxS⟩, fun h => hgx (congrArg Subtype.val h)⟩
  have hxcenter : (⟨x, hxS⟩ : ↥S) ∉ Subgroup.center ↥S := by
    intro hc
    obtain ⟨g, hgS, hgx⟩ := hxnc
    exact hgx (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g, hgS⟩))
  have hmap : S ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.map S.subtype (Subgroup.centralizer ({⟨x, hxS⟩} : Set ↥S)) := by
    ext y
    constructor
    · rintro ⟨hyS, hyC⟩
      refine Subgroup.mem_map.mpr ⟨⟨y, hyS⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      apply Subtype.ext
      simpa using Subgroup.mem_centralizer_iff.mp hyC x (by rw [Set.mem_singleton_iff])
    · rintro ⟨y0, hy0, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨y0.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy0 ⟨x, hxS⟩ (by
        rw [Set.mem_singleton_iff]))
  rw [hmap, Subgroup.card_map_of_injective S.subtype_injective]
  exact CFSG.Quasithin.SzN31.SmD6GrpB.card_centralizer_eq_nine hS hnc hxcenter

private theorem inf_centralizer_eq_sup_zpowers_center {S : Subgroup G}
    (hS : Nat.card S = 27) {x : G} (hxS : x ∈ S) (hx3 : x ^ 3 = 1)
    (hxnc : ∃ g ∈ S, g * x ≠ x * g) :
    S ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.zpowers x ⊔ (Subgroup.center ↥S).map S.subtype := by
  have hsupcard := card_sup_zpowers_center_eq_nine hS hxS hx3 hxnc
  have hinfcard := card_inf_centralizer_eq_nine hS hxS hxnc
  have hsup_le : Subgroup.zpowers x ⊔ (Subgroup.center ↥S).map S.subtype ≤
      S ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_
    · refine le_inf (Subgroup.zpowers_le.mpr hxS) ?_
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
    · refine le_inf (Subgroup.map_subtype_le _) ?_
      rintro z ⟨z0, hz0, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz0 ⟨x, hxS⟩)
  exact (Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hinfcard, hsupcard])).symm

theorem commutator_sup_le_of_commute_le {S W Z : Subgroup G}
    (hSW : ∀ s ∈ S, ∀ w ∈ W, Commute s w) (hSS : ⁅S, S⁆ ≤ Z) (hWW : ⁅W, W⁆ ≤ Z)
    (hZ : ∀ z ∈ Z, ∀ q ∈ S ⊔ W, Commute z q) : ⁅S ⊔ W, S ⊔ W⁆ ≤ Z := by
  rw [Subgroup.commutator_le]
  intro q1 hq1 q2 hq2
  obtain ⟨s1, hs1, w1, hw1, rfl⟩ := (CFSG.mem_sup_of_commute hSW).mp hq1
  obtain ⟨s2, hs2, w2, hw2, rfl⟩ := (CFSG.mem_sup_of_commute hSW).mp hq2
  have hws : ⁅w1, s2⁆ = 1 := by
    have h := (hSW s2 hs2 w1 hw1).commutator_eq
    rwa [show ⁅w1, s2⁆ = ⁅s2, w1⁆⁻¹ from by
      rw [commutatorElement_def, commutatorElement_def]; group, h, inv_one]
  have hsw : ⁅s1, w2⁆ = 1 := (hSW s1 hs1 w2 hw2).commutator_eq
  have h1 : ⁅w1, s2 * w2⁆ = s2 * ⁅w1, w2⁆ * s2⁻¹ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hws, one_mul]
  have h2 : ⁅s1, s2 * w2⁆ = ⁅s1, s2⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hsw, mul_one]
    group
  have h3 : ⁅s1 * w1, s2 * w2⁆ =
      s1 * (s2 * ⁅w1, w2⁆ * s2⁻¹) * s1⁻¹ * ⁅s1, s2⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, h1, h2]
  have hwZ : ⁅w1, w2⁆ ∈ Z := hWW (Subgroup.commutator_mem_commutator hw1 hw2)
  have hsZ : ⁅s1, s2⁆ ∈ Z := hSS (Subgroup.commutator_mem_commutator hs1 hs2)
  have h2' : s2 * ⁅w1, w2⁆ * s2⁻¹ = ⁅w1, w2⁆ :=
    (hZ _ hwZ s2 (Subgroup.mem_sup_left hs2)).symm.mul_inv_cancel
  have h1' : s1 * ⁅w1, w2⁆ * s1⁻¹ = ⁅w1, w2⁆ :=
    (hZ _ hwZ s1 (Subgroup.mem_sup_left hs1)).symm.mul_inv_cancel
  rw [h3, h2', h1']
  exact Z.mul_mem hwZ hsZ

theorem card_sup_eq_pow_of_inf_eq_bot {S E Q : Subgroup G} (hQ : Q = S ⊔ E)
    (hSE : S ⊓ E = ⊥) (hEN : E ≤ Subgroup.normalizer (S : Set G))
    (hScard : Nat.card S = 27) (hEcard : Nat.card E = 9) : Nat.card Q = 3 ^ 5 := by
  have hinf : E ⊓ S = ⊥ := by rw [inf_comm]; exact hSE
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := E) (K := S) hEN
  rw [hinf, Subgroup.card_bot, mul_one, hEcard, hScard] at h
  rw [hQ, sup_comm S E, h]
  norm_num

private theorem card_inf_starCentralizer_eq_27 {S W ZS Q : Subgroup G} (hQ : Q = S ⊔ W)
    (hWS : W ≤ Subgroup.normalizer (S : Set G)) (hSW : S ⊓ W = ZS)
    (hZScard : Nat.card ZS = 3) (hScard : Nat.card S = 27) (hQcard : Nat.card Q = 3 ^ 5) :
    Nat.card W = 27 := by
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := W) (K := S) hWS
  rw [sup_comm W S, ← hQ, inf_comm W S, hSW, hZScard, hQcard, hScard] at h
  norm_num at h
  omega

private theorem commutator_inf_starCentralizer_eq_bot {J Q : Subgroup G}
    (hS3 : IsPGroup 3 ↥(Q ⊓ J)) (hQN : Q ≤ Subgroup.normalizer (J : Set G)) :
    ⁅Q ⊓ J, Q ⊓ starCentralizer J⁆ = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  let W : Subgroup G := Q ⊓ starCentralizer J
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf Subgroup.le_normalizer hQN).trans Subgroup.inf_normalizer_le_normalizer_inf
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype
  have hOnot : ¬ 3 ∣ Nat.card O := by
    rw [show Nat.card O = Nat.card (CFSG.pPrimeCore 3 ↥J) from
      Subgroup.card_map_of_injective J.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hSO : S ⊓ O = ⊥ :=
    CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hOnot hS3
  have hleO : ⁅S, W⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro s hs w hw
    have hws : ⁅w, s⁆ ∈ O :=
      commutator_mem_map_of_mem_quotientCentralizer (CFSG.pPrimeCore 3 ↥J)
        Subgroup.le_normalizer le_rfl hw.2 hs.2
    have heq : ⁅s, w⁆ = ⁅w, s⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [heq]
    exact O.inv_mem hws
  have hleS : ⁅S, W⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro s hs w hw
    have hwN : w ∈ Subgroup.normalizer (S : Set G) := hQnormS (Subgroup.mem_inf.mp hw).1
    have hconj : w * s⁻¹ * w⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hwN s⁻¹).mp (S.inv_mem hs)
    have heq : ⁅s, w⁆ = s * (w * s⁻¹ * w⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact S.mul_mem hs hconj
  refine le_bot_iff.mp ?_
  calc ⁅S, W⁆ ≤ S ⊓ O := le_inf hleS hleO
    _ = ⊥ := hSO

private theorem commutator_inf_starCentralizer_eq_bot_of_choice
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) :
    ⁅Q ⊓ J, Q ⊓ starCentralizer J⁆ = ⊥ ∧
      (Q ⊓ J) ⊓ (Q ⊓ starCentralizer J) =
        (Subgroup.center ↥(Q ⊓ J)).map (Q ⊓ J).subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  let W : Subgroup G := Q ⊓ starCentralizer J
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hS3 : IsPGroup 3 S := h.sylow.isPGroup.to_le inf_le_left
  have hcommbot : ⁅S, W⁆ = ⊥ := commutator_inf_starCentralizer_eq_bot hS3 hQN
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S J := h.isSylowOf_inf_J hpre hU
  obtain ⟨-, -, hSZO, -⟩ :=
    IsKComp.sylow_three_structure h.isKComp (Or.inl hSL) hS_sylow
  have h1 : S ⊓ W = S ⊓ (J ⊓ starCentralizer J) := by
    ext x
    constructor
    · rintro ⟨⟨hxQ, hxJ⟩, hxQ', hxC⟩
      exact ⟨⟨hxQ, hxJ⟩, hxJ, hxC⟩
    · rintro ⟨⟨hxQ, hxJ⟩, -, hxC⟩
      exact ⟨⟨hxQ, hxJ⟩, hxQ, hxC⟩
  refine ⟨hcommbot, ?_⟩
  rw [h1, inf_starCentralizer_eq_oTwoZStar, hSZO]

private theorem E_le_sup_inf_starCentralizer_of_choice
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) :
    E ≤ (Q ⊓ J) ⊔ (Q ⊓ starCentralizer J) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  let W : Subgroup G := Q ⊓ starCentralizer J
  have hLN : ¬ pLayerIn 3 H ≤ M := hL 3 E H h.hypCGen
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hEN : E ≤ Subgroup.normalizer (J : Set G) := h.E_le_Q.trans hQN
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S J := h.isSylowOf_inf_J hpre hU
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf Subgroup.le_normalizer hQN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hES : E ≤ Subgroup.normalizer (S : Set G) := h.E_le_Q.trans hQnormS
  intro e he
  obtain ⟨x, hxS, hw⟩ := HypCGen.exists_inner_mul_mem_starCentralizer
    h.hypCGen hLN h.isKComp (Or.inl hSL) hEN hS_sylow hES he
  have hwW : x⁻¹ * e ∈ W := by
    refine Subgroup.mem_inf.mpr ⟨?_, hw⟩
    exact Q.mul_mem (Q.inv_mem ((inf_le_left : S ≤ Q) hxS)) (h.E_le_Q he)
  have heq : x * (x⁻¹ * e) = e := by group
  rw [← heq]
  exact Subgroup.mul_mem_sup hxS hwW

theorem S14Choice.eq_inf_J_sup_E_of_kComp_self (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hK : IsKComp M H (kSub 3 M H)) : Q = (Q ⊓ J) ⊔ E := by
  have hJeq : J = kSub 3 M H := IsKComp.eq_kSub_of_isKComp_self hK h.isKComp
  have hQle : Q ≤ J ⊔ E := by
    rw [hJeq]
    exact h.sylow.le
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hEN : E ≤ Subgroup.normalizer (J : Set G) := h.E_le_Q.trans hQN
  exact sup_inf_eq_of_le_sup hQle h.E_le_Q hEN

private theorem inf_E_inf_starCentralizer_eq_bot (h : HypCGen G M 3 E H)
    (hLN : ¬ pLayerIn 3 H ≤ M) {J : Subgroup G} (hJ : IsKComp M H J) :
    E ⊓ (Q ⊓ starCentralizer J) = ⊥ := by
  have hEstar : E ⊓ starCentralizer J = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨heE, heS⟩ := Subgroup.mem_inf.mp he
    have h1 := HypCGen.eq_one_of_mem_starCentralizer h hLN hJ heE heS
    simpa [h1]
  calc E ⊓ (Q ⊓ starCentralizer J) = (E ⊓ Q) ⊓ starCentralizer J := by rw [inf_assoc]
    _ = (Q ⊓ E) ⊓ starCentralizer J := by rw [inf_comm E Q]
    _ = Q ⊓ (E ⊓ starCentralizer J) := by rw [inf_assoc]
    _ = ⊥ := by rw [hEstar]; simp

private theorem E_le_zpowers_of_mem_inf
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) {e1 : G} (he1E : e1 ∈ E)
    (he1S : e1 ∈ Q ⊓ J) (he1ne : e1 ≠ 1)
    (hSWcomm : ∀ s ∈ Q ⊓ J, ∀ w ∈ Q ⊓ starCentralizer J, Commute s w)
    (hEW : E ⊓ (Q ⊓ starCentralizer J) = ⊥) :
    E ≤ Subgroup.zpowers e1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  let W : Subgroup G := Q ⊓ starCentralizer J
  have hLN : ¬ pLayerIn 3 H ≤ M := hL 3 E H h.hypCGen
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hEN : E ≤ Subgroup.normalizer (J : Set G) := h.E_le_Q.trans hQN
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S J := h.isSylowOf_inf_J hpre hU
  obtain ⟨hScard, hSexp, hSZO, -⟩ :=
    IsKComp.sylow_three_structure h.isKComp (Or.inl hSL) hS_sylow
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf Subgroup.le_normalizer hQN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hES : E ≤ Subgroup.normalizer (S : Set G) := h.E_le_Q.trans hQnormS
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype
  have hOnot : ¬ 3 ∣ Nat.card O := by
    rw [show Nat.card O = Nat.card (CFSG.pPrimeCore 3 ↥J) from
      Subgroup.card_map_of_injective J.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hQO : Q ⊓ O = ⊥ :=
    CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hOnot h.sylow.isPGroup
  have hZSleW : (Subgroup.center ↥S).map S.subtype ≤ W := by
    have hZSleStar : (Subgroup.center ↥S).map S.subtype ≤ starCentralizer J := by
      calc (Subgroup.center ↥S).map S.subtype ≤ oTwoZStar J := by
            rw [← hSZO]
            exact inf_le_right
        _ = J ⊓ starCentralizer J := (inf_starCentralizer_eq_oTwoZStar J).symm
        _ ≤ starCentralizer J := inf_le_right
    exact le_inf (Subgroup.map_subtype_le _ |>.trans inf_le_left) hZSleStar
  have he1x3 : e1 ^ 3 = 1 := h.elem.2 e1 he1E
  have he1nonc : ∃ g ∈ S, g * e1 ≠ e1 * g := by
    by_contra hcon
    push Not at hcon
    have he1ZS : e1 ∈ (Subgroup.center ↥S).map S.subtype := by
      refine Subgroup.mem_map.mpr ⟨⟨e1, he1S⟩, ?_, rfl⟩
      exact Subgroup.mem_center_iff.mpr (fun y => Subtype.ext (hcon (y : G) y.2))
    have hmem : e1 ∈ E ⊓ W := Subgroup.mem_inf.mpr ⟨he1E, hZSleW he1ZS⟩
    rw [hEW, Subgroup.mem_bot] at hmem
    exact he1ne hmem
  have hZXcomm : ∀ z ∈ (Subgroup.center ↥S).map S.subtype, Commute e1 z := by
    rintro z ⟨z0, hz0, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz0 ⟨e1, he1S⟩)
  have hcommZ : ∀ a ∈ Subgroup.zpowers e1,
      ∀ z ∈ (Subgroup.center ↥S).map S.subtype, Commute a z := by
    intro a ha z hz
    rw [Subgroup.mem_zpowers_iff] at ha
    obtain ⟨i, rfl⟩ := ha
    exact (hZXcomm z hz).zpow_left i
  intro e2 he2
  obtain ⟨s, hsS, hw⟩ := HypCGen.exists_inner_mul_mem_starCentralizer
    h.hypCGen hLN h.isKComp (Or.inl hSL) hEN hS_sylow hES he2
  have hwQ : s⁻¹ * e2 ∈ Q :=
    Q.mul_mem (Q.inv_mem ((inf_le_left : S ≤ Q) hsS)) (h.E_le_Q he2)
  have hwW : s⁻¹ * e2 ∈ W := Subgroup.mem_inf.mpr ⟨hwQ, hw⟩
  have hwcomm : Commute (s⁻¹ * e2) e1 := by
    have hmemO : (s⁻¹ * e2) * e1 * (s⁻¹ * e2)⁻¹ * e1⁻¹ ∈ O :=
      commutator_mem_map_of_mem_quotientCentralizer (CFSG.pPrimeCore 3 ↥J)
        Subgroup.le_normalizer le_rfl hw he1S.2
    have hmemQ : (s⁻¹ * e2) * e1 * (s⁻¹ * e2)⁻¹ * e1⁻¹ ∈ Q :=
      Q.mul_mem (Q.mul_mem (Q.mul_mem hwQ ((inf_le_left : S ≤ Q) he1S)) (Q.inv_mem hwQ))
        (Q.inv_mem ((inf_le_left : S ≤ Q) he1S))
    have hbot : (s⁻¹ * e2) * e1 * (s⁻¹ * e2)⁻¹ * e1⁻¹ = 1 := by
      have hmem : (s⁻¹ * e2) * e1 * (s⁻¹ * e2)⁻¹ * e1⁻¹ ∈ Q ⊓ O :=
        Subgroup.mem_inf.mpr ⟨hmemQ, hmemO⟩
      rwa [hQO, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (by
      simpa [commutatorElement_def] using hbot)
  have hscomm : Commute s e1 := by
    have hseq : s = e2 * (s⁻¹ * e2)⁻¹ := by group
    have h_e2e1 : Commute e2 e1 := by
      refine (commute_iff_eq e2 e1).mpr ?_
      exact congrArg Subtype.val
        (h.elem.1.is_comm.comm (⟨e2, he2⟩ : ↥E) ⟨e1, he1E⟩)
    rw [hseq]
    exact h_e2e1.mul_left hwcomm.inv_left
  have hsC : s ∈ S ⊓ Subgroup.centralizer ({e1} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hsS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hscomm.eq.symm
  rw [inf_centralizer_eq_sup_zpowers_center hScard he1S he1x3 he1nonc] at hsC
  obtain ⟨a, ha, z, hz, hsa⟩ := (CFSG.mem_sup_of_commute hcommZ).mp hsC
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
  have haS : a ∈ S := (Subgroup.zpowers_le.mpr he1S) ha
  have haE : a ∈ E := by
    rw [← hi]
    exact E.zpow_mem he1E i
  have heq : e2 * a⁻¹ = z * (s⁻¹ * e2) := by
    let w : G := s⁻¹ * e2
    have hwW' : w ∈ W := hwW
    have he2s : e2 = s * w := by dsimp [w]; group
    have hs_eq : s = a * z := hsa.symm
    have haz : Commute a z := by
      obtain ⟨z0, hz0, hz0z⟩ := Subgroup.mem_map.mp hz
      rw [← hz0z]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz0 ⟨a, haS⟩)
    have haw : Commute a w := hSWcomm a haS w hwW'
    have ha_s : Commute a s := by
      rw [hs_eq]
      exact (Commute.refl a).mul_right haz
    have ha_sw : Commute a (s * w) := ha_s.mul_right haw
    calc e2 * a⁻¹ = (s * w) * a⁻¹ := by rw [he2s]
      _ = a⁻¹ * (s * w) := (ha_sw.symm.inv_right).eq
      _ = a⁻¹ * ((a * z) * w) := by rw [hs_eq]
      _ = z * w := by group
      _ = z * (s⁻¹ * e2) := rfl
  have hmemE : e2 * a⁻¹ ∈ E := E.mul_mem he2 (E.inv_mem haE)
  have hmemW : e2 * a⁻¹ ∈ W := by
    rw [heq]
    exact W.mul_mem (hZSleW hz) hwW
  have hone : e2 * a⁻¹ = 1 := by
    have hmem : e2 * a⁻¹ ∈ E ⊓ W := Subgroup.mem_inf.mpr ⟨hmemE, hmemW⟩
    rwa [hEW, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨i, by rw [hi]; exact (mul_inv_eq_one.mp hone).symm⟩

private theorem inf_E_inf_J_eq_bot
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) :
    E ⊓ (Q ⊓ J) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLN : ¬ pLayerIn 3 H ≤ M := hL 3 E H h.hypCGen
  have hEW := inf_E_inf_starCentralizer_eq_bot (Q := Q) h.hypCGen hLN h.isKComp
  have hc := commutator_inf_starCentralizer_eq_bot_of_choice h hA hpre hU
  have hSWcomm : ∀ s ∈ Q ⊓ J, ∀ w ∈ Q ⊓ starCentralizer J, Commute s w := by
    intro s hs w hw
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc.1 hs) w hw)).symm
  rw [eq_bot_iff]
  intro e1 he1
  by_contra he1ne
  obtain ⟨he1E, he1S⟩ := Subgroup.mem_inf.mp he1
  have he1x3 : e1 ^ 3 = 1 := h.elem.2 e1 he1E
  have hEle := E_le_zpowers_of_mem_inf h hA hpre hU hL he1E he1S he1ne hSWcomm hEW
  have hcardle : Nat.card E ≤ Nat.card ↥(Subgroup.zpowers e1) := Subgroup.card_le_of_le hEle
  rw [Nat.card_zpowers, orderOf_eq_prime he1x3 he1ne] at hcardle
  rw [h.card] at hcardle
  norm_num at hcardle

private theorem pow_three_of_mem_inf_starCentralizer_of_choice
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hK : IsKComp M H (kSub 3 M H)) :
    ∀ x ∈ Q ⊓ starCentralizer J, x ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  let W : Subgroup G := Q ⊓ starCentralizer J
  have hLN : ¬ pLayerIn 3 H ≤ M := hL 3 E H h.hypCGen
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hEN : E ≤ Subgroup.normalizer (J : Set G) := h.E_le_Q.trans hQN
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S J := h.isSylowOf_inf_J hpre hU
  obtain ⟨-, hSexp, -, -⟩ :=
    IsKComp.sylow_three_structure h.isKComp (Or.inl hSL) hS_sylow
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf Subgroup.le_normalizer hQN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hES : E ≤ Subgroup.normalizer (S : Set G) := h.E_le_Q.trans hQnormS
  have hcoe : ((E ⊔ S : Subgroup G) : Set G) = (E : Set G) * (S : Set G) := by
    simpa using (Subgroup.coe_mul_of_left_le_normalizer_right E S hES)
  have hc := commutator_inf_starCentralizer_eq_bot_of_choice h hA hpre hU
  have hSWcomm : ∀ s ∈ S, ∀ w ∈ W, Commute s w := by
    intro s hs w hw
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc.1 hs) w hw)).symm
  intro x hxW
  have hxQ : x ∈ Q := (Subgroup.mem_inf.mp hxW).1
  have hxES : x ∈ E ⊔ S := by
    rw [h.eq_inf_J_sup_E_of_kComp_self hpre hU hK, sup_comm] at hxQ
    exact hxQ
  change x ∈ (((E ⊔ S : Subgroup G) : Set G)) at hxES
  rw [hcoe, Set.mem_mul] at hxES
  obtain ⟨e, heE, s, hsS, hes⟩ := hxES
  obtain ⟨se, hseS, hwe⟩ := HypCGen.exists_inner_mul_mem_starCentralizer
    h.hypCGen hLN h.isKComp (Or.inl hSL) hEN hS_sylow hES heE
  have hweW : se⁻¹ * e ∈ W :=
    Subgroup.mem_inf.mpr ⟨Q.mul_mem (Q.inv_mem ((inf_le_left : S ≤ Q) hseS)) (h.E_le_Q heE), hwe⟩
  have hsep : se * (se⁻¹ * e) = e := by group
  have hx_eq : x = (se * s) * (se⁻¹ * e) := by
    calc x = e * s := hes.symm
      _ = (se * (se⁻¹ * e)) * s := by rw [hsep]
      _ = se * ((se⁻¹ * e) * s) := by group
      _ = se * (s * (se⁻¹ * e)) := by rw [(hSWcomm s hsS (se⁻¹ * e) hweW).eq.symm]
      _ = (se * s) * (se⁻¹ * e) := by group
  have hzS : se * s ∈ S := S.mul_mem hseS hsS
  have hzStar : se * s ∈ starCentralizer J := by
    have h1 : x * (se⁻¹ * e)⁻¹ ∈ starCentralizer J :=
      (starCentralizer J).mul_mem hxW.2 ((starCentralizer J).inv_mem hweW.2)
    rwa [show x * (se⁻¹ * e)⁻¹ = se * s by rw [hx_eq]; group] at h1
  have hzW : se * s ∈ W := Subgroup.mem_inf.mpr ⟨(inf_le_left : S ≤ Q) hzS, hzStar⟩
  have hzZS : se * s ∈ (Subgroup.center ↥S).map S.subtype := by
    rw [← hc.2]
    exact Subgroup.mem_inf.mpr ⟨hzS, hzW⟩
  have hwe3 : (se⁻¹ * e) ^ 3 = 1 := by
    have hcomm : Commute se (se⁻¹ * e) := hSWcomm se hseS (se⁻¹ * e) hweW
    have h1 : e ^ 3 = se ^ 3 * (se⁻¹ * e) ^ 3 := by
      conv_lhs => rw [← hsep]
      rw [hcomm.mul_pow]
    rw [h.elem.2 e heE, hSexp se hseS, one_mul] at h1
    exact h1.symm
  have hz3 : (se * s) ^ 3 = 1 := hSexp (se * s) hzS
  have hcomm2 : Commute (se * s) (se⁻¹ * e) := hSWcomm (se * s) hzS (se⁻¹ * e) hweW
  calc x ^ 3 = ((se * s) * (se⁻¹ * e)) ^ 3 := by rw [hx_eq]
    _ = (se * s) ^ 3 * (se⁻¹ * e) ^ 3 := hcomm2.mul_pow 3
    _ = 1 := by rw [hz3, hwe3, mul_one]

private theorem not_isMulCommutative_inf_starCentralizer_of_choice
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hK : IsKComp M H (kSub 3 M H)) :
    ¬ IsMulCommutative ↥(Q ⊓ starCentralizer J) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  let W : Subgroup G := Q ⊓ starCentralizer J
  let ZS : Subgroup G := (Subgroup.center ↥S).map S.subtype
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S J := h.isSylowOf_inf_J hpre hU
  obtain ⟨hScard, hSexp, hSZO, hZScard⟩ :=
    IsKComp.sylow_three_structure h.isKComp (Or.inl hSL) hS_sylow
  have hc := commutator_inf_starCentralizer_eq_bot_of_choice h hA hpre hU
  have hinfSW : S ⊓ W = ZS := hc.2
  have hZSleW : ZS ≤ W := by rw [← hinfSW]; exact inf_le_right
  have hSWcomm : ∀ s ∈ S, ∀ w ∈ W, Commute s w := by
    intro s hs w hw
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc.1 hs) w hw)).symm
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hEN : E ≤ Subgroup.normalizer (J : Set G) := h.E_le_Q.trans hQN
  have hQeq := h.eq_inf_J_sup_E_of_kComp_self hpre hU hK
  have hESW := E_le_sup_inf_starCentralizer_of_choice h hA hpre hU hL
  have hQSW : Q = S ⊔ W := by
    rw [hQeq]
    refine le_antisymm ?_ ?_
    · refine sup_le (show S ≤ S ⊔ W from le_sup_left) hESW
    · have h : S ⊔ W ≤ Q :=
        sup_le (show S ≤ Q from inf_le_left) (show W ≤ Q from inf_le_left)
      rwa [hQeq] at h
  have hESbot := inf_E_inf_J_eq_bot h hA hpre hU hL
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf Subgroup.le_normalizer hQN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hESN : E ≤ Subgroup.normalizer (S : Set G) := h.E_le_Q.trans hQnormS
  have hQcard : Nat.card Q = 3 ^ 5 :=
    card_sup_eq_pow_of_inf_eq_bot hQeq (by rw [inf_comm]; exact hESbot) hESN hScard h.card
  have hWcard : Nat.card W = 27 :=
    card_inf_starCentralizer_eq_27 hQSW (inf_le_left.trans hQnormS) hinfSW hZScard hScard hQcard
  have hWexp := pow_three_of_mem_inf_starCentralizer_of_choice h hA hpre hU hL hK
  intro hWcomm
  have hWea : CFSG.Open.IsElemAbelian 3 W := ⟨hWcomm, hWexp⟩
  have hSna : ∃ a b : ↥S, a * b ≠ b * a := exists_mul_ne_of_card_center_lt hScard hZScard
  obtain ⟨a, b, hab⟩ := hSna
  let x : G := a
  have hxS : x ∈ S := a.2
  have hx3 : x ^ 3 = 1 := hSexp x hxS
  have hxnc : ∃ g ∈ S, g * x ≠ x * g := by
    refine ⟨(b : G), b.2, ?_⟩
    intro hh
    apply hab
    apply Subtype.ext
    simpa [x] using hh.symm
  have hx1 : x ≠ 1 := by
    intro hx
    exact hab (by rw [show a = 1 from Subtype.ext hx]; simp)
  let E9 : Subgroup G := S ⊓ Subgroup.centralizer ({x} : Set G)
  have hE9card : Nat.card E9 = 9 := card_inf_centralizer_eq_nine hScard hxS hxnc
  have hE9eq : E9 = Subgroup.zpowers x ⊔ ZS :=
    inf_centralizer_eq_sup_zpowers_center hScard hxS hx3 hxnc
  have hxW : x ∉ W := by
    intro hxw
    have hxZS : x ∈ ZS := by
      rw [← hinfSW]
      exact Subgroup.mem_inf.mpr ⟨hxS, hxw⟩
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxZS
    obtain ⟨g, hgS, hgx⟩ := hxnc
    have hcentral : g * (z : G) = (z : G) * g :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hgS⟩)
    exact hgx (by rw [show (z : G) = x from hzx] at hcentral; exact hcentral)
  have hxZScomm : ∀ z ∈ ZS, Commute x z := by
    intro z hz
    obtain ⟨z0, hz0, hz0z⟩ := Subgroup.mem_map.mp hz
    rw [← hz0z]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz0 ⟨x, hxS⟩)
  have hzpcard : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hWx : W ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card ↥(W ⊓ Subgroup.zpowers x) ∣ 3 := by
      simpa [hzpcard] using Subgroup.card_dvd_of_le
        (inf_le_right : W ⊓ Subgroup.zpowers x ≤ Subgroup.zpowers x)
    have hne : Nat.card ↥(W ⊓ Subgroup.zpowers x) ≠ 3 := by
      intro h3
      have hEq : W ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hzpcard])
      have hmem : x ∈ W ⊓ Subgroup.zpowers x := by
        rw [hEq]
        exact Subgroup.mem_zpowers x
      exact hxW hmem.1
    have hcard1 : Nat.card ↥(W ⊓ Subgroup.zpowers x) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exact absurd h hne
    exact Subgroup.eq_bot_of_card_eq _ hcard1
  have hE9W : E9 ⊓ W = ZS := by
    rw [hE9eq]
    have hZN : ZS ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      have hZc : ZS ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
        rintro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        change y ∈ Subgroup.zpowers x at hy
        rw [Subgroup.mem_zpowers_iff] at hy
        obtain ⟨i, rfl⟩ := hy
        exact (hxZScomm z hz).zpow_left i |>.eq
      exact hZc.trans (Subgroup.centralizer_le_normalizer _)
    have hmod := CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer (S := ZS)
      (T := Subgroup.zpowers x) (U := W) hZSleW hZN
    rw [hWx, sup_bot_eq] at hmod
    rw [sup_comm (Subgroup.zpowers x) ZS, inf_comm]
    exact hmod
  have hE9ea : CFSG.Open.IsElemAbelian 3 E9 := by
    rw [hE9eq]
    have hZSea : CFSG.Open.IsElemAbelian 3 ZS := by
      refine ⟨?_, ?_⟩
      · refine ⟨⟨fun p q => ?_⟩⟩
        obtain ⟨p0, hp0, hp0p⟩ := Subgroup.mem_map.mp p.2
        obtain ⟨q0, hq0, hq0q⟩ := Subgroup.mem_map.mp q.2
        apply Subtype.ext
        change (p : G) * (q : G) = (q : G) * (p : G)
        rw [← hp0p, ← hq0q]
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hp0 q0)).symm
      · rintro z hz
        obtain ⟨z0, hz0, hz0z⟩ := Subgroup.mem_map.mp hz
        rw [← hz0z]
        exact hSexp (z0 : G) z0.2
    refine CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers hx3) hZSea ?_
    intro p hp z hz
    rw [Subgroup.mem_zpowers_iff] at hp
    obtain ⟨i, rfl⟩ := hp
    exact (hxZScomm z hz).zpow_left i
  have hE9Wcomm : ∀ p ∈ E9, ∀ w ∈ W, Commute p w := by
    intro p hp w hw
    exact hSWcomm p (Subgroup.mem_inf.mp hp).1 w hw
  have hea : CFSG.Open.IsElemAbelian 3 (E9 ⊔ W) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE9ea hWea (fun p hp w hw => (hE9Wcomm p hp w hw).eq)
  have hWNe : W ≤ Subgroup.normalizer (E9 : Set G) := by
    have hWc : W ≤ Subgroup.centralizer (E9 : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (hE9Wcomm p hp w hw).eq
    exact hWc.trans (Subgroup.centralizer_le_normalizer _)
  have hcard81 : Nat.card ↥(E9 ⊔ W) = 81 := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := W) (K := E9) hWNe
    rw [inf_comm W E9, hE9W, hZScard, hE9card, hWcard] at h
    rw [sup_comm W E9] at h
    have h3 : Nat.card ↥(E9 ⊔ W) * 3 = 81 * 3 := by
      rw [show (81 : ℕ) * 3 = 27 * 9 by norm_num]
      exact h
    exact Nat.mul_right_cancel (by norm_num) h3
  have hSleM : S ≤ M := inf_le_left.trans (h.Q_le_M hU)
  have hleM : E9 ⊔ W ≤ M := sup_le (inf_le_left.trans hSleM) (inf_le_left.trans (h.Q_le_M hU))
  have hrank4 : 4 ≤ CFSG.Open.pRank 3 M :=
    CFSG.SectionRank.le_pRank (by norm_num) hleM hea (by rw [hcard81]; norm_num)
  have hrank3 : CFSG.Open.pRank 3 M ≤ 3 :=
    h.cstar.pRank_le_three_of_not_mem_sigmaSet h.maxLocal Nat.prime_three (by norm_num)
      h.hypCGen.not_mem_sigmaSet
  omega

private theorem center_map_eq_of_choice
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hK : IsKComp M H (kSub 3 M H)) :
    (Subgroup.center ↥Q).map Q.subtype =
      (Subgroup.center ↥(Q ⊓ J)).map (Q ⊓ J).subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  let W : Subgroup G := Q ⊓ starCentralizer J
  let ZS : Subgroup G := (Subgroup.center ↥S).map S.subtype
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S J := h.isSylowOf_inf_J hpre hU
  obtain ⟨hScard, -, hSZO, hZScard⟩ :=
    IsKComp.sylow_three_structure h.isKComp (Or.inl hSL) hS_sylow
  have hc := commutator_inf_starCentralizer_eq_bot_of_choice h hA hpre hU
  have hinfSW : S ⊓ W = ZS := hc.2
  have hZSleW : ZS ≤ W := by rw [← hinfSW]; exact inf_le_right
  have hSWcomm : ∀ s ∈ S, ∀ w ∈ W, Commute s w := by
    intro s hs w hw
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc.1 hs) w hw)).symm
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hQeq := h.eq_inf_J_sup_E_of_kComp_self hpre hU hK
  have hESW := E_le_sup_inf_starCentralizer_of_choice h hA hpre hU hL
  have hQSW : Q = S ⊔ W := by
    rw [hQeq]
    refine le_antisymm ?_ ?_
    · refine sup_le (show S ≤ S ⊔ W from le_sup_left) hESW
    · have h : S ⊔ W ≤ Q :=
        sup_le (show S ≤ Q from inf_le_left) (show W ≤ Q from inf_le_left)
      rwa [hQeq] at h
  have hWna := not_isMulCommutative_inf_starCentralizer_of_choice h hA hpre hU hL hK
  have hWnaW : ∃ a b : ↥W, a * b ≠ b * a :=
    CFSG.Quasithin.SteinbergBK.PairedSeeds.exists_mul_ne_mul hWna
  have hESbot := inf_E_inf_J_eq_bot h hA hpre hU hL
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf Subgroup.le_normalizer hQN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hESN : E ≤ Subgroup.normalizer (S : Set G) := h.E_le_Q.trans hQnormS
  have hQcard : Nat.card Q = 3 ^ 5 :=
    card_sup_eq_pow_of_inf_eq_bot hQeq (by rw [inf_comm]; exact hESbot) hESN hScard h.card
  have hWcard : Nat.card W = 27 :=
    card_inf_starCentralizer_eq_27 hQSW (inf_le_left.trans hQnormS) hinfSW hZScard hScard hQcard
  have hZW_eq : (Subgroup.center ↥W).map W.subtype = ZS := by
    have hWZcard : Nat.card ↥((Subgroup.center ↥W).map W.subtype) = 3 := by
      rw [Subgroup.card_map_of_injective W.subtype_injective]
      exact CFSG.HardMathSupport.Solomon.Coordinator.i112v_card_center_eq_three hWcard hWnaW
    refine (Subgroup.eq_of_le_of_card_ge ?_ (by rw [hWZcard, hZScard])).symm
    rintro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hZSleW hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (hSWcomm z ((Subgroup.map_subtype_le (Subgroup.center ↥S)) hz) w w.2).eq.symm
  have hCS : Q ⊓ Subgroup.centralizer (S : Set G) = W := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxSW : x ∈ S ⊔ W := by rwa [hQSW] at hxQ
      obtain ⟨a, ha, b, hb, hab⟩ := (CFSG.mem_sup_of_commute hSWcomm).mp hxSW
      have hbC : b ∈ Subgroup.centralizer (S : Set G) :=
        Subgroup.mem_centralizer_iff.mpr (fun s hs => (hSWcomm s hs b hb).eq)
      have haC : a ∈ Subgroup.centralizer (S : Set G) := by
        have haeq : x * b⁻¹ = a := by rw [← hab]; group
        rw [← haeq]
        exact (Subgroup.centralizer (S : Set G)).mul_mem hxC
          ((Subgroup.centralizer (S : Set G)).inv_mem hbC)
      have haZS : a ∈ ZS := by
        refine Subgroup.mem_map.mpr ⟨⟨a, ha⟩, ?_, rfl⟩
        exact Subgroup.mem_center_iff.mpr (fun y =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp haC (y : G) y.2))
      rw [← hab]
      exact W.mul_mem (hZSleW haZS) hb
    · intro w hw
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).1, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun s hs => (hSWcomm s hs w hw).eq)
  rw [← CFSG.GroupTheory.inf_centralizer_eq_map_center (L := Q)]
  conv_lhs => rw [hQSW]
  rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer, ← inf_assoc]
  have hCS' : (S ⊔ W) ⊓ Subgroup.centralizer (S : Set G) = W := by
    rw [← hQSW]
    exact hCS
  rw [hCS']
  rw [CFSG.GroupTheory.inf_centralizer_eq_map_center (L := W), hZW_eq]

private theorem commutator_eq_center_map_of_choice
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hK : IsKComp M H (kSub 3 M H)) :
    ⁅Q, Q⁆ = (Subgroup.center ↥(Q ⊓ J)).map (Q ⊓ J).subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  let W : Subgroup G := Q ⊓ starCentralizer J
  let ZS : Subgroup G := (Subgroup.center ↥S).map S.subtype
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S J := h.isSylowOf_inf_J hpre hU
  obtain ⟨hScard, -, hSZO, hZScard⟩ :=
    IsKComp.sylow_three_structure h.isKComp (Or.inl hSL) hS_sylow
  have hc := commutator_inf_starCentralizer_eq_bot_of_choice h hA hpre hU
  have hinfSW : S ⊓ W = ZS := hc.2
  have hZSleW : ZS ≤ W := by rw [← hinfSW]; exact inf_le_right
  have hSWcomm : ∀ s ∈ S, ∀ w ∈ W, Commute s w := by
    intro s hs w hw
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc.1 hs) w hw)).symm
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hQeq := h.eq_inf_J_sup_E_of_kComp_self hpre hU hK
  have hESW := E_le_sup_inf_starCentralizer_of_choice h hA hpre hU hL
  have hQSW : Q = S ⊔ W := by
    rw [hQeq]
    refine le_antisymm ?_ ?_
    · refine sup_le (show S ≤ S ⊔ W from le_sup_left) hESW
    · have h : S ⊔ W ≤ Q :=
        sup_le (show S ≤ Q from inf_le_left) (show W ≤ Q from inf_le_left)
      rwa [hQeq] at h
  have hWna := not_isMulCommutative_inf_starCentralizer_of_choice h hA hpre hU hL hK
  have hWnaW : ∃ a b : ↥W, a * b ≠ b * a :=
    CFSG.Quasithin.SteinbergBK.PairedSeeds.exists_mul_ne_mul hWna
  have hESbot := inf_E_inf_J_eq_bot h hA hpre hU hL
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf Subgroup.le_normalizer hQN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hESN : E ≤ Subgroup.normalizer (S : Set G) := h.E_le_Q.trans hQnormS
  have hQcard : Nat.card Q = 3 ^ 5 :=
    card_sup_eq_pow_of_inf_eq_bot hQeq (by rw [inf_comm]; exact hESbot) hESN hScard h.card
  have hWcard : Nat.card W = 27 :=
    card_inf_starCentralizer_eq_27 hQSW (inf_le_left.trans hQnormS) hinfSW hZScard hScard hQcard
  have hZW_eq : (Subgroup.center ↥W).map W.subtype = ZS := by
    have hWZcard : Nat.card ↥((Subgroup.center ↥W).map W.subtype) = 3 := by
      rw [Subgroup.card_map_of_injective W.subtype_injective]
      exact CFSG.HardMathSupport.Solomon.Coordinator.i112v_card_center_eq_three hWcard hWnaW
    refine (Subgroup.eq_of_le_of_card_ge ?_ (by rw [hWZcard, hZScard])).symm
    rintro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hZSleW hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (hSWcomm z ((Subgroup.map_subtype_le (Subgroup.center ↥S)) hz) w w.2).eq.symm
  have hSna : ∃ a b : ↥S, a * b ≠ b * a := exists_mul_ne_of_card_center_lt hScard hZScard
  have hSS : ⁅S, S⁆ = ZS := commutator_eq_center_map_of_card_27 hScard hSna
  have hWW : ⁅W, W⁆ = ZS := by
    rw [commutator_eq_center_map_of_card_27 hWcard hWnaW, hZW_eq]
  have hZScentral : ∀ z ∈ ZS, ∀ q ∈ S ⊔ W, Commute z q := by
    intro z hz q hq
    obtain ⟨s, hs, w, hw, hsw⟩ := (CFSG.mem_sup_of_commute hSWcomm).mp hq
    obtain ⟨z0, hz0, hz0z⟩ := Subgroup.mem_map.mp hz
    rw [← hz0z, ← hsw]
    have hzs : Commute (z0 : G) s :=
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz0 ⟨s, hs⟩)).symm
    have hzw : Commute (z0 : G) w := hSWcomm z0 z0.2 w hw
    exact hzs.mul_right hzw
  have hle : ⁅S ⊔ W, S ⊔ W⁆ ≤ ZS :=
    commutator_sup_le_of_commute_le hSWcomm (le_of_eq hSS) (le_of_eq hWW) hZScentral
  have hge : ZS ≤ ⁅S ⊔ W, S ⊔ W⁆ := by
    rw [← hSS]
    exact Subgroup.commutator_mono (show S ≤ S ⊔ W from le_sup_left)
      (show S ≤ S ⊔ W from le_sup_left)
  have hQQ : ⁅Q, Q⁆ = ⁅S ⊔ W, S ⊔ W⁆ := by rw [hQSW]
  exact hQQ.trans (le_antisymm hle hge)

private theorem commutator_inf_starCentralizer_le_pCoreOf
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) :
    ⁅Q ⊓ starCentralizer J, J⁆ ≤ CFSG.Open.pCoreOf 2 J := by
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hOeq : CFSG.Open.pCoreOf 2 J = (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
    rw [CFSG.openPCoreOf_eq_map_pCore,
      pCore_two_eq_pPrimeCore_three_of_isL34Type h.J_comp.2.2.1 hSL.1]
  rw [hOeq, Subgroup.commutator_le]
  intro w hw j hj
  exact commutator_mem_map_of_mem_quotientCentralizer (CFSG.pPrimeCore 3 ↥J)
    Subgroup.le_normalizer le_rfl hw.2 hj

theorem S14Choice.fourteenTwo_of_kComp_self
    (h : S14Choice G M H E Q J) (hA : TypeA M H)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hK : IsKComp M H (kSub 3 M H)) : FourteenTwoConcl Q J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  let W : Subgroup G := Q ⊓ starCentralizer J
  let ZS : Subgroup G := (Subgroup.center ↥S).map S.subtype
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S J := h.isSylowOf_inf_J hpre hU
  obtain ⟨hScard, hSexp, hSZO, hZScard⟩ :=
    IsKComp.sylow_three_structure h.isKComp (Or.inl hSL) hS_sylow
  have hQeq := h.eq_inf_J_sup_E_of_kComp_self hpre hU hK
  have hESbot := inf_E_inf_J_eq_bot h hA hpre hU hL
  have hc := commutator_inf_starCentralizer_eq_bot_of_choice h hA hpre hU
  have hinfSW : S ⊓ W = ZS := hc.2
  have hSWcomm : ∀ s ∈ S, ∀ w ∈ W, Commute s w := by
    intro s hs w hw
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc.1 hs) w hw)).symm
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf Subgroup.le_normalizer hQN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hESN : E ≤ Subgroup.normalizer (S : Set G) := h.E_le_Q.trans hQnormS
  have hQcard : Nat.card Q = 3 ^ 5 :=
    card_sup_eq_pow_of_inf_eq_bot hQeq (by rw [inf_comm]; exact hESbot) hESN hScard h.card
  have hESW := E_le_sup_inf_starCentralizer_of_choice h hA hpre hU hL
  have hQSW : Q = S ⊔ W := by
    rw [hQeq]
    refine le_antisymm ?_ ?_
    · refine sup_le (show S ≤ S ⊔ W from le_sup_left) hESW
    · have h : S ⊔ W ≤ Q :=
        sup_le (show S ≤ Q from inf_le_left) (show W ≤ Q from inf_le_left)
      rwa [hQeq] at h
  have hWcard : Nat.card W = 27 :=
    card_inf_starCentralizer_eq_27 hQSW (inf_le_left.trans hQnormS) hinfSW hZScard hScard hQcard
  have hWexp := pow_three_of_mem_inf_starCentralizer_of_choice h hA hpre hU hL hK
  have hQexp : ∀ x ∈ Q, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ S ⊔ W := by rw [← hQSW]; exact hx
    obtain ⟨s, hs, w, hw, hsw⟩ := (CFSG.mem_sup_of_commute hSWcomm).mp hx'
    calc x ^ 3 = (s * w) ^ 3 := by rw [hsw]
      _ = s ^ 3 * w ^ 3 := (hSWcomm s hs w hw).mul_pow 3
      _ = 1 := by rw [hSexp s hs, hWexp w hw, mul_one]
  have hZQ := center_map_eq_of_choice h hA hpre hU hL hK
  have hQQ := commutator_eq_center_map_of_choice h hA hpre hU hL hK
  have hWJ := commutator_inf_starCentralizer_le_pCoreOf h hA hpre hU
  have hZSleW : ZS ≤ W := by rw [← hinfSW]; exact inf_le_right
  refine ⟨⟨hQcard, hQexp, ?_, ?_⟩, W, inf_le_left, hWcard, hWJ, ?_⟩
  · rw [hQQ, hZQ]
  · rw [hZQ]
    exact hZScard
  · rw [hZQ]
    exact hZSleW

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
