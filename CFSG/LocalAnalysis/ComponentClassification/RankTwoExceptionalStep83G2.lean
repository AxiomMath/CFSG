module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83Basic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Inner
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverLevi
public import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCover
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.LieType.Chevalley.C2E6A5ExteriorCubeModel
public import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicKernel
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Timmesfeld.ARS.Sec5Ten
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Step83Proof

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.Chevalley.G2FieldFour
open CFSG.EvenSmallLie.GTwoFour
open CFSG.EvenSmallLie.TwoE6 (oddPart mem_oddPart oddPart_le lift_oddPart eq_one_of_odd_orderOf)
open scoped commutatorElement

section Cover

theorem eq_or_eq_of_card_le_two {H : Type*} [Finite H] (hH : Nat.card H ≤ 2) {a b : H}
    (hab : a ≠ b) (c : H) : c = a ∨ c = b := by
  by_contra h
  push Not at h
  have := Fintype.ofFinite H
  have h3 : 2 < Fintype.card H :=
    Fintype.two_lt_card_iff.mpr ⟨a, b, c, hab, Ne.symm h.1, Ne.symm h.2⟩
  rw [Nat.card_eq_fintype_card] at hH
  omega

variable {K : Type} [Field K] [CharP K 2]

theorem commutatorElement_eq_of_rootX_v
    (hK : Nat.card K = 4) {M : Type*} [Group M] [Finite M] [Group.IsPerfect M]
    {π : M →* adjointGroup .G2 K} (hπ : Function.Surjective π)
    (hker : ∀ k, π k = 1 → k ∈ center M) {z : M} (hz1 : z ≠ 1)
    (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z) {s : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {m m' : M}
    (hm : π m = rootX rootV 1) (hm' : π m' = rootX rootV s) : ⁅m', m⁆ = z := by
  have hsq : ∀ {x : M} {c : K}, c ≠ 0 → π x = rootX rootV c → x * x = z := fun {x c} hc hx =>
    mul_self_eq_of_isConj_rootX_v hz1 hz hK hπ hker
      (by rw [hx]; exact isConj_of_g2Conj (G2Conj.v_one hc))
  have h1 : m * m = z := hsq one_ne_zero hm
  have h2 : m' * m' = z := hsq hs0 hm'
  have hs1' : s + 1 ≠ 0 := fun h =>
    hs1 ((eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq 1))
  have h3 : (m' * m) * (m' * m) = z := hsq hs1' (by rw [map_mul, hm', hm, ← rootX_add])
  have hzc : z ∈ center M := hker z ((hz z).2 (Or.inr rfl))
  have he : ⁅m', m⁆ * (m * m') = m' * m := by rw [commutatorElement_def]; group
  have h4 : (m' * m) * (m' * m) = ⁅m', m⁆ := by
    calc (m' * m) * (m' * m) = (⁅m', m⁆ * (m * m')) * (m' * m) := by rw [he]
      _ = ⁅m', m⁆ * (m * (m' * m') * m) := by group
      _ = ⁅m', m⁆ * (z * (m * m)) := by rw [h2, mem_center_iff.1 hzc m, mul_assoc]
      _ = ⁅m', m⁆ := by rw [h1, mul_self_z hz1 hz, mul_one]
  exact h4.symm.trans h3

theorem card_ker_le_two
    (hK : Nat.card K = 4) {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    {π : B →* adjointGroup .G2 K} (hπ : Function.Surjective π) (hker : π.ker ≤ center B)
    (h2 : IsPGroup 2 π.ker) : Nat.card π.ker ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ω, hω1, -, -⟩ := exists_unit_ne_one hK
  obtain ⟨x₁, hx₁⟩ := hπ (rootX rootV 1)
  obtain ⟨xω, hxω⟩ := hπ (rootX rootV (ω : K))
  set e := ⁅xω, x₁⁆ with he_def
  have heC : e ∈ π.ker := by
    rw [MonoidHom.mem_ker, he_def, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
      hx₁, hxω, ← rootX_add, ← rootX_add, add_comm]
  have hx₁C : x₁ * x₁ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, hx₁, ← rootX_add, CharTwo.add_self_eq_zero, rootX_zero]
  have he2 : e ^ 2 = 1 := by
    have h1 : e * x₁ = xω * x₁ * xω⁻¹ := by rw [he_def, commutatorElement_def]; group
    have h3 : (xω * x₁ * xω⁻¹) * (xω * x₁ * xω⁻¹) = x₁ * x₁ := by
      rw [show (xω * x₁ * xω⁻¹) * (xω * x₁ * xω⁻¹) = xω * (x₁ * x₁) * xω⁻¹ by group,
        mem_center_iff.1 (hker hx₁C) xω, mul_inv_cancel_right]
    rw [← h1, show (e * x₁) * (e * x₁) = e * (x₁ * e) * x₁ by group,
      mem_center_iff.1 (hker heC) x₁, show e * (e * x₁) * x₁ = e * e * (x₁ * x₁) by group] at h3
    rw [sq]
    exact mul_eq_right.mp h3
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hn2 : 2 ≤ n := by
    rw [hn] at hlt
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num at hlt
    · exact h
  obtain ⟨H, hHcard, heH, hHC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (n := n - 1)
    Nat.prime_two (H := zpowers e) (L := π.ker)
    (by
      rw [Nat.card_zpowers]
      exact (orderOf_dvd_of_pow_eq_one he2).trans (dvd_pow_self 2 (by omega)))
    (by rw [hn]; exact pow_dvd_pow 2 (Nat.sub_le n 1))
    (zpowers_le.mpr heC)
  have hHZ : H ≤ center B := hHC.trans hker
  have hHn : H.Normal := ⟨fun a ha b => by
    rw [mem_center_iff.1 (hHZ ha) b, mul_inv_cancel_right]; exact ha⟩
  have hidx : (H.subgroupOf π.ker).index = 2 := by
    have h1 := (H.subgroupOf π.ker).card_mul_index
    have h2n : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [Nat.card_congr (subgroupOfEquivOfLe hHC).toEquiv, hHcard, hn, h2n] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  obtain ⟨z₀, hz₀C, hz₀H⟩ : ∃ z₀ ∈ π.ker, z₀ ∉ H := by
    by_contra h
    push Not at h
    have h3 := Subgroup.card_le_of_le (fun x hx => h x hx : π.ker ≤ H)
    rw [hn, hHcard] at h3
    exact absurd h3 (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  set π' : B ⧸ H →* adjointGroup .G2 K := QuotientGroup.lift H π hHC with hπ'def
  have hπ'mk : ∀ x : B, π' (x : B ⧸ H) = π x := fun x => QuotientGroup.lift_mk _ _ _
  have hπ's : Function.Surjective π' := fun y => by
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨x, hπ'mk x⟩
  have hz1 : ((z₀ : B) : B ⧸ H) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]; exact hz₀H
  have hz : ∀ k : B ⧸ H, π' k = 1 ↔ k = 1 ∨ k = (z₀ : B ⧸ H) := by
    intro k
    induction k using QuotientGroup.induction_on with
    | H x =>
      rw [hπ'mk]
      constructor
      · intro hx
        have hxk : x ∈ π.ker := MonoidHom.mem_ker.mpr hx
        by_cases hxH : x ∈ H
        · exact Or.inl ((QuotientGroup.eq_one_iff x).mpr hxH)
        · refine Or.inr (QuotientGroup.eq.mpr ?_)
          have ha : (⟨x⁻¹, inv_mem hxk⟩ : π.ker) ∉ H.subgroupOf π.ker := by
            rw [mem_subgroupOf]
            exact fun h => hxH (by simpa using inv_mem h)
          have hb : (⟨z₀, hz₀C⟩ : π.ker) ∉ H.subgroupOf π.ker := by
            rw [mem_subgroupOf]; exact hz₀H
          have key := (mul_mem_iff_of_index_two hidx).mpr (iff_of_false ha hb)
          rw [mem_subgroupOf] at key
          exact key
      · rintro (h | h)
        · rw [← hπ'mk, h, map_one]
        · rw [← hπ'mk, h, hπ'mk]
          exact MonoidHom.mem_ker.mp hz₀C
  have hzc : ((z₀ : B) : B ⧸ H) ∈ center (B ⧸ H) := by
    rw [mem_center_iff]
    intro w
    induction w using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 (hker hz₀C) w]
  have hker' : ∀ k, π' k = 1 → k ∈ center (B ⧸ H) := fun k hk => by
    rcases (hz k).1 hk with rfl | rfl
    · exact one_mem _
    · exact hzc
  have hcomm := commutatorElement_eq_of_rootX_v hK hπ's hker' hz1 hz ω.ne_zero hω1
    (m := (x₁ : B ⧸ H)) (m' := (xω : B ⧸ H)) (by rw [hπ'mk, hx₁]) (by rw [hπ'mk, hxω])
  apply hz1
  rw [← hcomm]
  change ⁅QuotientGroup.mk' H xω, QuotientGroup.mk' H x₁⁆ = 1
  rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact heH (mem_zpowers e)

theorem exists_center_eq
    {B : Type} [Group B] [Finite B] (hperf : commutator B = ⊤)
    (hS : ChevalleyExceptionalModel (B ⧸ center B) .G2 2 2)
    (heven : Even (Nat.card (center B))) :
    ∃ z : B, z ≠ 1 ∧ ∀ w : B, w ∈ center B ↔ w = 1 ∨ w = z := by
  have : Group.IsPerfect B := Group.isPerfect_def.2 hperf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := id hS
  have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hZX := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  set ι : B ⧸ center B ≃* adjointGroup .G2 K :=
    eS.trans ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot)
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  set z : B := (z₀ : B) with hz_def
  have hzc : z ∈ center B := z₀.2
  have hz2 : orderOf z = 2 := by rw [hz_def, Subgroup.orderOf_coe, hz₀]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; norm_num at hz2
  have hzz : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  set φ₀ := QuotientGroup.mk' (center B) with hφ₀
  have hZ : φ₀.ker ≤ center B := (QuotientGroup.ker_mk' _).le
  obtain ⟨hψs, hψc, hψ2⟩ := lift_oddPart φ₀ (QuotientGroup.mk'_surjective _) hZ
  set O := oddPart φ₀.ker hZ with hOdef
  set ψ := QuotientGroup.lift O φ₀ oddPart_le with hψdef
  have hcard : Nat.card ψ.ker ≤ 2 := by
    have h := card_ker_le_two hK4 (π := ι.toMonoidHom.comp ψ) (ι.surjective.comp hψs)
      (by rw [CFSG.SectionRank.ker_mulEquiv_comp]; exact hψc)
      (by rw [CFSG.SectionRank.ker_mulEquiv_comp]; exact hψ2)
    rwa [CFSG.SectionRank.ker_mulEquiv_comp] at h
  have hO : ∀ w : B, w ∈ O ↔ w ∈ center B ∧ Odd (orderOf w) := fun w => by
    rw [hOdef, mem_oddPart, MonoidHom.mem_ker, hφ₀, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hmem : ∀ v ∈ center B, (v : B ⧸ O) ∈ ψ.ker := fun v hv => by
    rw [MonoidHom.mem_ker, hψdef, QuotientGroup.lift_mk, hφ₀, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hv
  have hzO : (z : B ⧸ O) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, hO]
    rintro ⟨-, hodd⟩
    rw [hz2] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have hne : (⟨1, one_mem _⟩ : ψ.ker) ≠ ⟨(z : B ⧸ O), hmem z hzc⟩ := fun h =>
    hzO (congrArg Subtype.val h).symm
  have h2el : ∀ w ∈ center B, ∀ k : ℕ, w ^ 2 ^ k = 1 → w = 1 ∨ w = z := by
    intro w hw k hk
    rcases eq_or_eq_of_card_le_two hcard hne ⟨(w : B ⧸ O), hmem w hw⟩ with h | h
    · left
      have h' : (w : B ⧸ O) = 1 := congrArg Subtype.val h
      rw [QuotientGroup.eq_one_iff, hO] at h'
      exact eq_one_of_odd_orderOf h'.2 hk
    · right
      have h' : (w : B ⧸ O) = z := congrArg Subtype.val h
      rw [QuotientGroup.eq, hO] at h'
      have hcz : Commute w⁻¹ z := mem_center_iff.1 hzc w⁻¹
      have hw' : w ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
      have hz' : z ^ 2 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, hzz, one_pow]
      have h1 := eq_one_of_odd_orderOf h'.2 (k := k + 1)
        (by rw [hcz.mul_pow, inv_pow, hw', inv_one, one_mul, hz'])
      exact inv_mul_eq_one.mp h1
  have hNZ : zpowers z ≤ center B := zpowers_le.mpr hzc
  have hNn : (zpowers z).Normal := ⟨fun a ha b => by
    rw [mem_center_iff.1 (hNZ ha) b, mul_inv_cancel_right]; exact ha⟩
  have hNk : zpowers z ≤ φ₀.ker := by rw [QuotientGroup.ker_mk']; exact hNZ
  set χ := QuotientGroup.lift (zpowers z) φ₀ hNk with hχdef
  have hχmk : ∀ x : B, χ (x : B ⧸ zpowers z) = φ₀ x := fun x => QuotientGroup.lift_mk _ _ _
  have hχs : Function.Surjective χ := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center B) y
    exact ⟨x, hχmk x⟩
  have hχ1 : ∀ x : B, χ (x : B ⧸ zpowers z) = 1 ↔ x ∈ center B := fun x => by
    rw [hχmk, hφ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hNmem : ∀ v ∈ zpowers z, v ^ 2 ^ 1 = 1 := fun v hv => by
    rw [pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hv).trans hz2.dvd)
  have hχc : χ.ker ≤ center (B ⧸ zpowers z) := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [MonoidHom.mem_ker, hχ1] at hx
      rw [mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H y => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 hx y]
  have hχodd : Odd (Nat.card χ.ker) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (x : B ⧸ zpowers z)
    have hwZ : w ∈ center B := by
      rw [← hχ1, hw]; exact x.2
    have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hw2 : w ^ 2 ∈ zpowers z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hw, ← Subgroup.coe_pow, hx2,
        Subgroup.coe_one]
    have hw4 : w ^ 2 ^ 2 = 1 := by
      rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul]
      simpa using hNmem _ hw2
    have hx1 : x = 1 := by
      apply Subtype.ext
      rw [OneMemClass.coe_one, ← hw, QuotientGroup.eq_one_iff]
      rcases h2el w hwZ 2 hw4 with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers z
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  have hχbot := CFSG.SectionRank.g2_even_perfect_odd_cover_trivial hS χ hχs hχc hχodd
  refine ⟨z, hz1, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have hwN : (w : B ⧸ zpowers z) ∈ χ.ker := (hχ1 w).mpr hw
    rw [hχbot, mem_bot, QuotientGroup.eq_one_iff] at hwN
    exact h2el w hw 1 (hNmem w hwN)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact hzc

theorem mem_of_card_eq
    [Finite K] (hK : Nat.card K = 4) {M : Type*} [Group M] [Finite M]
    {π : M →* adjointGroup .G2 K} {z : M} (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z)
    {S : Subgroup M} (hS : Nat.card S = 2 ^ 13) : z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hzS
  have hinj : Function.Injective (π.comp S.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs
    rcases (hz _).1 hs with h | h
    · exact mem_bot.mpr (Subtype.ext h)
    · exact absurd (h ▸ s.2) hzS
  have hP : Nat.card (π.comp S.subtype).range = 2 ^ 13 := by
    rw [← hS]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hP2 : IsPGroup 2 (π.comp S.subtype).range := IsPGroup.of_card hP
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element .G2
  obtain ⟨U₀, hU₀⟩ := (exceptional_ordinary_Sylow_opposition .G2 K 2 w₀ hw₀).1
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup .G2 K) U₀ Q
  have hQ : Nat.card (Q : Subgroup (adjointGroup .G2 K)) = 2 ^ 12 := by
    rw [← hc, coe_smul_sylow_eq_map, hU₀, card_map_of_injective (MulAut.conj c).injective,
      card_posU hK]
  have h := Subgroup.card_le_of_le hPQ
  rw [hP, hQ] at h
  norm_num at h

end Cover

section Main

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

theorem odd_card_center_of_G2
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (hc : Sec3 A R T g)
    (hS : ChevalleyExceptionalModel (rankTwoQuot A) .G2 2 2) : Odd (Nat.card (center A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : commutator ↥A = ⊤ := hc.hyp.standard.1.1
  have : Group.IsPerfect ↥A := Group.isPerfect_def.2 hperf
  have hOut := odd_card_commutator_outer_of_quot hperf (odd_card_commutator_outer_G2 le_rfl hS)
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨z₀, hz₀1, hZ⟩ := exists_center_eq hperf hS hodd
  obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := hS
  have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hZX := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  set ι : rankTwoQuot A ≃* adjointGroup .G2 K :=
    eS.trans ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot)
  set π : ↥A →* adjointGroup .G2 K := ι.toMonoidHom.comp (QuotientGroup.mk' (center ↥A))
    with hπdef
  have hπs : Function.Surjective π := ι.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπ1 : ∀ a : ↥A, π a = 1 ↔ a ∈ center ↥A := fun a => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z₀ := fun k => (hπ1 k).trans (hZ k)
  have hker : ∀ k, π k = 1 → k ∈ center ↥A := fun k hk => (hπ1 k).1 hk
  have hz₀c : z₀ ∈ center ↥A := (hZ z₀).2 (Or.inr rfl)
  have hz₀K : ((z₀ : ↥A) : G) ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (mem_center_iff.1 hz₀c ⟨a, ha⟩)
  obtain ⟨t, ht, ht1⟩ := T.bot_or_exists_ne_one.resolve_left hc.T_ne_bot
  obtain ⟨p, hp, hρ⟩ := hc.exists_aPart h32 h4 h34 ht
  set pA : ↥A := ⟨p, hp⟩ with hpA
  have hpp : pA * pA = 1 := Subtype.ext (Sec3.aPart_mul_self hc h32 ht hρ)
  have hπp : π pA ≠ 1 := by
    intro h
    have hpZ := (hπ1 pA).1 h
    have hpK : p ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      exact congrArg Subtype.val (mem_center_iff.1 hpZ ⟨a, ha⟩)
    have htK : t ∈ T ⊓ centralizer (A : Set G) := by
      refine mem_inf.mpr ⟨ht, ?_⟩
      rw [show t = p * (t⁻¹ * p)⁻¹ by group]
      exact mul_mem hpK (inv_mem (hc.sylowR.le hρ))
    rw [Sec3.inf_centralizer_eq_bot hc, mem_bot] at htK
    exact ht1 htK
  have hπp2 : orderOf (π pA) = 2 := orderOf_eq_prime (by rw [sq, ← map_mul, hpp, map_one]) hπp
  have hconj : IsConj (π pA) (rootX rootC 1) := by
    rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) _ hπp2 with h | h
    · exact h
    · exfalso
      have h' := mul_self_eq_of_isConj_rootX_v hz₀1 hz hK4 hπs hker h
      rw [hpp] at h'
      exact hz₀1 h'.symm
  obtain ⟨k, hk⟩ := isConj_iff.1 hconj.symm
  set Z : Subgroup (adjointGroup .G2 K) := centralizer {π pA} with hZdef
  have hZ' : Z = (centralizer {rootX rootC (1 : K)}).map (MulAut.conj k).toMonoidHom := by
    rw [hZdef, ← hk, Setup.centralizer_conj]
  have hZperf : ⁅Z, Z⁆ = Z := by
    rw [hZ', ← map_commutator, commutator_centralizer_rootX_c hK4]
  obtain ⟨m₀, hm₀⟩ := hπs (k * rootX rootV 1 * k⁻¹)
  have hm₀Z : π m₀ ∈ Z := by
    rw [hm₀, hZ']
    exact ⟨_, rootX_v_mem_centralizer_c, rfl⟩
  have hm₀2 : m₀ * m₀ = z₀ :=
    mul_self_eq_of_isConj_rootX_v hz₀1 hz hK4 hπs hker
      (by rw [hm₀]; exact isConj_iff.2 ⟨k⁻¹, by group⟩)
  set C := Z.comap π with hCdef
  have hCperf : ⁅C, C⁆ = C := commutator_comap_eq hπs hz₀1 hz hker hZperf hm₀Z hm₀2
  have hCp : C ≤ centralizer {pA} := by
    rw [← hCperf]
    exact commutator_comap_le_centralizer hker pA
  have hCG : C.map A.subtype ≤ rightConjugate A g := by
    have hCt : C.map A.subtype ≤ A ⊓ centralizer ({t} : Set G) := by
      rw [Sec3.inf_centralizer_eq hc hρ]
      rintro _ ⟨x, hx, rfl⟩
      refine mem_inf.mpr ⟨x.2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hCp hx))
    have hperfG : ⁅C.map A.subtype, C.map A.subtype⁆ = C.map A.subtype := by
      rw [← map_commutator, hCperf]
    have hX : C.map A.subtype ≤ oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆ :=
      calc C.map A.subtype = ⁅C.map A.subtype, C.map A.subtype⁆ := hperfG.symm
        _ ≤ ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆ :=
          commutator_mono hCt hCt
        _ ≤ _ := le_sup_right
    exact (le_admResidual_of_perfect hX hperfG).trans
      (Lemma39.lemma39_one h4 h32 h34 hc.hyp hc.sylowT ht ht1 hOut).1
  set Ut := (posU K).map (MulAut.conj k).toMonoidHom with hUt
  have hUtZ : Ut ≤ Z := by
    rw [hUt, hZ']
    exact map_mono posU_le_centralizer_c
  set SL := Ut.comap π with hSL
  have hSLC : SL ≤ C := comap_mono hUtZ
  have hz₀SL : z₀ ∈ SL := by
    rw [hSL, mem_comap, (hz z₀).2 (Or.inr rfl)]
    exact one_mem _
  have hpSL : pA ∈ SL := by
    rw [hSL, mem_comap, ← hk]
    exact ⟨_, rootX_mem_posU rootC_mem 1, rfl⟩
  have hcardSL : Nat.card SL = 2 ^ 13 := by
    have h1 := card_le_two_mul hπs hz SL (fun _ => True)
    have h2 := two_mul_card_le hz hz₀1 SL hz₀SL (fun _ => True)
    have e1 : Nat.card {s : SL // True} = Nat.card SL :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
    have e2 : Nat.card {q // q ∈ SL.map π ∧ True} = Nat.card Ut := by
      rw [hSL, map_comap_eq_self_of_surjective hπs]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun q => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩)
    have hUtcard : Nat.card Ut = 2 ^ 12 := by
      rw [hUt, card_map_of_injective (MulAut.conj k).injective, card_posU hK4]
    rw [e1, e2, hUtcard] at h1 h2
    omega
  have hpc : (⟨pA, hpSL⟩ : SL) ∈ center SL := Subgroup.mem_center_iff.2 fun s => Subtype.ext (by
    have h := mem_centralizer_singleton_iff.1 (hCp (hSLC s.2))
    exact h)
  obtain ⟨-, h576⟩ := card_sq_lt hK4 hπs hz₀1 hz hker hz₀SL hcardSL hpc hπp
  have hconjA : ∀ s ∈ SL, g * ((s : ↥A) : G) * g⁻¹ ∈ A := fun s hs => by
    have h := hCG ⟨s, hSLC hs, rfl⟩
    rwa [mem_rightConjugate_iff] at h
  let ψ : SL →* ↥A :=
    { toFun := fun s => ⟨g * ((s : ↥A) : G) * g⁻¹, hconjA s s.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s s' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hψinj : Function.Injective ψ := fun s s' h => by
    have h' := congrArg (fun x : ↥A => (x : G)) h
    change g * ((s : ↥A) : G) * g⁻¹ = g * ((s' : ↥A) : G) * g⁻¹ at h'
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel h')))
  let e : SL ≃* ψ.range := MonoidHom.ofInjective hψinj
  have he : ∀ s : SL, ((e s : ψ.range) : ↥A) = ψ s := fun s => rfl
  have hcardS₁ : Nat.card ψ.range = 2 ^ 13 := by rw [← Nat.card_congr e.toEquiv, hcardSL]
  have hz₀S₁ : z₀ ∈ ψ.range := mem_of_card_eq hK4 hz hcardS₁
  have hac : e ⟨z₀, hz₀SL⟩ ∈ center ψ.range := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨s, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz₀c s)
  have hπa : π (e ⟨z₀, hz₀SL⟩) ≠ 1 := by
    rw [he]
    intro h
    have hg : g * ((z₀ : ↥A) : G) * g⁻¹ = 1 ∨ g * ((z₀ : ↥A) : G) * g⁻¹ = z₀ := by
      rcases (hz _).1 h with h' | h'
      · exact Or.inl (congrArg Subtype.val h')
      · exact Or.inr (congrArg Subtype.val h')
    rcases hg with h' | h'
    · apply hz₀1
      apply Subtype.ext
      change ((z₀ : ↥A) : G) = 1
      rw [show ((z₀ : ↥A) : G) = g⁻¹ * (g * z₀ * g⁻¹) * g by group, h', mul_one,
        inv_mul_cancel]
    · have hzT := Sec3.conj_mem_of_mem_center hc z₀.2 hz₀K (k := 1)
        (by rw [pow_one, sq]; exact congrArg Subtype.val (mul_self_z hz₀1 hz))
      have h'' : g⁻¹ * ((z₀ : ↥A) : G) * g = z₀ := by
        calc g⁻¹ * ((z₀ : ↥A) : G) * g = g⁻¹ * (g * z₀ * g⁻¹) * g := by rw [h']
          _ = z₀ := by group
      rw [h''] at hzT
      have hzTK : ((z₀ : ↥A) : G) ∈ T ⊓ centralizer (A : Set G) := mem_inf.mpr ⟨hzT, hz₀K⟩
      rw [Sec3.inf_centralizer_eq_bot hc, mem_bot] at hzTK
      exact hz₀1 (Subtype.ext hzTK)
  obtain ⟨h480, -⟩ := card_sq_lt hK4 hπs hz₀1 hz hker hz₀S₁ hcardS₁ hac hπa
  rw [← card_sq_eq_of_mulEquiv e] at h480
  omega

end Main

end CFSG.ComponentClassification.RankTwoExceptional.Step83Proof
