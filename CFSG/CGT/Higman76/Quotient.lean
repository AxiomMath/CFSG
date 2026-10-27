module

public import CFSG.CGT.Higman76.Setup
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.Assembly.Defs
public import CFSG.Models.BenderSuzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.SteinbergBVA7OddQuotientIndexTwo
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelInvolutionFusion
import CFSG.GroupTheory.CardMapInfKer
import CFSG.Goldschmidt75.Sec42Bender
import CFSG.Walter.W67.W1Prop24B
import CFSG.CharacterTheory.Wreathed.InvolutionInducedCharactersSupport
import CFSG.CharacterTheory.Semidihedral.ParameterFiveGeneration

public section

namespace CFSG.CGT.Higman76

open Subgroup CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_coe_sylow (S : Sylow 2 G) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup G) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
  exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩

theorem isConj_of_quotient_isConj {O : Subgroup G} [O.Normal] (hOodd : Odd (Nat.card O))
    {x y : G} (hx : BenderSuzuki.PFAppendixIII.IsInvolution x)
    (hy : BenderSuzuki.PFAppendixIII.IsInvolution y)
    (h : IsConj ((QuotientGroup.mk' O) x) ((QuotientGroup.mk' O) y)) : IsConj x y := by
  obtain ⟨gq, hgq⟩ := isConj_iff.mp h
  obtain ⟨g, hg⟩ :=
    CFSG.GorensteinWalter.involutions_conjugate_of_quotient_conjugate_odd_kernel
      O hOodd hx hy ⟨gq, hgq⟩
  exact isConj_iff.mpr ⟨g, hg⟩

theorem normalClosure_quotient_eq_top {O : Subgroup G} [O.Normal] {a : G}
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) :
    Subgroup.normalClosure ({(QuotientGroup.mk' O) a} : Set (G ⧸ O)) = ⊤ := by
  let f : G →* G ⧸ O := QuotientGroup.mk' O
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective O
  have h := Subgroup.map_normalClosure ({a} : Set G) f hf
  rw [hgen, Subgroup.map_top_of_surjective f hf] at h
  rw [show f '' ({a} : Set G) = {f a} by ext x; simp] at h
  exact h.symm

theorem quotient_factorization_two (S : Sylow 2 G)
    (hScard : Nat.card (S : Subgroup G) = 8) :
    (Nat.card (G ⧸ CFSG.pPrimeCore 2 G)).factorization 2 = 3 := by
  let O : Subgroup G := CFSG.pPrimeCore 2 G
  have hOodd : Odd (Nat.card O) := by
    dsimp [O]
    exact CFSG.Walter.W67.odd_card_pPrimeCore G
  have hSidx0 : (S : Subgroup G).index ≠ 0 := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  have hGfac : (Nat.card G).factorization 2 = 3 := by
    have hmul := congrArg (fun f : ℕ →₀ ℕ => f 2)
      (Nat.factorization_mul (Nat.card_pos.ne' : Nat.card (S : Subgroup G) ≠ 0) hSidx0)
    rw [← Subgroup.card_mul_index (S : Subgroup G)]
    rw [show (Nat.card (S : Subgroup G) * (S : Subgroup G).index).factorization 2 =
        (Nat.card (S : Subgroup G)).factorization 2 +
          ((S : Subgroup G).index).factorization 2 by
      simpa only [Finsupp.add_apply] using hmul]
    rw [hScard, Nat.factorization_eq_zero_of_not_dvd S.not_dvd_index]
    norm_num [Nat.factorization]
  have hmul : Nat.card (G ⧸ O) * Nat.card O = Nat.card G := by
    rw [← Subgroup.index_eq_card (H := O)]
    exact Subgroup.index_mul_card O
  have hmul2 : (Nat.card (G ⧸ O) * Nat.card O).factorization 2 =
      (Nat.card (G ⧸ O)).factorization 2 + (Nat.card O).factorization 2 := by
    simpa only [Finsupp.add_apply] using
      congrArg (fun f : ℕ →₀ ℕ => f 2)
        (Nat.factorization_mul (Nat.card_pos.ne' : Nat.card (G ⧸ O) ≠ 0)
          (Nat.card_pos.ne' : Nat.card O ≠ 0))
  have h1 : (Nat.card (G ⧸ O)).factorization 2 + (Nat.card O).factorization 2 = 3 := by
    rw [← hmul2, hmul, hGfac]
  rw [Nat.factorization_eq_zero_of_not_dvd hOodd.not_two_dvd_nat] at h1
  omega

theorem mod_eight_of_pgl2_factorization {q : ℕ} (hqodd : Odd q)
    (hfac : (q * (q ^ 2 - 1)).factorization 2 = 3) : q % 8 = 3 ∨ q % 8 = 5 := by
  have hqpos : 0 < q := hqodd.pos
  have hq1 : q ≠ 1 := by
    intro h
    rw [h] at hfac
    norm_num [Nat.factorization] at hfac
  have hq3 : 3 ≤ q := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hn0 : q * (q ^ 2 - 1) ≠ 0 := by
    have hq2 : 0 < q ^ 2 - 1 := by
      have : 1 < q ^ 2 := by nlinarith
      omega
    positivity
  have hoddmod : Odd (q % 8) := hqodd.mod_even (by norm_num)
  have hlt : q % 8 < 8 := Nat.mod_lt q (by norm_num)
  have hdiv16 : ∀ r : ℕ, q = 8 * r + 1 → 16 ∣ q * (q ^ 2 - 1) := by
    intro r hr
    rw [hr]
    exact dvd_mul_of_dvd_right
      (by use r * (4 * r + 1); ring_nf; omega) _
  have hdiv16' : ∀ r : ℕ, q = 8 * r + 7 → 16 ∣ q * (q ^ 2 - 1) := by
    intro r hr
    rw [hr]
    exact dvd_mul_of_dvd_right
      (by use (r + 1) * (4 * r + 3); ring_nf; omega) _
  have hge16 : ∀ {m : ℕ}, m ≠ 0 → 16 ∣ m → 4 ≤ m.factorization 2 := by
    intro m hm0 hm
    have hm' : 2 ^ 4 ∣ m := by norm_num at hm ⊢; exact hm
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).mp hm'
    simpa using this
  have hne1 : q % 8 ≠ 1 := by
    intro h
    have hq' : q = 8 * (q / 8) + 1 := by
      have := Nat.div_add_mod q 8
      omega
    have := hge16 hn0 (hdiv16 (q / 8) hq')
    omega
  have hne7 : q % 8 ≠ 7 := by
    intro h
    have hq' : q = 8 * (q / 8) + 7 := by
      have := Nat.div_add_mod q 8
      omega
    have := hge16 hn0 (hdiv16' (q / 8) hq')
    omega
  obtain ⟨k, hk⟩ := hoddmod
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · exfalso
    exact hne1 (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)
  · exfalso
    exact hne7 (by omega)

private theorem eq_top_of_mem_normalClosure_eq_top {Q : Type} [Group Q] {L : Subgroup Q}
    [L.Normal] {x : Q} (hx : x ∈ L)
    (hgen : Subgroup.normalClosure ({x} : Set Q) = ⊤) : L = ⊤ := by
  have hle : Subgroup.normalClosure ({x} : Set Q) ≤ L := by
    refine Subgroup.normalClosure_le_normal ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx
  rw [hgen] at hle
  exact top_le_iff.mp hle

private theorem conj_eq_self_of_conj_sq (v a : G) {m : ℕ}
    (hv2a : v ^ 2 * a * (v ^ 2)⁻¹ = a) (hveq : v = (v ^ 2) ^ (m + 1)) :
    v * a * v⁻¹ = a := by
  have hiter : ∀ j : ℕ, (v ^ 2) ^ j * a * ((v ^ 2) ^ j)⁻¹ = a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ]
        calc ((v ^ 2) ^ j * v ^ 2) * a * (((v ^ 2) ^ j * v ^ 2))⁻¹
            = (v ^ 2) ^ j * (v ^ 2 * a * (v ^ 2)⁻¹) * ((v ^ 2) ^ j)⁻¹ := by group
          _ = (v ^ 2) ^ j * a * ((v ^ 2) ^ j)⁻¹ := by rw [hv2a]
          _ = a := ih
  calc v * a * v⁻¹ = (v ^ 2) ^ (m + 1) * a * ((v ^ 2) ^ (m + 1))⁻¹ := by
        conv_lhs => rw [hveq]
    _ = a := hiter (m + 1)

private theorem not_odd_conj_abelian (S : Sylow 2 G) {a b v : G}
    (hb2 : b * b = 1) (hbS : b ∈ S) (hab : IsConj a b) (hne : a ≠ b)
    (hcl : ∀ x : G, x ∈ S → IsConj a x → x = a ∨ x = b) (hz1 : a * b ≠ 1)
    (hvodd : Odd (orderOf v)) (hvN : v ∈ Subgroup.normalizer (S : Set G))
    (hva : v * a * v⁻¹ = b) : False := by
  have hvbS : v * b * v⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hvN b).mp hbS
  have hconj_vb : IsConj b (v * b * v⁻¹) := isConj_iff.mpr ⟨v, by group⟩
  have hconj_a_vb : IsConj a (v * b * v⁻¹) := IsConj.trans hab hconj_vb
  rcases hcl (v * b * v⁻¹) hvbS hconj_a_vb with h | h
  · have hv2a : v ^ 2 * a * (v ^ 2)⁻¹ = a := by
      rw [pow_two, mul_inv_rev]
      calc (v * v) * a * (v⁻¹ * v⁻¹) = v * (v * a * v⁻¹) * v⁻¹ := by group
        _ = v * b * v⁻¹ := by rw [hva]
        _ = a := h
    obtain ⟨m, hm⟩ := hvodd
    have hveq : v = (v ^ 2) ^ (m + 1) := by
      rw [← pow_mul]
      have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [h2, pow_succ, ← hm, pow_orderOf_eq_one, one_mul]
    have hva' : v * a * v⁻¹ = a := conj_eq_self_of_conj_sq v a hv2a hveq
    exact hne (hva.symm.trans hva').symm
  · have hzv : v * (a * b) * v⁻¹ = 1 := by
      calc v * (a * b) * v⁻¹ = (v * a * v⁻¹) * (v * b * v⁻¹) := by group
        _ = b * b := by rw [hva, h]
        _ = 1 := hb2
    have hzne : v * (a * b) * v⁻¹ ≠ 1 := by
      intro hh
      apply hz1
      have := congrArg (fun w => v⁻¹ * w * v) hh
      simpa [mul_assoc] using this
    exact hzne hzv

private theorem twoPart_mem_of_normalizer (S : Sylow 2 G) {n u : G} {k : ℕ}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (hu : u ∈ Subgroup.zpowers n)
    (huk : u ^ (2 ^ k) = 1) : u ∈ S := by
  have huN : u ∈ Subgroup.normalizer (S : Set G) := (Subgroup.zpowers_le.mpr hn) hu
  have hzu : IsPGroup 2 (Subgroup.zpowers u) := by
    rw [isPGroup_iff_exists_orderOf_dvd_pow]
    refine ⟨k, fun g => ?_⟩
    rw [← Subgroup.orderOf_coe g]
    exact (orderOf_dvd_of_mem_zpowers g.2).trans (orderOf_dvd_of_pow_eq_one huk)
  have hsupP : IsPGroup 2 (Subgroup.zpowers u ⊔ (S : Subgroup G) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (p := 2) (H := Subgroup.zpowers u)
      (K := (S : Subgroup G)) hzu S.isPGroup' (Subgroup.zpowers_le.mpr huN)
  have hsup_eq : (Subgroup.zpowers u ⊔ (S : Subgroup G) : Subgroup G) = S :=
    (isSylowOf_coe_sylow S).eq_of_le le_sup_right le_top hsupP
  change u ∈ (S : Subgroup G)
  rw [← hsup_eq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)

theorem not_sylowOf_fourGroup (S : Sylow 2 G) {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (haS : a ∈ S) (hbS : b ∈ S)
    (hne : a ≠ b) (hab : IsConj a b)
    (hcl : ∀ x : G, x ∈ S → IsConj a x → x = a ∨ x = b)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (fourGroup a b) ⊤) : False := by
  have hVleS : fourGroup a b ≤ (S : Subgroup G) := fourGroup_le haS hbS
  have hSV : (S : Subgroup G) = fourGroup a b := hsyl.eq_of_le hVleS le_top S.isPGroup'
  have ha2 : a * a = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two ha).symm
  have hb2 : b * b = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two hb).symm
  have hcomm : a * b = b * a := mul_comm_of_conj_pair S hb haS hbS hne hcl
  have hVea : IsElemAbelian 2 (fourGroup a b) := fourGroup_isElemAbelian ha2 hb2 hcomm
  have hScomm : IsMulCommutative (S : Subgroup G) := by
    rw [hSV]
    exact hVea.1
  obtain ⟨nn, hnn⟩ := isConj_iff.mp hab
  haveI : IsMulCommutative (S : Subgroup G) := hScomm
  obtain ⟨n, hn, hnconj⟩ :=
    Sylow.conj_eq_normalizer_conj_of_mem S a nn⁻¹ haS (by
      rw [show nn⁻¹⁻¹ * a * nn⁻¹ = b by simpa using hnn]
      exact hbS)
  have hNnorm : n⁻¹ ∈ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hn
  have hNa : n⁻¹ * a * n = b := by
    rw [← hnconj]
    simpa using hnn
  obtain ⟨u, hu, v, hv, hnuv, ⟨k, huk⟩, hvodd⟩ :=
    CFSG.LocalAnalysis.SteinbergBV.exists_two_pow_mul_odd_decomposition n⁻¹
  have huS : u ∈ S := twoPart_mem_of_normalizer S hNnorm hu huk
  have huV : u ∈ fourGroup a b := by rw [← hSV]; exact huS
  have hua : u * a = a * u := hVea.comm huV (mem_fourGroup_left a b)
  have hub : u * b = b * u := hVea.comm huV (mem_fourGroup_right a b)
  have hva : v * a * v⁻¹ = b := by
    have h1 : u * (v * a * v⁻¹) * u⁻¹ = b := by
      calc u * (v * a * v⁻¹) * u⁻¹ = (u * v) * a * (u * v)⁻¹ := by group
        _ = b := by rw [← hnuv]; simpa using hNa
    calc v * a * v⁻¹ = u⁻¹ * (u * (v * a * v⁻¹) * u⁻¹) * u := by group
      _ = u⁻¹ * b * u := by rw [h1]
      _ = b := by rw [mul_assoc, ← hub, inv_mul_cancel_left]
  have hvN : v ∈ Subgroup.normalizer (S : Set G) := (Subgroup.zpowers_le.mpr hNnorm) hv
  have hz1 : a * b ≠ 1 := by
    have hnot := mul_notMem_of_orderOf_eq_two ha hb hne
    exact fun h => hnot (by simp [h])
  exact not_odd_conj_abelian S hb2 hbS hab hne hcl hz1 hvodd hvN hva

private theorem isInvolution_subtype {Q : Type} [Group Q] {M : Subgroup Q} {x : Q}
    (hxM : x ∈ M) (hx : orderOf x = 2) :
    BenderSuzuki.PFAppendixIII.IsInvolution (⟨x, hxM⟩ : M) := by
  have hxM_order : orderOf (⟨x, hxM⟩ : M) = 2 := by
    rwa [Subgroup.orderOf_mk]
  exact CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two hxM_order

private theorem isConj_of_quotient_psu3 {M : Subgroup G} (O : Subgroup M) [O.Normal]
    (hOodd : Odd (Nat.card O)) {x y : M}
    (hx : BenderSuzuki.PFAppendixIII.IsInvolution x)
    (hy : BenderSuzuki.PFAppendixIII.IsInvolution y)
    (hquot : Nonempty (M ⧸ O ≃* PSU3 2 2)) : IsConj x y := by
  classical
  have hxord : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hyord : orderOf y = 2 := orderOf_eq_prime hy.2 hy.1
  have hqx : orderOf ((QuotientGroup.mk' O) x) = 2 :=
    CFSG.Wreathed.InvolutionInducedCharacters.orderOf_mk_eq_two O hOodd hxord
  have hqy : orderOf ((QuotientGroup.mk' O) y) = 2 :=
    CFSG.Wreathed.InvolutionInducedCharacters.orderOf_mk_eq_two O hOodd hyord
  obtain ⟨e⟩ := hquot
  haveI : Finite (PSU3 2 2) := Finite.of_injective e.symm e.symm.injective
  have hB : CFSG.BenderSuzuki.IsBenderGroup (PSU3 2 2) :=
    CFSG.BenderSuzuki.IsBenderGroup.isPSU3 2 (le_refl 2)
      (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 2))
  have hord_ex : orderOf (e ((QuotientGroup.mk' O) x)) = 2 := by
    rw [MulEquiv.orderOf_eq, hqx]
  have hord_ey : orderOf (e ((QuotientGroup.mk' O) y)) = 2 := by
    rw [MulEquiv.orderOf_eq, hqy]
  obtain ⟨gm, hgm⟩ := isConj_iff.mp
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hB hord_ex hord_ey)
  have hqconj : ∃ gq : M ⧸ O,
      gq * (QuotientGroup.mk' O) x * gq⁻¹ = (QuotientGroup.mk' O) y := by
    refine ⟨e.symm gm, ?_⟩
    apply e.injective
    simpa using hgm
  obtain ⟨g, hg⟩ :=
    CFSG.GorensteinWalter.involutions_conjugate_of_quotient_conjugate_odd_kernel
      O hOodd hx hy hqconj
  exact isConj_iff.mpr ⟨g, hg⟩

theorem not_quotient_psu3 (S : Sylow 2 G) {a b : G}
    (ha : orderOf a = 2) (hzord : orderOf (a * b) = 2)
    (hzconj : ¬ IsConj a (a * b))
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤)
    (hquot : Nonempty (↥(Subgroup.normalClosure (fourGroup a b : Set G)) ⧸
      CFSG.Assembly.oddCore ↥(Subgroup.normalClosure (fourGroup a b : Set G)) ≃* PSU3 2 2)) :
    False := by
  classical
  let M : Subgroup G := Subgroup.normalClosure (fourGroup a b : Set G)
  have hMtop : M = ⊤ := normalClosure_fourGroup_eq_top hgen
  let O : Subgroup M := CFSG.Assembly.oddCore M
  haveI hOn : O.Normal := by
    dsimp [O]
    infer_instance
  have hOodd : Odd (Nat.card O) := by
    have heq : O = CFSG.pPrimeCore 2 M := CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore M
    rw [heq]
    exact CFSG.Walter.W67.odd_card_pPrimeCore M
  have haM : a ∈ M := by rw [hMtop]; exact Subgroup.mem_top a
  have hzM : a * b ∈ M := by rw [hMtop]; exact Subgroup.mem_top (a * b)
  let aM : M := ⟨a, haM⟩
  let zM : M := ⟨a * b, hzM⟩
  have haM_inv : BenderSuzuki.PFAppendixIII.IsInvolution aM := isInvolution_subtype haM ha
  have hzM_inv : BenderSuzuki.PFAppendixIII.IsInvolution zM := isInvolution_subtype hzM hzord
  have hconjM : IsConj aM zM := isConj_of_quotient_psu3 O hOodd haM_inv hzM_inv hquot
  apply hzconj
  obtain ⟨gg, hgg⟩ := isConj_iff.mp hconjM
  exact isConj_iff.mpr ⟨gg.1, by simpa using congrArg Subtype.val hgg⟩

private theorem conj_class_twoGroup_quotient (S : Sylow 2 G) (O : Subgroup G) [O.Normal]
    (hO : O = CFSG.pPrimeCore 2 G) (hScard : Nat.card (S : Subgroup G) = 8)
    {a b : G} (haS : a ∈ S)
    (hcl : ∀ x : G, x ∈ S → IsConj a x → x = a ∨ x = b)
    (hQ : IsPGroup 2 (G ⧸ O)) :
    Subgroup.map (QuotientGroup.mk' O) (S : Subgroup G) = ⊤ ∧
      Nat.card (Subgroup.map (QuotientGroup.mk' O) (S : Subgroup G)) = 8 ∧
      ∀ g : G ⧸ O, g * (QuotientGroup.mk' O) a * g⁻¹ = (QuotientGroup.mk' O) a ∨
        g * (QuotientGroup.mk' O) a * g⁻¹ = (QuotientGroup.mk' O) b := by
  classical
  let Q := G ⧸ O
  let f : G →* Q := QuotientGroup.mk' O
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective O
  let Sbar : Sylow 2 Q := Sylow.mapSurjective hf S
  have hSbar_coe : (Sbar : Subgroup Q) = (S : Subgroup G).map f :=
    Sylow.coe_mapSurjective hf S
  have hQtop : IsPGroup 2 (⊤ : Subgroup Q) := IsPGroup.to_subgroup hQ ⊤
  have hSbar_top : (Sbar : Subgroup Q) = ⊤ := (Sbar.is_maximal' hQtop le_top).symm
  have hSmap_top : (S : Subgroup G).map f = ⊤ := by rw [← hSbar_coe, hSbar_top]
  have hSmap_card : Nat.card ((S : Subgroup G).map f) = 8 := by
    have hOodd : Odd (Nat.card O) := by
      rw [hO]
      exact CFSG.Walter.W67.odd_card_pPrimeCore G
    have hcop : Nat.Coprime (Nat.card (S : Subgroup G)) (Nat.card O) := by
      rw [hScard]
      exact Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hOodd)
    have hSO : (S : Subgroup G) ⊓ f.ker = ⊥ := by
      rw [show f.ker = O from QuotientGroup.ker_mk' O]
      exact Subgroup.inf_eq_bot_of_coprime hcop
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot f hSO, hScard]
  have hclass : ∀ g : Q, g * f a * g⁻¹ = f a ∨ g * f a * g⁻¹ = f b := by
    intro g
    have hg : g ∈ (S : Subgroup G).map f := by rw [hSmap_top]; exact Subgroup.mem_top g
    obtain ⟨s, hsS, hsf⟩ := Subgroup.mem_map.mp hg
    have hconjS : s * a * s⁻¹ ∈ S := mul_mem (mul_mem hsS haS) (inv_mem hsS)
    have hconja : IsConj a (s * a * s⁻¹) := isConj_iff.mpr ⟨s, rfl⟩
    have hkey : f s * f a * (f s)⁻¹ = f (s * a * s⁻¹) := by simp [map_mul]
    rcases hcl (s * a * s⁻¹) hconjS hconja with h | h
    · left
      rw [← hsf, hkey, h]
    · right
      rw [← hsf, hkey, h]
  exact ⟨hSmap_top, hSmap_card, hclass⟩

theorem not_isPGroup_quotient (S : Sylow 2 G) {a b : G}
    (haS : a ∈ S) (hScard : Nat.card (S : Subgroup G) = 8)
    (hcardV : Nat.card (fourGroup a b) = 4)
    (hcl : ∀ x : G, x ∈ S → IsConj a x → x = a ∨ x = b)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤)
    (hQ : IsPGroup 2 (G ⧸ CFSG.pPrimeCore 2 G)) : False := by
  classical
  let O : Subgroup G := CFSG.pPrimeCore 2 G
  haveI hOn : O.Normal := CFSG.pPrimeCore_normal
  let Q := G ⧸ O
  let f : G →* Q := QuotientGroup.mk' O
  have hQ' : IsPGroup 2 (G ⧸ O) := hQ
  obtain ⟨hSmap_top, hSmap_card, hclass⟩ :=
    conj_class_twoGroup_quotient S O rfl hScard haS hcl hQ'
  have hgenQ : Subgroup.normalClosure ({f a} : Set Q) = ⊤ :=
    normalClosure_quotient_eq_top (O := O) hgen
  have hVmap_top : (fourGroup a b).map f = ⊤ := by
    have hle : Subgroup.normalClosure ({f a} : Set Q) ≤ (fourGroup a b).map f := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      rw [Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨g, hg⟩ := isConj_iff.mp hyx
      rw [← hg]
      rcases hclass g with h | h
      · rw [h]; exact Subgroup.mem_map_of_mem f (mem_fourGroup_left a b)
      · rw [h]; exact Subgroup.mem_map_of_mem f (mem_fourGroup_right a b)
    rw [hgenQ] at hle
    exact top_le_iff.mp hle
  have hQcard : Nat.card Q = 8 := by
    rw [← Subgroup.card_top (G := Q), ← hSmap_top, hSmap_card]
  have hQle : Nat.card Q ≤ 4 := by
    rw [← Subgroup.card_top (G := Q), ← hVmap_top]
    calc Nat.card ((fourGroup a b).map f) ≤ Nat.card (fourGroup a b) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (fourGroup a b) f)
      _ = 4 := hcardV
  omega

theorem not_psl2_quotient {a b : G}
    (ha : orderOf a = 2) (hzord : orderOf (a * b) = 2) (hzconj : ¬ IsConj a (a * b))
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤)
    (K : Type) [Field K] [Finite K] (hKpp : IsOddPrimePower (Nat.card K))
    (L : Subgroup (G ⧸ CFSG.pPrimeCore 2 G)) (hLn : L.Normal) (hLidx : Odd L.index)
    (eP : L ≃* CFSG.GorensteinWalter.PSL2 K) : False := by
  classical
  let O : Subgroup G := CFSG.pPrimeCore 2 G
  haveI hOn : O.Normal := CFSG.pPrimeCore_normal
  haveI hLN : L.Normal := hLn
  have hOodd : Odd (Nat.card O) := by
    dsimp [O]
    exact CFSG.Walter.W67.odd_card_pPrimeCore G
  let Q := G ⧸ O
  let f : G →* Q := QuotientGroup.mk' O
  have hfa : orderOf (f a) = 2 :=
    CFSG.Wreathed.InvolutionInducedCharacters.orderOf_mk_eq_two O hOodd ha
  have hfz : orderOf (f (a * b)) = 2 :=
    CFSG.Wreathed.InvolutionInducedCharacters.orderOf_mk_eq_two O hOodd hzord
  have hfa_sq : f a ^ 2 = 1 := by rw [← hfa]; exact pow_orderOf_eq_one (f a)
  have hfz_sq : f (a * b) ^ 2 = 1 := by rw [← hfz]; exact pow_orderOf_eq_one (f (a * b))
  have hfaL : f a ∈ L := CFSG.Goldschmidt75.mem_of_sq_eq_one_of_odd_index hLidx hfa_sq
  have hfzL : f (a * b) ∈ L :=
    CFSG.Goldschmidt75.mem_of_sq_eq_one_of_odd_index hLidx hfz_sq
  have hgenQ : Subgroup.normalClosure ({f a} : Set Q) = ⊤ :=
    normalClosure_quotient_eq_top (O := O) hgen
  have hLtop : L = ⊤ := eq_top_of_mem_normalClosure_eq_top hfaL hgenQ
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hKpp
  have hxL : orderOf (⟨f a, hfaL⟩ : L) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨f a, hfaL⟩ : L), hfa]
  have hzL : orderOf (⟨f (a * b), hfzL⟩ : L) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨f (a * b), hfzL⟩ : L), hfz]
  have hxP : orderOf (eP ⟨f a, hfaL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, hxL]
  have hzP : orderOf (eP ⟨f (a * b), hfzL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, hzL]
  haveI : Fact p.Prime := ⟨hp⟩
  have hconjP : IsConj (eP ⟨f a, hfaL⟩) (eP ⟨f (a * b), hfzL⟩) :=
    CFSG.Walter.psl2_isConj_of_orderOf_eq_two K (p := p) (f := n) hq hpodd (by omega) hxP hzP
  obtain ⟨gP, hgP⟩ := isConj_iff.mp hconjP
  have hconjL : IsConj (⟨f a, hfaL⟩ : L) (⟨f (a * b), hfzL⟩ : L) := by
    refine isConj_iff.mpr ⟨eP.symm gP, ?_⟩
    apply eP.injective
    simpa using hgP
  obtain ⟨gL, hgL⟩ := isConj_iff.mp hconjL
  have hQconj : IsConj (f a) (f (a * b)) := by
    refine isConj_iff.mpr ⟨(gL : Q), ?_⟩
    simpa using congrArg Subtype.val hgL
  exact hzconj (isConj_of_quotient_isConj (O := O) hOodd
    (CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two ha)
    (CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two hzord) hQconj)

theorem pgl2_branch (S : Sylow 2 G) {a : G}
    (ha : orderOf a = 2)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤)
    (hScard : Nat.card (S : Subgroup G) = 8)
    (K : Type) [Field K] [Finite K] (hKpp : IsOddPrimePower (Nat.card K))
    (L : Subgroup (G ⧸ CFSG.pPrimeCore 2 G)) (hLn : L.Normal) (hLidx : Odd L.index)
    (eP : L ≃* CFSG.GorensteinWalter.PGL2 K) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'),
      (Nat.card K' % 8 = 3 ∨ Nat.card K' % 8 = 5) ∧
        Nonempty (G ⧸ CFSG.pPrimeCore 2 G ≃* CFSG.GorensteinWalter.PGL2 K') := by
  classical
  let O : Subgroup G := CFSG.pPrimeCore 2 G
  haveI hOn : O.Normal := CFSG.pPrimeCore_normal
  haveI hLN : L.Normal := hLn
  have hOodd : Odd (Nat.card O) := by
    dsimp [O]
    exact CFSG.Walter.W67.odd_card_pPrimeCore G
  let Q := G ⧸ O
  let f : G →* Q := QuotientGroup.mk' O
  have hfa : orderOf (f a) = 2 :=
    CFSG.Wreathed.InvolutionInducedCharacters.orderOf_mk_eq_two O hOodd ha
  have hfa_sq : f a ^ 2 = 1 := by rw [← hfa]; exact pow_orderOf_eq_one (f a)
  have hfaL : f a ∈ L := CFSG.Goldschmidt75.mem_of_sq_eq_one_of_odd_index hLidx hfa_sq
  have hgenQ : Subgroup.normalClosure ({f a} : Set Q) = ⊤ :=
    normalClosure_quotient_eq_top (O := O) hgen
  have hLtop : L = ⊤ := eq_top_of_mem_normalClosure_eq_top hfaL hgenQ
  let eQ : Q ≃* CFSG.GorensteinWalter.PGL2 K :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hLtop).symm.trans eP)
  have hQfac : (Nat.card Q).factorization 2 = 3 := quotient_factorization_two S hScard
  have hKfac : (Nat.card K * (Nat.card K ^ 2 - 1)).factorization 2 = 3 := by
    rw [← CFSG.GorensteinWalter.pgl2_card_formula K, ← Nat.card_congr eQ.toEquiv]
    exact hQfac
  have hqodd : Odd (Nat.card K) := by
    obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hKpp
    rw [hq]
    exact hpodd.pow
  refine ⟨K, inferInstance, inferInstance, mod_eight_of_pgl2_factorization hqodd hKfac, ⟨eQ⟩⟩
