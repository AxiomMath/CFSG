module

public import CFSG.CGT.PushingUpLit.SolKR2.Defs
public import CFSG.CGT.T75O.AptSyl
public import CFSG.CGT.T75O.Fix
public import CFSG.CGT.T75O.Orders
public import CFSG.CGT.T75G.Sec68Main
public import CFSG.RankThree.GF2n.L34TwoLocalProj
public import CFSG.CGT.Timmesfeld75.Sec68FromCorB

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78 CFSG.Timmesfeld CFSG.Timmesfeld.ARS
  CFSG.CGT.T75O
open CFSG.RankThree.PartTwo (omegaOneSub)

structure Cfg81 {G : Type} [Group G] (R : Set (Subgroup G)) (A U : Subgroup G) : Prop where
  le : A ≤ U
  isPGroup : IsPGroup 2 U
  normalizer_le : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (U : Set G)
  inter : ∀ E ∈ R, ∀ y ∈ E, y ∈ U → y ∈ A
  not_le : ¬ U ≤ A

section Helpers

namespace Engine

theorem exists_ne_zero_one_field {E : Type} [Field E] [Finite E] (h : 3 ≤ Nat.card E) :
    ∃ l : E, l ≠ 0 ∧ l ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective fun b : Bool => if b then (1 : E) else 0 := fun l => by
    by_cases hl : l = 0
    · exact ⟨false, by simp [hl]⟩
    · exact ⟨true, by simp [hcon l hl]⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  omega

end Engine

variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

namespace Engine

theorem exists_rootSet_ne {t : G} (hs : CorB.Setup t) {B₀ : Subgroup G}
    (hrg : rootGroup (CorB.cls t) t = B₀) (h3 : 3 ≤ Nat.card B₀) :
    ∃ x ∈ CorB.cls t, ∃ e ∈ rootSet (CorB.cls t) x, e ≠ x := by
  by_contra hcon
  push Not at hcon
  have hle : rootGroup (CorB.cls t) t ≤ Subgroup.zpowers t := by
    rw [rootGroup, Subgroup.closure_le]
    intro e he
    rw [hcon t (CorB.mem_cls_self t) e he]
    exact Subgroup.mem_zpowers t
  have h2 : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers, hs.orderOf_eq]
  have h1 := Subgroup.card_le_of_le hle
  rw [hrg, h2] at h1
  omega

theorem hyp_of_simple [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (hs : CorB.Setup t) (hnd : ∃ d e : G, IsConj t d ∧ IsConj t e ∧ orderOf (d * e) = 4) :
    CFSG.Timmesfeld.Hyp G (CorB.cls t) := by
  have ht1 : t ≠ 1 := by
    intro h1
    have := hs.orderOf_eq
    rw [h1, orderOf_one] at this
    omega
  have hNtop : Subgroup.normalClosure ({t} : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({t} : Set G)) with
      h | h
    · exfalso
      apply ht1
      have : t ∈ Subgroup.normalClosure ({t} : Set G) := Subgroup.subset_normalClosure rfl
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    · exact h
  refine ⟨inferInstance, ⟨t, rfl⟩, hs.isRootInvolutionSet, ?_, ?_, ?_, ?_⟩
  · rw [← CorB.normalClosure_eq]
    exact hNtop
  · intro N hN hodd
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      have heven : 2 ∣ Nat.card G := hs.orderOf_eq ▸ orderOf_dvd_natCard t
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 heven)
  · intro N hN h2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have hG2 : IsPGroup 2 G := fun g => by
        obtain ⟨k, hk⟩ := h2 ⟨g, h ▸ Subgroup.mem_top g⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      have hcen := center_eq_bot_of_simple_nonabelian G hnab
      have : Nontrivial (Subgroup.center G) := hG2.center_nontrivial
      rw [hcen] at this
      exact absurd this (not_nontrivial (⊥ : Subgroup G))
  · obtain ⟨d, e, hd, he, h4⟩ := hnd
    exact ⟨d, hd, e, he, h4⟩

end Engine

theorem Cfg81.ofR2 (h : R2 M B) {R : Set (Subgroup G)} (hR : IsRootClass R) :
    Cfg81 R (omegaOneSub B) (omegaTwoSub B) where
  le := by
    have h1 := CFSG.RankThree.PartTwo.omegaOneSub_le (omegaTwoSub B)
    rwa [omegaOneSub_omegaTwoSub h.H.comm] at h1
  isPGroup := h.H.two.to_le (omegaTwoSub_le B)
  normalizer_le := by
    have hB0 : omegaOneSub B ≠ ⊥ := by
      intro hbot
      have h4 := h.card4
      rw [hbot, Subgroup.card_bot] at h4
      omega
    rw [h.H.normalizer_eq (CFSG.RankThree.PartTwo.omegaOneSub_le B) hB0
      h.H.le_normalizer_omegaOne]
    exact h.H.le_normalizer_omegaTwo
  inter := fun E hE y hy hyU =>
    (mem_omegaOneSub_iff h.H.comm).2 ⟨omegaTwoSub_le B hyU, hR.mul_self E hE y hy⟩
  not_le := by
    intro hle
    obtain ⟨e⟩ := h.c4c4
    have h16 : Nat.card (omegaTwoSub B) = 16 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      simp
    have h1 := Subgroup.card_le_of_le hle
    rw [h16, h.card4] at h1
    omega

end Helpers

section Apartment

variable {G : Type} [Group G] {R : Set (Subgroup G)}
  {A U : Subgroup G} (c : Cfg81 R A U)
include c

namespace Cfg81

theorem false_of_coords {A₀ P P' : Subgroup G} (S : CaseH.Setup R A A₀ P P') {F E : Type}
    [Field F] [Field E] [CharP E 2] [CharP F 2] [Finite F] (cc : CaseH.Coords S F E)
    (e : F →+* E) (he : ∀ s u, cc.c5 s u = cc.c5 (e u * s) 1)
    (hfix : ∀ (u : F) (w r : E) (v : F),
      (∀ s : E, S.ad (cc.x1_mem_normalizer s) (cc.vc u w r v) = cc.vc u w r v) →
        u = 0 ∧ w = 0 ∧ r = 0)
    {n m k o : ℕ} (hq : Nat.card A = 2 ^ n)
    (hL : (linesThrough R A).ncard = 2 ^ m + 1) (hE : Nat.card E = 2 ^ m)
    (hodd : Odd o) (hG : Nat.card G = 2 ^ k * o) (hk : k ≤ 3 * n + 3 * m) : False := by
  have := S.hyp.finite
  apply c.not_le
  refine Apt.le_A cc e he hfix c.le c.isPGroup (fun x hx => c.normalizer_le hx)
    (fun v hv => ?_) hodd hG ?_
  · by_contra hv0
    have hyA := c.inter P' S.hP'.2.1 _ (cc.x2_mem v) hv
    have h := (S.proj_P' (cc.x2_mem v)).symm.trans (S.proj_A hyA)
    have h2 := congrArg (fun p => (p.2.2.2 : G)) h
    exact hv0 (cc.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1) (h2.trans cc.x2_zero.symm))
  · rw [Apt.card_M_mul_card_E S hq hL hE]
    exact Nat.pow_le_pow_right (by norm_num) hk

end Cfg81

end Apartment

section ApartmentFinal


variable {G : Type} [Group G] {R : Set (Subgroup G)} {A U : Subgroup G} (c : Cfg81 R A U)
include c

namespace Cfg81

theorem false_of_setup {A₀ P P' : Subgroup G} (S : CaseH.Setup R A A₀ P P')
    (h23 : ¬ (Nat.card A = 2 ∧ (linesThrough R A).ncard = 3)) : False := by
  have := S.hyp.finite
  obtain ⟨n, m, hn, hm, hq, hL, ⟨cc⟩⟩ := S.exists_coords
  obtain ⟨e, he⟩ := cc.exists_ringHom
  obtain ⟨τ, hτ0, hτ⟩ := cc.exists_tau
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hE : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  rcases cc.classify e he hτ0 hτ hn hF hE with ⟨rfl, hsq⟩ | ⟨rfl, hsq⟩ | ⟨rfl, rfl⟩
  · have h2 : 2 ≤ m := by
      by_contra hlt
      have hm1 : m = 1 := by omega
      subst hm1
      exact h23 ⟨by rw [hq]; norm_num, by rw [hL]; norm_num⟩
    have hω : ∃ ω : GaloisField 2 m, ω ≠ 0 ∧ ω ≠ 1 :=
      Engine.exists_ne_zero_one_field (by
        rw [hE]
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2)
    obtain ⟨o, hodd, hG⟩ := card_g2 cc e he hτ0 hτ hsq (hE.trans hF.symm) hF h2
    exact c.false_of_coords S cc e he (hfix_g2 cc e he hτ0 hτ hsq hω) hq hL hE hodd hG
      (le_of_eq (by ring))
  · have hE' : Nat.card (GaloisField 2 (3 * n)) = (2 ^ n) ^ 3 := by
      rw [hE, ← pow_mul, mul_comm]
    let σ : GaloisField 2 (3 * n) →+* GaloisField 2 (3 * n) :=
      iterateFrobenius (GaloisField 2 (3 * n)) 2 n
    have hσ : ∀ x, σ x = x ^ 2 ^ n := fun x => iterateFrobenius_def 2 n x
    have hσ3 : ∀ x, σ (σ (σ x)) = x :=
      CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hE' hσ
    have hsq' : ∀ s, cc.sharp s = σ s * σ (σ s) := fun s => by
      rw [hsq, hσ, hσ, ← pow_mul, ← pow_add]
      congr 1
      rw [two_mul, pow_add]
    have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    have hs : ∃ s, σ s ≠ s := by
      by_contra hcon
      push Not at hcon
      have hsurj : Function.Surjective e := fun x => CaseH.exists_e_eq e hF hσ hq1 (hcon x)
      have h1 := Nat.card_le_card_of_surjective e hsurj
      rw [hE, hF] at h1
      have h2 : 2 ^ n < 2 ^ (3 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨o, hodd, hG⟩ := card_d4 cc e he hτ0 hτ hsq hF hE hn
    exact c.false_of_coords S cc e he (hfix_d4 cc e he hτ0 hτ σ hσ3 hsq' hs) hq hL hE hodd hG
      (le_of_eq (by ring))
  · exact absurd (by rw [hL]; norm_num)
      (CaseH.ncard_linesThrough_ne_five S.hyp S.hH S.hA (by rw [hq]; norm_num))

end Cfg81

end ApartmentFinal

section Main


variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

namespace R2

theorem false_of_hyp (h : R2 M B) {t : G} (hs : CorB.Setup t)
    (hH : CFSG.Timmesfeld.Hyp G (CorB.cls t))
    (hrg : rootGroup (CorB.cls t) t = omegaOneSub B) : False := by
  have hno := CorB.noOppCentral_rootClass hs.isRootInvolutionSet hs.noOddCent
  obtain ⟨hc, hsc, hm, -⟩ := CorB.largeFacts hH
    (Engine.exists_rootSet_ne hs hrg (by rw [h.card4]; norm_num))
  have hARS := arsHyp_rootClass hH hc hsc hm
  have hA : omegaOneSub B ∈ rootClass (CorB.cls t) :=
    ⟨t, CorB.mem_cls_self t, hrg.symm⟩
  by_cases hmax : IsCoatom (Subgroup.normalizer ((omegaOneSub B : Subgroup G) : Set G))
  · have hσ := CorB.sigmaSet_eq_lambdaSet hARS hno hA
    have hH' : SigmaEqLambda (rootClass (CorB.cls t)) := sigmaEqLambda_of_mem hARS.root hA hσ
    have h3 := CaseH.three_le_ncard_linesThrough hARS hH' hA hmax
    have h23 : ¬ (Nat.card (omegaOneSub B) = 2 ∧
        (linesThrough (rootClass (CorB.cls t)) (omegaOneSub B)).ncard = 3) := fun h' => by
      have h1 := h'.1
      have h4 := h.card4
      omega
    have hT := CaseH.mTransitive_of_not_two_three hARS hH' hA h3 h23
    obtain ⟨A₀, P, P', S⟩ := CaseH.exists_setup hARS hH' hT hA h3
    exact (Cfg81.ofR2 h hARS.root).false_of_setup S h23
  · obtain ⟨f, -, -, hLM⟩ := CFSG.CGT.T75G.caseL_psl3 hARS hno hA hmax
    have hm2 := statedClassicalModel_of_lieModel_of_ne_zero (by norm_num) hLM
    exact h.ne (CFSG.RankThree.GF2n.L34.isElemAbelian_of_le_of_isMaximalTwoLocal_L3 hm2 h.H.max
      h.H.le h.H.normal h.H.two)

theorem false_of_setup [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (h : R2 M B) {t : G}
    (hs : CorB.Setup t) (hrg : rootGroup (CorB.cls t) t = omegaOneSub B)
    (hnd : ∃ d e : G, IsConj t d ∧ IsConj t e ∧ orderOf (d * e) = 4) : False :=
  h.false_of_hyp hs (Engine.hyp_of_simple hnab hs hnd) hrg

end R2

end Main

end CFSG.CGT.PushingUpLit.SolKR2
