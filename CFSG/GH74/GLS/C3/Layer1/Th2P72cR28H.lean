module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28G
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28
import CFSG.GH74.GLS.C3.Layer1.Th2L83
public import CFSG.GH74.GLS.C3.Layer1.Th2P64C

public section

namespace CFSG.GH74.GLS.Th2.R714

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G]

structure Ctx (x : G) (K T : Subgroup G) : Prop where
  cen : CenterlessBar K
  PQ : CommDisj (T ⊓ K) (T ⊓ CxK x K)
  P4 : Nat.card ↥(T ⊓ K) = 4
  PEA : CFSG.IsElementaryAbelian 2 ↥(T ⊓ K)
  KN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  Tle : Nat.card ↥T ≤ 8 * Nat.card ↥(T ⊓ CxK x K)
  e5 : Nonempty (kBar K ≃* alternatingGroup (Fin 5))

theorem ctx_of_std (hG4 : pRank 2 G ≤ 4)
    {x y : G} {K T S : Subgroup G} (hstd : Th2Std x y K T S)
    (hL5 : HasL2Model (kBar K) (fun q => q = 5)) : Ctx x K T := by
  have hPr : ∀ q : ℕ, q = 5 → Odd q := by
    rintro q rfl
    decide
  have hcen := centerlessBar_of_hasL2Model hPr hL5
  have hPQ := hstd.commDisj hcen
  have hP := rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL5
  have hP4 := card_sylow_L2_five hstd.sylow_P hL5
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  have hUP : U = T ⊓ K := Subgroup.eq_of_le_of_card_ge hU.1 (by rw [hU.2.2, hP4])
  have hrkP : 2 ≤ pRank 2 ↥(T ⊓ K) := by rw [← hUP, pRank_of_isFourSub hU]
  have hKN := hstd.K_normal hG4 hcen hrkP
  obtain ⟨e5⟩ := C3.Layer1.Back.nonempty_alt5_of_hasL2Model5 hL5
  have hTle := hstd.card_T_le_of_A5 hKN e5
  exact ⟨hcen, hPQ, hP4, hUP ▸ hU.2.1, hKN, hTle, ⟨e5⟩⟩

omit [Finite G] in
@[expose] def GoodK (K : Subgroup G) (u : G) : Prop :=
  ∀ J : Subgroup G, IsPCompIn 2 (centralizer ({u} : Set G)) J → Nonempty (kBar J ≃* kBar K) →
    CFSG.IsQuasisimple ↥J

theorem GoodK.conj {K : Subgroup G} {u : G} (h : GoodK K u) (s : G) : GoodK K (s * u * s⁻¹) := by
  intro J hJ hbar
  have hJ' : IsPCompIn 2 (centralizer ({u} : Set G)) (cj s⁻¹ J) := by
    have h1 := Stage1.Thm2.Recip.isPCompIn_map_conj hJ s⁻¹
    have e : s⁻¹ * (s * u * s⁻¹) * s⁻¹⁻¹ = u := by group
    rwa [map_conj_centralizer_singleton, e] at h1
  obtain ⟨e⟩ := hbar
  have hq := h (cj s⁻¹ J) hJ' ⟨(kBarConjEquiv s⁻¹ J).symm.trans e⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ((MulAut.conj s⁻¹).subgroupMap J).symm hq

omit [Finite G] in
theorem exists_central_p {P : Subgroup G} {w : G} (hP4 : Nat.card P = 4)
    (hPc : ∀ p ∈ P, ∀ p' ∈ P, p * p' = p' * p) (hPs : ∀ p ∈ P, p * p = 1) (hw2 : w * w = 1)
    (hwP : ∀ p ∈ P, w * p * w⁻¹ ∈ P) : ∃ p ∈ P, p ≠ 1 ∧ w * p = p * w := by
  by_cases hcomm : ∀ p ∈ P, w * p = p * w
  · have hne : P ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hP4
      omega
    obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    exact ⟨p, hp, fun h => hp1 (Subtype.ext h), hcomm p hp⟩
  · push Not at hcomm
    obtain ⟨p₀, hp₀, hwp₀⟩ := hcomm
    have hw1 : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    set p₁ := w * p₀ * w⁻¹ with hp₁
    have hp₁P : p₁ ∈ P := hwP p₀ hp₀
    refine ⟨p₀ * p₁, P.mul_mem hp₀ hp₁P, ?_, ?_⟩
    · intro h
      apply hwp₀
      have h1 : p₀⁻¹ = p₀ := inv_eq_of_mul_eq_one_right (hPs p₀ hp₀)
      have h2 : p₁ = p₀ := by
        calc p₁ = p₀⁻¹ * (p₀ * p₁) := by group
          _ = p₀⁻¹ := by rw [h, mul_one]
          _ = p₀ := h1
      have : w * p₀ * w⁻¹ = p₀ := h2
      calc w * p₀ = (w * p₀ * w⁻¹) * w := by group
        _ = p₀ * w := by rw [this]
    · have hwp₁ : w * p₁ * w⁻¹ = p₀ := by
        rw [hp₁, hw1]
        calc w * (w * p₀ * w) * w = (w * w) * p₀ * (w * w) := by group
          _ = p₀ := by rw [hw2]; group
      have hwz : w * (p₀ * p₁) * w⁻¹ = p₀ * p₁ := by
        calc w * (p₀ * p₁) * w⁻¹ = (w * p₀ * w⁻¹) * (w * p₁ * w⁻¹) := by group
          _ = p₁ * p₀ := by rw [← hp₁, hwp₁]
          _ = p₀ * p₁ := hPc p₁ hp₁P p₀ hp₀
      calc w * (p₀ * p₁) = (w * (p₀ * p₁) * w⁻¹) * w := by group
        _ = p₀ * p₁ * w := by rw [hwz]

end Ctx

section Outer

variable {G : Type} [Group G] [Finite G]

theorem exists_outer_data (hG : C3Hyp G) (h102a : B_ivk_10_2a)
    {x y : G} {K T S : Subgroup G}
    (hstd : Th2Std x y K T S) (hrow : Th2Row.r4b.holds x y K T S) (c : Ctx x K T) :
    ∃ (a : G) (A : Subgroup G), a ∈ A ∧ A ≤ T ∧ CFSG.IsElementaryAbelian 2 ↥A ∧ 4 ≤ pRank 2 ↥A ∧
      a * a = 1 ∧ a ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K) ∧ ¬ ∀ p ∈ T ⊓ K, a * p = p * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL5, -, hr, hunb⟩ := hrow
  have hyout : y ∉ K ⊔ centralizerSection K (pPrimeCoreOf 2 K) := by
    obtain ⟨p, f, hp, hf, hP5, hLie⟩ := hL5
    have hP5' : p ^ f = 5 := hP5
    have hfm : HasL2Model (kBar K) IsFM9 :=
      ⟨p, f, hp, hf, by rw [hP5']; exact Or.inr ⟨by norm_num, Or.inl ⟨1, by norm_num⟩⟩, hLie⟩
    exact h102a G hG x y K hstd.v2ss.isV2Triple hfm
  obtain ⟨F, hFC, hFel, hFrk⟩ := exists_elemAbelian_pRank (centralizer ({x, y} : Set G))
  obtain ⟨A, hAT, hAel, hAF, a, ha, hnot⟩ :=
    Th2.L83.exists_outer_elemAbelian hstd c.KN hunb.2.2.1 hyout hunb.2.1 hFel hFC
  have hA4 : 4 ≤ pRank 2 ↥A := by omega
  obtain ⟨hAc, hAs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  have haT : a ∈ T := hAT ha
  have haC : a ∈ centralizer ({x} : Set G) := hstd.T_le_C haT
  have haR : a ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K) := by
    intro hR
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute c.PQ.comm hR
    apply hnot
    have hpC : p ∈ centralizer ({x} : Set G) := hstd.T_le_C hp.1
    have hqC : q ∈ centralizer ({x} : Set G) := hq.2.1
    have e : (⟨p * q, haC⟩ : ↥(centralizer ({x} : Set G))) = ⟨p, hpC⟩ * ⟨q, hqC⟩ := rfl
    have hq1 : C3.Layer1.Back.actHom c.KN ⟨q, hqC⟩ = 1 := by
      rw [C3.Layer1.Back.actHom_eq_one_iff_commutator_mem]
      intro k hk
      exact hq.2.2.2.2 k hk
    rw [e, map_mul, hq1, mul_one,
      C3.Layer1.Back.actHom_of_mem c.KN hp.2 hpC]
    exact ⟨_, rfl⟩
  have ha2 : a * a = 1 := hAs a ha
  refine ⟨a, A, ha, hAT, hAel, hA4, ha2, haR, fun hcomm => hnot ?_⟩
  set N : Subgroup ↥K := pPrimeCore 2 ↥K with hN
  set Pb : Subgroup (kBar K) := ((T ⊓ K).subgroupOf K).map (QuotientGroup.mk' N) with hPb
  have hbot : (T ⊓ K).subgroupOf K ⊓ N = ⊥ := by
    refine eq_bot_iff.2 fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := hk
    have hkO : (k : G) ∈ T ⊓ pPrimeCoreOf 2 K := ⟨(Subgroup.mem_subgroupOf.1 hk1).1, ⟨k, hk2, rfl⟩⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot K hstd.T_pGroup, Subgroup.mem_bot] at hkO
    exact Subgroup.mem_bot.2 (Subtype.ext hkO)
  have hPb4 : Nat.card ↥Pb = 4 := by
    have h1 := C3.Layer1.Thm1.card_eq_card_map_mul_card_inf_ker (QuotientGroup.mk' N) ((T ⊓ K).subgroupOf K)
    rw [QuotientGroup.ker_mk', hbot, Subgroup.card_bot, mul_one] at h1
    have h2 : Nat.card ↥((T ⊓ K).subgroupOf K) = Nat.card ↥(T ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv
    calc Nat.card ↥Pb = Nat.card ↥((T ⊓ K).subgroupOf K) := h1.symm
      _ = Nat.card ↥(T ⊓ K) := h2
      _ = 4 := c.P4
  obtain ⟨e5⟩ := c.e5
  obtain ⟨h, hh⟩ := C3.Layer1.Back.a5_aut_centralizer_inner e5 Pb hPb4
    (C3.Layer1.Back.actHom c.KN ⟨a, haC⟩) (by
      rintro _ ⟨k, hk, rfl⟩
      have hkP : (k : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.1 hk
      show C3.Layer1.Back.actHom c.KN ⟨a, haC⟩ (QuotientGroup.mk k) = QuotientGroup.mk k
      rw [C3.Layer1.Back.actHom_mk]
      congr 1
      apply Subtype.ext
      show a * (k : G) * a⁻¹ = (k : G)
      calc a * (k : G) * a⁻¹ = ((k : G) * a) * a⁻¹ := by rw [hcomm _ hkP]
        _ = (k : G) := by group)
  exact ⟨h, hh.symm⟩

omit [Finite G] in
theorem Ctx.Pn {x : G} {K T : Subgroup G} (c : Ctx x K T) (hTC : T ≤ centralizer ({x} : Set G)) :
    ∀ s ∈ T, ∀ p ∈ T ⊓ K, s * p * s⁻¹ ∈ T ⊓ K := fun s hs p hp =>
  ⟨T.mul_mem (T.mul_mem hs hp.1) (T.inv_mem hs), c.KN s (hTC hs) p hp.2⟩

omit [Finite G] in
theorem Ctx.Qn {x : G} {K T : Subgroup G} (c : Ctx x K T) (hTC : T ≤ centralizer ({x} : Set G)) :
    ∀ s ∈ T, ∀ q ∈ T ⊓ CxK x K, s * q * s⁻¹ ∈ T ⊓ CxK x K := by
  intro s hs q hq
  have hsN : s ∈ NxK x K := ⟨hTC hs, mem_normalizer_K_of_KN c.KN (hTC hs)⟩
  exact ⟨T.mul_mem (T.mul_mem hs hq.1) (T.inv_mem hs),
    (Subgroup.mem_normalizer_iff.1 (NxK_le_normalizer_CxK x K hsN) q).1 hq.2⟩

theorem card_inf_centralizer_le_two {P : Subgroup G} {a : G} (hP4 : Nat.card P = 4)
    (hnc : ¬ ∀ p ∈ P, a * p = p * a) : Nat.card ↥(P ⊓ centralizer ({a} : Set G)) ≤ 2 := by
  have hCyP : P ⊓ centralizer ({a} : Set G) ≤ P := inf_le_left
  have hlt : Nat.card ↥(P ⊓ centralizer ({a} : Set G)) < Nat.card P := by
    by_contra hge
    push Not at hge
    have hCyeq := Subgroup.eq_of_le_of_card_ge hCyP hge
    apply hnc
    intro p hp
    have : p ∈ P ⊓ centralizer ({a} : Set G) := by rw [hCyeq]; exact hp
    exact (mem_centralizer_singleton_iff.1 this.2).symm
  have hdvd : Nat.card ↥(P ⊓ centralizer ({a} : Set G)) ∣ 4 := hP4 ▸ Subgroup.card_dvd_of_le hCyP
  rw [hP4] at hlt
  by_contra hgt
  push Not at hgt
  have h3 : Nat.card ↥(P ⊓ centralizer ({a} : Set G)) = 3 := by omega
  rw [h3] at hdvd
  exact absurd hdvd (by norm_num)

theorem Ctx.relIndex_R {x : G} {K T : Subgroup G} (c : Ctx x K T) :
    ((T ⊓ K) ⊔ (T ⊓ CxK x K)).relIndex T ≤ 2 := by
  have hRT : (T ⊓ K) ⊔ (T ⊓ CxK x K) ≤ T := sup_le inf_le_left inf_le_left
  have hcardR : Nat.card ↥((T ⊓ K) ⊔ (T ⊓ CxK x K)) = 4 * Nat.card ↥(T ⊓ CxK x K) := by
    rw [c.PQ.card_sup le_rfl le_rfl, c.P4]
  have h1 := Subgroup.relIndex_mul_card ((T ⊓ K) ⊔ (T ⊓ CxK x K)) T
  rw [inf_eq_left.2 hRT, hcardR] at h1
  have hQ : 0 < Nat.card ↥(T ⊓ CxK x K) := Nat.card_pos
  have hTle := c.Tle
  by_contra h
  push Not at h
  have h3 : 3 * (4 * Nat.card ↥(T ⊓ CxK x K)) ≤
      ((T ⊓ K) ⊔ (T ⊓ CxK x K)).relIndex T * (4 * Nat.card ↥(T ⊓ CxK x K)) :=
    Nat.mul_le_mul_right _ h
  omega

theorem Qrank_of_std (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) {x y : G}
    {K T S : Subgroup G} (hstd : Th2Std x y K T S) :
    ∀ E : Subgroup G, E ≤ T ⊓ CxK x K → (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) →
      (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 4 := by
  intro E hE hc hs
  have hEA : CFSG.IsElementaryAbelian 2 ↥E :=
    C3.Layer1.Back.isElementaryAbelian_of_forall (fun u hu v hv => hc u hu v hv) (fun u hu => hs u hu)
  have h2 := hstd.pRank_le_two_of_le_Q hG hL34 h102 hE
  rw [C3.Layer1.Back.card_eq_two_pow_pRank hEA]
  calc 2 ^ pRank 2 ↥E ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
    _ = 4 := by norm_num

theorem exists_klein_Qy {x : G} {K T : Subgroup G} (c : Ctx x K T)
    (hQrank : ∀ E : Subgroup G, E ≤ T ⊓ CxK x K → (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) →
      (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 4)
    (hTC : T ≤ centralizer ({x} : Set G)) {a : G} {A : Subgroup G} (haA : a ∈ A) (hAT : A ≤ T)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA4 : 4 ≤ pRank 2 ↥A)
    (haP : ¬ ∀ p ∈ T ⊓ K, a * p = p * a) :
    ∃ a₁ b₁ : G, a₁ ∈ T ⊓ CxK x K ∧ b₁ ∈ T ⊓ CxK x K ∧ a₁ * a₁ = 1 ∧ b₁ * b₁ = 1 ∧
      a₁ * b₁ = b₁ * a₁ ∧ a₁ ≠ 1 ∧ b₁ ≠ 1 ∧ a₁ ≠ b₁ ∧ a * a₁ = a₁ * a ∧ a * b₁ = b₁ * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAc, hAs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  set R : Subgroup G := (T ⊓ K) ⊔ (T ⊓ CxK x K) with hR
  have hRT : R ≤ T := sup_le inf_le_left inf_le_left
  have haT : a ∈ T := hAT haA
  have hKaN := c.Pn hTC
  have hKaQ := c.Qn hTC
  set E' : Subgroup G := R ⊓ A with hE'
  have hE'A : E' ≤ A := inf_le_right
  have hA16 : 16 ≤ Nat.card A := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hAel]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥A := Nat.pow_le_pow_right (by norm_num) hA4
  have hAE' : Nat.card A ≤ 2 * Nat.card E' := by
    have h1 := Subgroup.relIndex_mul_card R A
    have hne : R.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : R.relIndex A ≤ 2 := (Subgroup.relIndex_le_of_le_right hAT hne).trans c.relIndex_R
    rw [← h1]
    exact Nat.mul_le_mul_right _ h2
  have hE'R : E' ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := inf_le_left
  have hE'el : CFSG.IsElementaryAbelian 2 ↥E' := isElementaryAbelian_le hAel hE'A
  have hproj : E' ≤ c.PQ.projP E' ⊔ c.PQ.projQ E' := c.PQ.le_projP_sup_projQ hE'R
  have hcardle : Nat.card E' ≤ Nat.card ↥(c.PQ.projP E') * Nat.card ↥(c.PQ.projQ E') := by
    rw [← c.PQ.card_sup (c.PQ.projP_le_left E') (c.PQ.projQ_le_right E')]
    exact Subgroup.card_le_of_le hproj
  have hcomm_comp : ∀ p ∈ T ⊓ K, ∀ q ∈ T ⊓ CxK x K, p * q ∈ A → a * p = p * a ∧ a * q = q * a := by
    intro p hp q hq hpq
    have h1 : a * (p * q) * a⁻¹ = p * q := by
      calc a * (p * q) * a⁻¹ = (p * q * a) * a⁻¹ := by rw [hAc a haA _ hpq]
        _ = p * q := by group
    have h2 : (a * p * a⁻¹) * (a * q * a⁻¹) = p * q := by
      rw [← h1]; group
    obtain ⟨h3, h4⟩ := c.PQ.mul_cancel (hKaN a haT p hp) hp (hKaQ a haT q hq) hq h2
    constructor
    · calc a * p = (a * p * a⁻¹) * a := by group
        _ = p * a := by rw [h3]
    · calc a * q = (a * q * a⁻¹) * a := by group
        _ = q * a := by rw [h4]
  have hPcomp : c.PQ.projP E' ≤ (T ⊓ K) ⊓ centralizer ({a} : Set G) := by
    intro p hp
    obtain ⟨hpP, q, hq, hpq⟩ := hp
    exact ⟨hpP, mem_centralizer_singleton_iff.2 (hcomm_comp p hpP q hq (hE'A hpq)).1.symm⟩
  have hPcard : Nat.card ↥(c.PQ.projP E') ≤ 2 :=
    (Subgroup.card_le_of_le hPcomp).trans (card_inf_centralizer_le_two c.P4 haP)
  have hQcard4 : 4 ≤ Nat.card ↥(c.PQ.projQ E') := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card ↥(c.PQ.projP E') * Nat.card ↥(c.PQ.projQ E') ≤ 2 * 3 :=
      Nat.mul_le_mul hPcard (by omega)
    omega
  have hQel : CFSG.IsElementaryAbelian 2 ↥(c.PQ.projQ E') := c.PQ.isElementaryAbelian_projQ hE'el
  obtain ⟨hQc, hQs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hQel
  have hQQ : c.PQ.projQ E' ≤ T ⊓ CxK x K := c.PQ.projQ_le_right E'
  have hQcard : Nat.card ↥(c.PQ.projQ E') = 4 :=
    le_antisymm (hQrank _ hQQ (fun e he e' he' => hQc e he e' he') (fun e he => hQs e he)) hQcard4
  obtain ⟨a₁, b₁, ha₁, hb₁, ha₁1, hb₁1, hab₁, hel⟩ := klein_gens hQcard hQc hQs
  have hcentr : ∀ q ∈ c.PQ.projQ E', a * q = q * a := by
    intro q hq
    obtain ⟨hqQ, p, hp, hpq⟩ := hq
    exact (hcomm_comp p hp q hqQ (hE'A hpq)).2
  exact ⟨a₁, b₁, hQQ ha₁, hQQ hb₁, hQs a₁ ha₁, hQs b₁ hb₁, hQc a₁ ha₁ b₁ hb₁, ha₁1, hb₁1, hab₁,
    hcentr a₁ ha₁, hcentr b₁ hb₁⟩

theorem Ctx.card_T_eq {x : G} {K T : Subgroup G} (c : Ctx x K T) {s : G} (hsT : s ∈ T)
    (hsR : s ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K)) : Nat.card ↥T = 8 * Nat.card ↥(T ⊓ CxK x K) := by
  have hRT : (T ⊓ K) ⊔ (T ⊓ CxK x K) ≤ T := sup_le inf_le_left inf_le_left
  have hcardR : Nat.card ↥((T ⊓ K) ⊔ (T ⊓ CxK x K)) = 4 * Nat.card ↥(T ⊓ CxK x K) := by
    rw [c.PQ.card_sup le_rfl le_rfl, c.P4]
  have hne : (T ⊓ K) ⊔ (T ⊓ CxK x K) ≠ T := fun h => hsR (by rw [h]; exact hsT)
  have hlt : Nat.card ↥((T ⊓ K) ⊔ (T ⊓ CxK x K)) < Nat.card ↥T := by
    by_contra hge
    push Not at hge
    exact hne (Subgroup.eq_of_le_of_card_ge hRT hge)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hRT
  have hQ : 0 < Nat.card ↥(T ⊓ CxK x K) := Nat.card_pos
  rw [hcardR] at hm hlt
  have hTle := c.Tle
  have hm2 : 2 ≤ m := by
    by_contra h2
    push Not at h2
    interval_cases m <;> omega
  have hm3 : m ≤ 2 := by
    by_contra h3
    push Not at h3
    have : 4 * Nat.card ↥(T ⊓ CxK x K) * 3 ≤ 4 * Nat.card ↥(T ⊓ CxK x K) * m :=
      Nat.mul_le_mul_left _ h3
    omega
  have : m = 2 := le_antisymm hm3 hm2
  subst this
  omega

theorem exists_B0 {x : G} {K T : Subgroup G} (c : Ctx x K T) (hTC : T ≤ centralizer ({x} : Set G))
    {a b w : G} (haQ : a ∈ T ⊓ CxK x K) (hbQ : b ∈ T ⊓ CxK x K) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab' : a ≠ b) (hwT : w ∈ T) (hw2 : w * w = 1)
    (hwR : w ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K)) (hwa : w * a = a * w) (hwb : w * b = b * w) :
    ∃ B₀ : Subgroup G, B₀ ≤ T ∧ CFSG.IsElementaryAbelian 2 ↥B₀ ∧ 4 ≤ pRank 2 ↥B₀ ∧ a ∈ B₀ ∧
      b ∈ B₀ ∧ w ∈ B₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hel : ∀ {z : G}, orderOf z = 2 → CFSG.IsElementaryAbelian 2 ↥(zpowers z) := fun h =>
    Th2.isElementaryAbelian_zpowers_of_orderOf_two h
  obtain ⟨hPc, hPs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian c.PEA
  obtain ⟨p, hpP, hp1, hwp⟩ := exists_central_p c.P4 hPc hPs hw2 (fun p hp => c.Pn hTC w hwT p hp)
  have ha2' : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hb2' : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hwR (one_mem _)
  have hw2' : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hp2' : orderOf p = 2 := orderOf_eq_prime (by rw [sq]; exact hPs p hpP) hp1
  obtain ⟨hVcard, hVel⟩ := klein_facts ha2 hb2 hab ha1 hb1 hab'
  set V : Subgroup G := zpowers a ⊔ zpowers b with hV
  have hVQ : V ≤ T ⊓ CxK x K := sup_le (zpowers_le.2 haQ) (zpowers_le.2 hbQ)
  have hVEA : CFSG.IsElementaryAbelian 2 ↥V :=
    isElementaryAbelian_sup (hel ha2') (hel hb2') fun k hk l hl => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hk
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hl
      exact (Commute.zpow_zpow (show Commute a b from hab) m n).eq
  have hpPP : zpowers p ≤ T ⊓ K := zpowers_le.2 hpP
  set B₁ : Subgroup G := zpowers p ⊔ V with hB₁
  have hB₁card : Nat.card B₁ = 8 := by
    rw [hB₁, c.PQ.card_sup hpPP hVQ, Nat.card_zpowers, hp2', hVcard]
  have hB₁EA : CFSG.IsElementaryAbelian 2 ↥B₁ := c.PQ.isElementaryAbelian_sup' (hel hp2') hVEA hpPP hVQ
  have hB₁R : B₁ ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := sup_le (hpPP.trans le_sup_left) (hVQ.trans le_sup_right)
  have hB₁w : B₁ ≤ centralizer ({w} : Set G) := by
    refine sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hwp.symm)) (sup_le ?_ ?_)
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hwa.symm)
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hwb.symm)
  have hcd : CommDisj B₁ (zpowers w) := by
    refine ⟨fun k hk l hl => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hl
      exact (Commute.zpow_right (show Commute k w from mem_centralizer_singleton_iff.1 (hB₁w hk)) m).eq
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two hw2' hz.2 with h0 | h0
      · simp [h0]
      · exact absurd (hB₁R (h0 ▸ hz.1)) hwR
  set B₀ : Subgroup G := B₁ ⊔ zpowers w with hB₀
  have hB₀T : B₀ ≤ T := sup_le (hB₁R.trans (sup_le inf_le_left inf_le_left)) (zpowers_le.2 hwT)
  have hB₀EA : CFSG.IsElementaryAbelian 2 ↥B₀ :=
    hcd.isElementaryAbelian_sup' hB₁EA (hel hw2') le_rfl le_rfl
  have hB₀card : Nat.card B₀ = 16 := by
    rw [hB₀, hcd.card_sup le_rfl le_rfl, hB₁card, Nat.card_zpowers, hw2']
  have hrk : 4 ≤ pRank 2 ↥B₀ := by
    have h := C3.Layer1.Back.card_eq_two_pow_pRank hB₀EA
    rw [hB₀card] at h
    have h4 : (2 : ℕ) ^ 4 = 2 ^ pRank 2 ↥B₀ := by simpa using h
    exact (Nat.pow_right_injective le_rfl h4).le
  refine ⟨B₀, hB₀T, hB₀EA, hrk, ?_, ?_, ?_⟩
  · exact mem_sup_left (mem_sup_right (mem_sup_left (mem_zpowers a)))
  · exact mem_sup_left (mem_sup_right (mem_sup_right (mem_zpowers b)))
  · exact mem_sup_right (mem_zpowers w)

theorem exists_pumpup_Q (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) {x y : G}
    {K T S : Subgroup G} (hstd : Th2Std x y K T S) {u : G} (hu : u ∈ T ⊓ CxK x K)
    (hu2 : orderOf u = 2) : ∃ Je : Subgroup G, PumpUpLT 2 x K u Je := by
  obtain ⟨hcen, hP⟩ := hstd.centerless_and_shape hG hL34 h102
  have hILo : IsILo 2 x K := (hstd.v2ss.isV2Triple.2.1 : IsTwoTerminal x K).1
  have hrank := hstd.three_le_pRank_centralizer hcen hP hu hu2
  exact TwoThin.exists_pumpup_of_involution hstd.orderOf_x hu2 hstd.comp hu.2.1 hu.2.2 hILo hrank

theorem goodK_outer (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) {x y : G}
    {K T S : Subgroup G} (hstd : Th2Std x y K T S) (c : Ctx x K T)
    (h713 : ∀ B₀ : Subgroup G, B₀ ≤ T → CFSG.IsElementaryAbelian 2 ↥B₀ → 4 ≤ pRank 2 ↥B₀ →
      ∀ u ∈ B₀, u ∈ T ⊓ CxK x K → orderOf u = 2 → ∀ y' ∈ B₀, y' ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K) →
        ∀ J' : Subgroup G, PumpUpLT 2 x K u J' → CFSG.IsQuasisimple ↥J')
    {u w : G} (huQ : u ∈ T ⊓ CxK x K) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hux : u ≠ x) (hwT : w ∈ T)
    (hwR : w ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K)) (hw2 : w * w = 1) (hwu : w * u = u * w) : GoodK K u := by
  have hxQ : x ∈ T ⊓ CxK x K := ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hTC := hstd.T_le_C
  have hx2 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hstd.orderOf_x
  have hx1 : x ≠ 1 := by
    intro h
    have := hstd.orderOf_x
    rw [h, orderOf_one] at this
    omega
  have hxu : x * u = u * x := (mem_centralizer_singleton_iff.1 (hTC huQ.1)).symm
  have hwx : w * x = x * w := mem_centralizer_singleton_iff.1 (hTC hwT)
  obtain ⟨B₀, hB₀T, hB₀EA, hB₀rk, hxB, huB, hwB⟩ :=
    exists_B0 c hTC hxQ huQ hx2 hu2 hxu hx1 hu1 (fun h => hux h.symm) hwT hw2 hwR hwx hwu
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  intro J' hJ' hbar
  obtain ⟨Je, hJe⟩ := exists_pumpup_Q hG hL34 h102 hstd huQ hu2'
  have hJ'e : J' = Je := hstd.eq_pumpup_of_isPCompIn hG hL34 h102 hu2' hJe hJ' hbar
  rw [hJ'e]
  exact h713 B₀ hB₀T hB₀EA hB₀rk u huB huQ hu2' w hwB hwR Je hJe

theorem goodK_x (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) {x y : G}
    {K T S : Subgroup G} (hstd : Th2Std x y K T S) (c : Ctx x K T)
    (h713 : ∀ B₀ : Subgroup G, B₀ ≤ T → CFSG.IsElementaryAbelian 2 ↥B₀ → 4 ≤ pRank 2 ↥B₀ →
      ∀ u ∈ B₀, u ∈ T ⊓ CxK x K → orderOf u = 2 → ∀ y' ∈ B₀, y' ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K) →
        ∀ J' : Subgroup G, PumpUpLT 2 x K u J' → CFSG.IsQuasisimple ↥J')
    {u₀ w : G} (hu₀Q : u₀ ∈ T ⊓ CxK x K) (hu₀2 : u₀ * u₀ = 1) (hu₀1 : u₀ ≠ 1) (hu₀x : u₀ ≠ x)
    (hwT : w ∈ T) (hwR : w ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K)) (hw2 : w * w = 1) (hwu : w * u₀ = u₀ * w) :
    GoodK K x := by
  have hxQ : x ∈ T ⊓ CxK x K := ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hTC := hstd.T_le_C
  have hx2 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hstd.orderOf_x
  have hx1 : x ≠ 1 := by
    intro h
    have := hstd.orderOf_x
    rw [h, orderOf_one] at this
    omega
  have hxu : x * u₀ = u₀ * x := (mem_centralizer_singleton_iff.1 (hTC hu₀Q.1)).symm
  have hwx : w * x = x * w := mem_centralizer_singleton_iff.1 (hTC hwT)
  obtain ⟨B₀, hB₀T, hB₀EA, hB₀rk, hxB, -, hwB⟩ :=
    exists_B0 c hTC hxQ hu₀Q hx2 hu₀2 hxu hx1 hu₀1 (fun h => hu₀x h.symm) hwT hw2 hwR hwx hwu
  obtain ⟨hpumpx, hKK⟩ := pumpUp_eq_self hstd.K_le_C hstd.comp
  have hILo : IsILo 2 x K := (hstd.v2ss.isV2Triple.2.1 : IsTwoTerminal x K).1
  have hP0 : PumpUpLT 2 x K x K :=
    ⟨hILo, hILo, mem_centralizer_singleton_iff.2 rfl, hstd.x_mem_CxK.2, by rw [hpumpx]; exact hKK⟩
  have hKq : CFSG.IsQuasisimple ↥K :=
    h713 B₀ hB₀T hB₀EA hB₀rk x hxB hxQ hstd.orderOf_x w hwB hwR K hP0
  intro J' hJ' hbar
  have hJ'e : J' = K := hstd.eq_pumpup_of_isPCompIn hG hL34 h102 hstd.orderOf_x hP0 hJ' hbar
  rw [hJ'e]
  exact hKq

omit [Finite G] in
theorem fusC_std {x : G} {K T : Subgroup G} (c : Ctx x K T) {t : G} (htQ : t ∈ T ⊓ CxK x K) :
    ∀ g : G, g * x = x * g → g⁻¹ * t * g ∈ T → g⁻¹ * t * g ∈ T ⊓ CxK x K := by
  intro g hg ht₁
  have hgC : g⁻¹ ∈ centralizer ({x} : Set G) := by
    refine mem_centralizer_singleton_iff.2 ?_
    calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hg]
      _ = x * g⁻¹ := by group
  have hgN : g⁻¹ ∈ NxK x K := ⟨hgC, mem_normalizer_K_of_KN c.KN hgC⟩
  refine ⟨ht₁, ?_⟩
  have := (Subgroup.mem_normalizer_iff.1 (NxK_le_normalizer_CxK x K hgN) t).1 htQ.2
  simpa using this

theorem fus_std (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) {x y : G}
    {K T S : Subgroup G} (hstd : Th2Std x y K T S) {t : G} (htQ : t ∈ T ⊓ CxK x K) {J : Subgroup G}
    (hJ : PumpUpLT 2 x K t J) (hJnq : ¬ CFSG.IsQuasisimple ↥J) (hJbar : Nonempty (kBar J ≃* kBar K)) :
    ∀ g : G, g⁻¹ * x * g ∈ T ⊓ CxK x K → GoodK K (g⁻¹ * x * g) → g⁻¹ * t * g ∈ T →
      (g⁻¹ * t * g ∈ T ⊓ CxK x K ∧ ¬ GoodK K (g⁻¹ * t * g)) := by
  intro g hu₁Q hGu₁ ht₁T
  have hu₁2 : orderOf (g⁻¹ * x * g) = 2 := by
    have := orderOf_conj' g⁻¹ x
    rw [inv_inv] at this
    rw [this]; exact hstd.orderOf_x
  have hterm : IsTwoTerminal x K := hstd.v2ss.isV2Triple.2.1
  have hK' : IsPCompIn 2 (centralizer ({g⁻¹ * x * g} : Set G)) (cj g⁻¹ K) := by
    have h1 := Stage1.Thm2.Recip.isPCompIn_map_conj hstd.comp g⁻¹
    have e : g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g := by rw [inv_inv]
    rwa [map_conj_centralizer_singleton, e] at h1
  have hK'bar : Nonempty (kBar (cj g⁻¹ K) ≃* kBar K) := ⟨(kBarConjEquiv g⁻¹ K).symm⟩
  have hqK' : CFSG.IsQuasisimple ↥(cj g⁻¹ K) := hGu₁ _ hK' hK'bar
  have hqK : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ((MulAut.conj g⁻¹).subgroupMap K).symm hqK'
  obtain ⟨Je, hJe⟩ := exists_pumpup_Q hG hL34 h102 hstd hu₁Q hu₁2
  have hJeq : cj g⁻¹ K = Je := hstd.eq_pumpup_of_isPCompIn hG hL34 h102 hu₁2 hJe hK' hK'bar
  obtain ⟨hbJe, -, -, -⟩ := hstd.pumpup_facts hG hL34 h102 hu₁2 hJe
  have hqJe : CFSG.IsQuasisimple ↥Je := hGu₁ Je hJe.2.1.2.2 hbJe
  have htriv : IsTrivialPumpupAt x K (g⁻¹ * x * g) := fun K' hK'' => hterm.2.1 _ K' hK''
  have hKJe : K = Je :=
    Th2.P72c.eq_pumpup_of_quasisimple hstd.comp hqK hu₁Q.2.2 hJe htriv hqJe
  have hKK' : cj g⁻¹ K = K := hJeq.trans hKJe.symm
  refine ⟨⟨ht₁T, ?_⟩, ?_⟩
  · refine ⟨hstd.T_le_C ht₁T, ?_⟩
    have h1 := Stage1.Thm2.Recip.mem_cSec_cj htQ.2.2 g⁻¹
    have hKK'' : Stage1.Thm2.Recip.cj g⁻¹ K = K := hKK'
    rw [hKK''] at h1
    have e : g⁻¹ * t * g⁻¹⁻¹ = g⁻¹ * t * g := by rw [inv_inv]
    rw [e] at h1
    exact h1
  · intro hG₁
    have hJ' : IsPCompIn 2 (centralizer ({g⁻¹ * t * g} : Set G)) (cj g⁻¹ J) := by
      have h1 := Stage1.Thm2.Recip.isPCompIn_map_conj hJ.2.1.2.2 g⁻¹
      have e : g⁻¹ * t * g⁻¹⁻¹ = g⁻¹ * t * g := by rw [inv_inv]
      rwa [map_conj_centralizer_singleton, e] at h1
    obtain ⟨eJ⟩ := hJbar
    have hq := hG₁ (cj g⁻¹ J) hJ' ⟨(kBarConjEquiv g⁻¹ J).symm.trans eJ⟩
    exact hJnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv ((MulAut.conj g⁻¹).subgroupMap J).symm hq)

omit [Finite G] in
theorem perfect_of_simple_nonabelian [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
      Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · exact h

theorem exists_setup714 (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem)
    (h102 : B_ivk_10_2) (h102a : B_ivk_10_2a) {x y : G} {K T S : Subgroup G}
    (hstd : Th2Std x y K T S) (hrow : Th2Row.r4b.holds x y K T S) {B : Subgroup G} {t : G}
    {J : Subgroup G} (hpick : Th2Pick .r4b x y K T S B t J)
    (h713 : ∀ B₀ : Subgroup G, B₀ ≤ T → CFSG.IsElementaryAbelian 2 ↥B₀ → 4 ≤ pRank 2 ↥B₀ →
      ∀ u ∈ B₀, u ∈ T ⊓ CxK x K → orderOf u = 2 → ∀ y' ∈ B₀, y' ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K) →
        ∀ J' : Subgroup G, PumpUpLT 2 x K u J' → CFSG.IsQuasisimple ↥J') :
    ∃ a : G, Setup714 x t a T (T ⊓ CxK x K) (T ⊓ K) (GoodK K) ∧
      (∀ g : G, g⁻¹ * x * g ∈ T ⊓ CxK x K → GoodK K (g⁻¹ * x * g) → g⁻¹ * t * g ∈ T →
        g⁻¹ * t * g ∈ T ⊓ CxK x K ∧ ¬ GoodK K (g⁻¹ * t * g)) ∧
      (∀ g : G, g * x = x * g → g⁻¹ * t * g ∈ T → g⁻¹ * t * g ∈ T ⊓ CxK x K) := by
  classical
  have c := ctx_of_std (by rw [hG.pRank_eq_four]) hstd hrow.1
  obtain ⟨a, A, haA, hAT, hAel, hA4, ha2, haR, haP⟩ := exists_outer_data hG h102a hstd hrow c
  have hTC := hstd.T_le_C
  have hQrank := Qrank_of_std hG hL34 h102 hstd
  obtain ⟨a₁, b₁, ha₁Q, hb₁Q, ha₁2, hb₁2, hab, ha₁1, hb₁1, hab', hya, hyb⟩ :=
    exists_klein_Qy c hQrank hTC haA hAT hAel hA4 haP
  have haT : a ∈ T := hAT haA
  have htQ : t ∈ T ⊓ CxK x K := hpick.t_mem.2
  have ht2' : orderOf t = 2 := hpick.t_two
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht2'
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2'
    omega
  have hx2 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hstd.orderOf_x
  have hx1 : x ≠ 1 := by
    intro h
    have := hstd.orderOf_x
    rw [h, orderOf_one] at this
    omega
  have hbad : ¬ GoodK K t := fun h => hpick.nonqs (h J hpick.pump.2.1.2.2 hpick.bar)
  have hgoodx : GoodK K x := by
    by_cases ha₁x : a₁ = x
    · exact goodK_x hG hL34 h102 hstd c h713 hb₁Q hb₁2 hb₁1 (fun h => hab' (ha₁x.trans h.symm)) haT
        haR ha2 hyb
    · exact goodK_x hG hL34 h102 hstd c h713 ha₁Q ha₁2 ha₁1 ha₁x haT haR ha2 hya
  have htx : t ≠ x := by
    intro h
    apply hbad
    rw [h]
    exact hgoodx
  obtain ⟨hPc, hPs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian c.PEA
  refine ⟨a, ⟨hstd.T_pGroup, inf_le_left, c.Qn hTC, inf_le_left, c.Pn hTC, c.PQ.comm, c.PQ.inf, hPc, hPs,
    c.P4, c.card_T_eq haT haR, hQrank, ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩, hx2, hx1,
    fun s hs => mem_centralizer_singleton_iff.1 (hTC hs), haT, ha2, haR, haP, htQ, ht2, ht1, htx,
    ⟨a₁, b₁, ha₁Q, hb₁Q, ha₁2, hb₁2, hab, ha₁1, hb₁1, hab', hya, hyb⟩,
    fun s _ u h => h.conj s,
    fun u huQ hu2 hu1 hux w hwT hwR hw2 hwu =>
      goodK_outer hG hL34 h102 hstd c h713 huQ hu2 hu1 hux hwT hwR hw2 hwu,
    hgoodx, hbad⟩,
    fus_std hG hL34 h102 hstd htQ hpick.pump hpick.nonqs hpick.bar, fusC_std c htQ⟩

end Outer

end CFSG.GH74.GLS.Th2.R714

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.R714

theorem b_row4b_714_of (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (h102a : B_ivk_10_2a) : B_row4b_714 := by
  intro G _ _ hG x y K T S hstd hnt hrow hbal B t J hpick hE2 hθ h713
  obtain ⟨a, hS, hfus, hfusC⟩ := exists_setup714 hG hL34 h102 h102a hstd hrow hpick h713
  have : IsSimpleGroup G := hG.kproper.1
  have hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := perfect_of_simple_nonabelian hG.kproper.2.1
  exact hS.false_of_transfer Stage1.Thm3.Sec5.ig_15_16_ext_thm hperf hstd.sylowS hstd.T_le_S
    hstd.setup.sylowT hfus hfusC

theorem b_thm2_p72c_row4b_proved (hL34 : B_gen4_noL34_elem)
    (h102 : B_ivk_10_2) (h102a : B_ivk_10_2a) (hKG : B_ivk_oddcent) (h218 : B_IG_21_8)
    (h2110 : B_IG_21_10) : B_thm2_p72c_row4b :=
  b_thm2_p72c_row4b_of_leaf hL34 h102 h102a hKG h218 h2110 (b_row4b_714_of hL34 h102 h102a)

end CFSG.GH74.GLS
