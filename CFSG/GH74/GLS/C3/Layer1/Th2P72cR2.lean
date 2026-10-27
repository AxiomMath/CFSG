module





public import CFSG.GH74.GLS.C3.Layer1.Th2P72cB
public import CFSG.GH74.GLS.C3.Layer1.Th2P617
public import CFSG.GH74.GLS.C3.Layer1.Th2P615
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.GH74.GLS.C3.Layer1.Th2P812Rows
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P72c

section Rows

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem pRank_eq_two_of_rankTwoShape {P : Subgroup G} (hP : RankTwoShape P) : pRank 2 ↥P = 2 := by
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  obtain ⟨E, hEP, hEel, hErk⟩ := exists_elemAbelian_pRank P
  have h1 := C3.Layer1.Back.pRank_mono' hU.1
  rw [pRank_of_isFourSub hU] at h1
  have h2 := hP.1 E hEP hEel
  have h3 := C3.Layer1.Back.card_eq_two_pow_pRank hEel
  by_contra hne
  have h4 : 3 ≤ pRank 2 ↥E := by omega
  have h5 : 2 ^ 3 ≤ 2 ^ pRank 2 ↥E := Nat.pow_le_pow_right (by norm_num) h4
  omega

theorem Th2Std.pumpup_facts (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (h : Th2Std x y K T S) {t : G} (ht2 : orderOf t = 2) {J : Subgroup G} (hJ : PumpUpLT 2 x K t J) :
    Nonempty (kBar J ≃* kBar K) ∧ CenterlessBar J ∧ 2 ≤ pRank 2 ↥J ∧
      ∀ g ∈ centralizer ({t} : Set G), g ∈ normalizer (J : Set G) := by
  obtain ⟨hcen, hP⟩ := h.centerless_and_shape hG hL34 h102
  have hterm : IsTwoTerminal x K := h.v2ss.isV2Triple.2.1
  obtain ⟨-, ⟨eJK⟩⟩ := hterm.2.1 t J hJ
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hJ.2.1.2.2
  have hJcen : CenterlessBar J := by
    intro a ha
    apply eJK.injective
    rw [map_one]
    apply hcen
    intro b
    obtain ⟨c, rfl⟩ := eJK.surjective b
    rw [← map_mul, ← map_mul, ha c]
  have hodd : ∀ X : Subgroup G, ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥X) := by
    intro X
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hrJ : pRank 2 (kBar J) = pRank 2 ↥J :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
      (pPrimeCore 2 ↥J) (hodd J)
  have hrK : pRank 2 (kBar K) = pRank 2 ↥K :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
      (pPrimeCore 2 ↥K) (hodd K)
  have hrJK : pRank 2 (kBar J) = pRank 2 (kBar K) :=
    CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two eJK
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  have hK2 : 2 ≤ pRank 2 ↥K := by
    have := C3.Layer1.Back.pRank_mono' (hU.1.trans inf_le_right : U ≤ K)
    rw [pRank_of_isFourSub hU] at this
    exact this
  have hJ2 : 2 ≤ pRank 2 ↥J := by omega
  refine ⟨⟨eJK⟩, hJcen, hJ2, fun g hg => ?_⟩
  exact Th2.Obs.mem_normalizer_of_pRank_le_four_cent hG.pRank_eq_four.le ht2 hJc hJcen hJ2 hg

theorem Th2Std.exists_isS_Q_mem (h : Th2Std x y K T S) (h2 : 2 ≤ pRank 2 ↥(CxK x K))
    {t : G} (htQ : t ∈ T ⊓ CxK x K) (ht2 : orderOf t = 2) :
    ∃ E : Subgroup G, t ∈ E ∧ IsS (T ⊓ CxK x K) E ∧ 2 ≤ pRank 2 ↥E := by
  have hQ : IsPGroup 2 ↥(T ⊓ CxK x K) := h.T_pGroup.to_le inf_le_left
  obtain ⟨E₀, hE₀, hE₀rk⟩ := h.exists_isS_Q' h2
  have hQne : (T ⊓ CxK x K) ≠ ⊥ := by
    intro h0
    have : t ∈ (⊥ : Subgroup G) := h0 ▸ htQ
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at ht2
    omega
  obtain ⟨z, hzQ, hz2, hzc⟩ := Th2.exists_central_involution hQ hQne
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  have htel := Th2.isElementaryAbelian_zpowers_of_orderOf_two ht2
  obtain ⟨E, htE, hE, hErk⟩ := Th2.exists_isS_two_le (zpowers_le.2 htQ) htel hE₀ hE₀rk hzQ hz1
    (mul_self_eq_one_of_orderOf_eq_two hz2) hzc
  exact ⟨E, htE (mem_zpowers t), hE, hErk⟩

omit [Finite G] in
theorem Th2Std.x_mem_of_isS {X B : Subgroup G} (h : Th2Std x y K T S) (hX : X ≤ T) (hxX : x ∈ X)
    (hB : IsS X B) : x ∈ B :=
  mem_of_isS_of_central hB hxX (mul_self_eq_one_of_orderOf_eq_two h.orderOf_x)
    (fun _ hq => (mem_centralizer_singleton_iff.1 (h.T_le_C (hX hq))).symm)

theorem Th2Std.sup_facts (h : Th2Std x y K T S) (hcen : CenterlessBar K) (hP : RankTwoShape (T ⊓ K))
    {U E : Subgroup G} (hU : IsFourSub (T ⊓ K) U) (hE : IsS (T ⊓ CxK x K) E) (hErk : 2 ≤ pRank 2 ↥E) :
    IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) (U ⊔ E) ∧ U ⊔ E ≤ T ∧
      CFSG.IsElementaryAbelian 2 ↥(U ⊔ E) ∧ 4 ≤ pRank 2 ↥(U ⊔ E) ∧ x ∈ U ⊔ E ∧
      pRank 2 ↥((U ⊔ E) ⊓ (T ⊓ K)) = pRank 2 ↥(T ⊓ K) := by
  have hPQ := h.commDisj hcen
  have hSn := (isS_sup_iff hPQ hP _).2 ⟨U, hU, E, hE, hErk, rfl⟩
  have hel := hPQ.isElementaryAbelian_sup' hU.2.1 hE.2.1 hU.1 hE.1
  have hrk : pRank 2 ↥(U ⊔ E) = 2 + pRank 2 ↥E := by
    rw [hPQ.pRank_sup hU.2.1 hE.2.1 hU.1 hE.1, pRank_of_isFourSub hU]
  have hle : U ⊔ E ≤ T := sup_le (hU.1.trans inf_le_left) (hE.1.trans inf_le_left)
  have hxQ : x ∈ T ⊓ CxK x K := ⟨h.x_mem_T, h.x_mem_CxK⟩
  have hxE : x ∈ E := h.x_mem_of_isS (X := T ⊓ CxK x K) inf_le_left hxQ hE
  have hP2 := pRank_eq_two_of_rankTwoShape hP
  refine ⟨hSn, hle, hel, by omega, Subgroup.mem_sup_right hxE, ?_⟩
  refine le_antisymm (C3.Layer1.Back.pRank_mono' inf_le_right) ?_
  have := C3.Layer1.Back.pRank_mono' (le_inf le_sup_left hU.1 : U ≤ (U ⊔ E) ⊓ (T ⊓ K))
  rw [pRank_of_isFourSub hU] at this
  omega

end Rows

section Pick

variable {G : Type} [Group G]

structure Th2Pick (ρ : Th2Row) (x y : G) (K T S B : Subgroup G) (t : G) (J : Subgroup G) : Prop where
  mem : B ∈ ρ.BT x K T S
  le_T : B ≤ T
  elem : CFSG.IsElementaryAbelian 2 ↥B
  rank : 4 ≤ pRank 2 ↥B
  x_mem : x ∈ B
  t_mem : t ∈ B ⊓ (T ⊓ CxK x K)
  t_two : orderOf t = 2
  pump : PumpUpLT 2 x K t J
  nonqs : ¬ CFSG.IsQuasisimple ↥J
  bar : Nonempty (kBar J ≃* kBar K)
  rank_J : 2 ≤ pRank 2 ↥J
  normalizes : B ≤ normalizer (J : Set G)
  rank_P : pRank 2 ↥(B ⊓ (T ⊓ K)) = pRank 2 ↥(T ⊓ K)

end Pick

section Picks

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem eq_of_eight_dvd (hs : Th2Std x y K T S) (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4)
    {J : Subgroup G} (hJc : IsPCompIn 2 (centralizer ({x} : Set G)) J) (h8 : 8 ∣ Nat.card ↥J) :
    J = K := by
  by_contra hne
  have hle : J ≤ centralizerSection K (pPrimeCoreOf 2 K) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hJc hs.comp hne
  have hJC : J ≤ CxK x K := le_inf hJc.1 hle
  have h8' : 8 ∣ Nat.card ↥(CxK x K) := h8.trans (Subgroup.card_dvd_of_le hJC)
  have hsyl := hs.sylow_Q.card_eq
  rw [hQ4] at hsyl
  have hv : (Nat.card ↥(CxK x K)).factorization 2 = 2 := by
    have h4 : 2 ^ 2 = 2 ^ (Nat.card ↥(CxK x K)).factorization 2 := by simpa using hsyl
    exact (Nat.pow_right_injective le_rfl h4).symm
  have hpos : Nat.card ↥(CxK x K) ≠ 0 := Nat.card_pos.ne'
  have h3 : 3 ≤ (Nat.card ↥(CxK x K)).factorization 2 := by
    have : 2 ^ 3 ∣ Nat.card ↥(CxK x K) := by simpa using h8'
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 this
  omega

theorem Th2Std.not_isQuasisimple_K_3b (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (hexc : ¬ IsExceptionalA7Triple x y K) (h412a : B_prop412a_3b) (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4)
    (hTS : T < S) (hnt : ¬ IsTerminalPair 2 x K) : ¬ CFSG.IsQuasisimple ↥K := by
  obtain ⟨hcen, hP⟩ := h.centerless_and_shape hG hL34 h102
  obtain ⟨t, htQ, ht2, J, hJ, hJq⟩ := h.exists_nonqs_pumpup hnt
    (fun u hu hu2 => h.three_le_pRank_centralizer hcen hP hu hu2)
  obtain ⟨⟨eJK⟩, -, -, -⟩ := h.pumpup_facts hG hL34 h102 ht2 hJ
  obtain ⟨e7⟩ := h7
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hJ.2.1.2.2
  have hQel := Th2.Obs.q_elementary h hQ4 hexc
  have hconj : ∃ c : G, c * x * c⁻¹ = t := by
    by_contra hno
    have hsol := h412a G hG x y K T S h ⟨e7⟩ hQ4 hTS hQel t ht2 hno
    have hJs : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJc.1)
    have hbar : Group.IsSolvable (kBar J) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J))
    have hA7 : Group.IsSolvable (alternatingGroup (Fin 7)) :=
      Group.isSolvable_of_surjective (f := (eJK.trans e7).toMonoidHom) (eJK.trans e7).surjective
    exact C3.Layer1.Bk.alt_not_isSolvable 7 (Or.inr rfl) hA7
  obtain ⟨c, hc⟩ := hconj
  have h2520 : Nat.card (kBar J) = 2520 := by
    rw [Nat.card_congr (eJK.trans e7).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hJcard : Nat.card ↥J = Nat.card (kBar J) * Nat.card ↥(pPrimeCore 2 ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J)
  have h8 : 8 ∣ Nat.card ↥J := by
    rw [hJcard, h2520]
    exact Dvd.dvd.mul_right ⟨315, by norm_num⟩ _
  have h1 : IsPCompIn 2 (cj c⁻¹ (centralizer ({t} : Set G))) (cj c⁻¹ J) :=
    Stage1.Thm2.Recip.isPCompIn_map_conj hJc c⁻¹
  have h2 : cj c⁻¹ (centralizer ({t} : Set G)) = centralizer ({x} : Set G) := by
    rw [cj_centralizer_singleton]
    congr 2
    rw [← hc]
    group
  rw [h2] at h1
  have h8' : 8 ∣ Nat.card ↥(cj c⁻¹ J) := by
    have : Nat.card ↥(cj c⁻¹ J) = Nat.card ↥J :=
      Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
    rw [this]
    exact h8
  have hKJ : cj c⁻¹ J = K := eq_of_eight_dvd h hQ4 h1 h8'
  intro hKq
  apply hJq
  have hq' : CFSG.IsQuasisimple ↥(cj c⁻¹ J) := hKJ ▸ hKq
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ((MulAut.conj c⁻¹).subgroupMap J).symm hq'

theorem Th2Std.exists_pick_L2 (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (h : Th2Std x y K T S) (hnt : ¬ IsTerminalPair 2 x K)
    (hnotA7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {ρ : Th2Row}
    (hρ : ρ = .r1b ∨ ρ = .r2 ∨ ρ = .r4b) :
    ∃ (B : Subgroup G) (t : G) (J : Subgroup G), Th2Pick ρ x y K T S B t J ∧
      2 ≤ pRank 2 ↥(B ⊓ (T ⊓ CxK x K)) := by
  obtain ⟨hcen, hP⟩ := h.centerless_and_shape hG hL34 h102
  obtain ⟨t, htQ, ht2, J, hJ, hJq⟩ := h.exists_nonqs_pumpup hnt
    (fun u hu hu2 => h.three_le_pRank_centralizer hcen hP hu hu2)
  obtain ⟨hbar, _, hJ2, hnorm⟩ := h.pumpup_facts hG hL34 h102 ht2 hJ
  have h2 := h.two_le_pRank_of_not_A7 hnotA7
  obtain ⟨E, htE, hE, hErk⟩ := h.exists_isS_Q_mem h2 htQ ht2
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  obtain ⟨hSn, hle, hel, hrk, hxB, hrkP⟩ := h.sup_facts hcen hP hU hE hErk
  have htB : t ∈ U ⊔ E := Subgroup.mem_sup_right htE
  have hcomm := (C3.Layer1.Back.forall_of_isElementaryAbelian hel).1
  refine ⟨U ⊔ E, t, J, ⟨?_, hle, hel, hrk, hxB, ⟨htB, htQ⟩, ht2, hJ, hJq, hbar, hJ2,
    fun b hb => hnorm b (mem_centralizer_singleton_iff.2 (hcomm b hb t htB)), hrkP⟩, ?_⟩
  · rcases hρ with rfl | rfl | rfl
    · exact hSn
    · exact hSn
    · exact ⟨Th2.P812.isS_of_isE_rank hG hle hel hrk, hrk⟩
  · exact hErk.trans (C3.Layer1.Back.pRank_mono' (le_inf le_sup_right hE.1))

theorem Th2Std.exists_pick_3c (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (hexc : B_thm2_A7_exc) (h : Th2Std x y K T S) (hnt : ¬ IsTerminalPair 2 x K)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    ∃ (B : Subgroup G) (t : G) (J : Subgroup G), Th2Pick .r3c x y K T S B t J ∧
      2 ≤ pRank 2 ↥(B ⊓ (T ⊓ CxK x K)) := by
  obtain ⟨hcen, hP⟩ := h.centerless_and_shape hG hL34 h102
  obtain ⟨t, htQ, ht2, J, hJ, hJq⟩ := h.exists_nonqs_pumpup hnt
    (fun u hu hu2 => h.three_le_pRank_centralizer hcen hP hu hu2)
  obtain ⟨hbar, _, hJ2, hnorm⟩ := h.pumpup_facts hG hL34 h102 ht2 hJ
  have h2 : 2 ≤ pRank 2 ↥(CxK x K) := by
    have := h.two_le_pRank_Q hexc hG
    rwa [Th2.pRank_eq_of_isSylowOf h.sylow_Q] at this
  obtain ⟨E, htE, hE, hErk⟩ := h.exists_isS_Q_mem h2 htQ ht2
  obtain ⟨D₀, hD₀⟩ := exists_isDSub h.sylow_P h7
  have hU : IsFourSub (T ⊓ K) D₀ := ⟨hD₀.1, hD₀.2.2.1, hD₀.2.2.2.1⟩
  obtain ⟨hSn, hle, hel, hrk, hxB, hrkP⟩ := h.sup_facts hcen hP hU hE hErk
  have htB : t ∈ D₀ ⊔ E := Subgroup.mem_sup_right htE
  have hcomm := (C3.Layer1.Back.forall_of_isElementaryAbelian hel).1
  refine ⟨D₀ ⊔ E, t, J, ⟨⟨hSn, D₀, hD₀, le_sup_left⟩, hle, hel, hrk, hxB, ⟨htB, htQ⟩, ht2, hJ, hJq,
    hbar, hJ2, fun b hb => hnorm b (mem_centralizer_singleton_iff.2 (hcomm b hb t htB)),
    hrkP⟩, ?_⟩
  exact hErk.trans (C3.Layer1.Back.pRank_mono' (le_inf le_sup_right hE.1))

theorem Th2Std.exists_pick_3b (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (hexc : B_thm2_A7_exc) (h3b : B_thm2_A7_3b_T) (h412a : B_prop412a_3b)
    (h : Th2Std x y K T S) (hnt : ¬ IsTerminalPair 2 x K)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4)
    (hTS : T < S) :
    ∃ (B : Subgroup G) (t : G) (J : Subgroup G), Th2Pick .r3b x y K T S B t J := by
  obtain ⟨hcen, hP⟩ := h.centerless_and_shape hG hL34 h102
  obtain ⟨D₀, hD₀⟩ := exists_isDSub h.sylow_P h7
  have hU : IsFourSub (T ⊓ K) D₀ := ⟨hD₀.1, hD₀.2.2.1, hD₀.2.2.2.1⟩
  obtain ⟨hBel, hBrk, hBT⟩ := h3b G hG x y K T S h h7 hQ4 hTS D₀ hD₀
  have hDB : D₀ ≤ ⨆ s ∈ S, D₀.map (MulAut.conj s).toMonoidHom := fun d hd =>
    Subgroup.mem_iSup_of_mem (1 : G) (Subgroup.mem_iSup_of_mem (one_mem S)
      ⟨d, hd, by show 1 * d * 1⁻¹ = d; group⟩)
  have hKnqs := h.not_isQuasisimple_K_3b hG hL34 h102 (hexc G hG x y K T S h) h412a h7 hQ4 hTS hnt
  obtain ⟨hpumpx, hKK⟩ := pumpUp_eq_self h.K_le_C h.comp
  have hILo : IsILo 2 x K := (h.v2ss.isV2Triple.2.1 : IsTwoTerminal x K).1
  have hP0 : PumpUpLT 2 x K x K :=
    ⟨hILo, hILo, mem_centralizer_singleton_iff.2 rfl, h.x_mem_CxK.2, by rw [hpumpx]; exact hKK⟩
  obtain ⟨hbar, _, hJ2, -⟩ := h.pumpup_facts hG hL34 h102 h.orderOf_x hP0
  have hxB : x ∈ ⨆ s ∈ S, D₀.map (MulAut.conj s).toMonoidHom :=
    h.x_mem_of_isS (X := T) le_rfl h.x_mem_T (Th2.P812.isS_of_isE_rank hG hBT hBel hBrk)
  have hKN := h.K_normal_A7 hG h7
  have hP2 := pRank_eq_two_of_rankTwoShape hP
  refine ⟨⨆ s ∈ S, D₀.map (MulAut.conj s).toMonoidHom, x, K, ⟨⟨D₀, hD₀, rfl⟩, hBT, hBel, hBrk,
    hxB, ⟨hxB, h.x_mem_T, h.x_mem_CxK⟩, h.orderOf_x, hP0, hKnqs, hbar, hJ2,
    fun b hb => mem_normalizer_K_of_KN hKN (h.T_le_C (hBT hb)), ?_⟩⟩
  refine le_antisymm (C3.Layer1.Back.pRank_mono' inf_le_right) ?_
  have := C3.Layer1.Back.pRank_mono' (le_inf hDB hD₀.1 :
    D₀ ≤ (⨆ s ∈ S, D₀.map (MulAut.conj s).toMonoidHom) ⊓ (T ⊓ K))
  rw [pRank_of_isFourSub hU] at this
  omega

end Picks

section Leaves

@[expose] def B_thm2_p72c_U2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ¬ IsTerminalPair 2 x K → ∀ ρ : Th2Row,
      (ρ = .r1b ∨ ρ = .r3b ∨ ρ = .r3c) → ρ.holds x y K T S →
        (∀ B ∈ ρ.BT x K T S, ρ.level.IsBal B) →
          ∀ (B : Subgroup G) (t : G) (J : Subgroup G), Th2Pick ρ x y K T S B t J →
            ρ.level.theta B ≠ ⊥

@[expose] def B_thm2_p72c_row2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ¬ IsTerminalPair 2 x K → Th2Row.r2.holds x y K T S →
      (∀ B ∈ Th2Row.r2.BT x K T S, Th2Row.r2.level.IsBal B) →
        ∀ (B : Subgroup G) (t : G) (J : Subgroup G), Th2Pick .r2 x y K T S B t J →
          2 ≤ pRank 2 ↥(B ⊓ (T ⊓ CxK x K)) → Th2Row.r2.level.theta B ≠ ⊥

@[expose] def B_thm2_p72c_row4b : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ¬ IsTerminalPair 2 x K → Th2Row.r4b.holds x y K T S →
      (∀ B ∈ Th2Row.r4b.BT x K T S, Th2Row.r4b.level.IsBal B) →
        ∀ (B : Subgroup G) (t : G) (J : Subgroup G), Th2Pick .r4b x y K T S B t J →
          2 ≤ pRank 2 ↥(B ⊓ (T ⊓ CxK x K)) → Th2Row.r4b.level.theta B ≠ ⊥

theorem b_thm2_p72c_rows_of (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hexc : B_thm2_A7_exc)
    (h3b : B_thm2_A7_3b_T) (h412a : B_prop412a_3b)
    (hU2 : B_thm2_p72c_U2) (h2 : B_thm2_p72c_row2) (h4b : B_thm2_p72c_row4b) :
    B_thm2_p72c_rows := by
  intro G _ _ hG x y K T S h hnt ρ hρ hρh hbal
  rcases hρ with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨B, t, J, hpick, -⟩ := h.exists_pick_L2 hG hL34 h102 hnt
      (not_nonempty_A7_of_hasL2Model hρh.1) (Or.inl rfl)
    exact ⟨B, hpick.mem, hU2 G hG x y K T S h hnt .r1b (Or.inl rfl) hρh hbal B t J hpick,
      hpick.rank_P⟩
  · obtain ⟨B, t, J, hpick, hBQ⟩ := h.exists_pick_L2 hG hL34 h102 hnt
      (not_nonempty_A7_of_hasL2Model (Pr := fun q => Odd q ∧ IsFM9 q ∧ q ≠ 5) hρh)
      (Or.inr (Or.inl rfl))
    exact ⟨B, hpick.mem, h2 G hG x y K T S h hnt hρh hbal B t J hpick hBQ, hpick.rank_P⟩
  · obtain ⟨h7, hQ4, hTS⟩ := hρh
    obtain ⟨B, t, J, hpick⟩ := h.exists_pick_3b hG hL34 h102 hexc h3b h412a hnt h7 hQ4 hTS
    exact ⟨B, hpick.mem, hU2 G hG x y K T S h hnt .r3b (Or.inr (Or.inl rfl)) ⟨h7, hQ4, hTS⟩ hbal
      B t J hpick, hpick.rank_P⟩
  · obtain ⟨B, t, J, hpick, -⟩ := h.exists_pick_3c hG hL34 h102 hexc hnt hρh.1
    exact ⟨B, hpick.mem, hU2 G hG x y K T S h hnt .r3c (Or.inr (Or.inr rfl)) hρh hbal B t J hpick,
      hpick.rank_P⟩
  · obtain ⟨B, t, J, hpick, hBQ⟩ := h.exists_pick_L2 hG hL34 h102 hnt
      (not_nonempty_A7_of_hasL2Model hρh.1) (Or.inr (Or.inr rfl))
    exact ⟨B, hpick.mem, h4b G hG x y K T S h hnt hρh hbal B t J hpick hBQ, hpick.rank_P⟩

end Leaves

end CFSG.GH74.GLS

