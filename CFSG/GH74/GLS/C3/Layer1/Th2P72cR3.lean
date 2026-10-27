module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR2

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

section Rank

variable {G : Type} [Group G] [Finite G]

theorem pRank_add_le_of_ne_comp {b : G} (hb2 : orderOf b = 2) {J₁ J₂ : Subgroup G}
    (hJ₁ : IsPCompIn 2 (centralizer ({b} : Set G)) J₁)
    (hJ₂ : IsPCompIn 2 (centralizer ({b} : Set G)) J₂)
    (hJ₁cen : CenterlessBar J₁) (hJ₂cen : CenterlessBar J₂) (hne : J₂ ≠ J₁) :
    1 + pRank 2 ↥J₁ + pRank 2 ↥J₂ ≤ pRank 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : J₂ ≤ centralizerSection J₁ (pPrimeCoreOf 2 J₁) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hJ₂ hJ₁ hne
  obtain ⟨E₂, hE₂J, hE₂el, hE₂rk⟩ := exists_elemAbelian_pRank J₂
  have hEβle : E₂ ≤ centralizerSection J₁ (pPrimeCoreOf 2 J₁) := hE₂J.trans hle
  have hbJc : ∀ k ∈ J₁, b * k = k * b := fun k hk => (mem_centralizer_singleton_iff.1 (hJ₁.1 hk)).symm
  have hbEc : ∀ e ∈ E₂, b * e = e * b := fun e he =>
    (mem_centralizer_singleton_iff.1 (hJ₂.1 (hE₂J he))).symm
  have hbE₂ : b ∉ E₂ := by
    intro hbE
    have hbJ : b ∈ J₂ := hE₂J hbE
    have hbJc2 : ∀ k ∈ J₂, b * k = k * b := fun k hk =>
      (mem_centralizer_singleton_iff.1 (hJ₂.1 hk)).symm
    have hbO : b ∈ pPrimeCoreOf 2 J₂ := by
      refine mem_pPrimeCoreOf_of_commutators hJ₂cen hbJ (fun k hk => ?_)
      have : ⁅k, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hbJc2 k hk).symm
      rw [this]
      exact one_mem _
    have hodd : Odd (orderOf b) :=
      Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd J₂) (Subgroup.orderOf_dvd_natCard _ hbO)
    rw [hb2] at hodd
    exact absurd hodd (by decide)
  have hcd : CommDisj (zpowers b) E₂ := by
    refine ⟨fun p hp q hq => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hp
      exact (Commute.zpow_left (show Commute b q from hbEc q hq) m).eq
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two hb2 hz.1 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hz.2) hbE₂
  have hbel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hb2
  have hW₀el : CFSG.IsElementaryAbelian 2 ↥(zpowers b ⊔ E₂) :=
    hcd.isElementaryAbelian_sup' hbel hE₂el le_rfl le_rfl
  have hW₀rk : pRank 2 ↥(zpowers b ⊔ E₂) = 1 + pRank 2 ↥J₂ := by
    rw [hcd.pRank_sup hbel hE₂el le_rfl le_rfl, Th2.pRank_zpowers_of_orderOf_two hb2, hE₂rk]
  have hbcs : b ∈ centralizerSection J₁ (pPrimeCoreOf 2 J₁) :=
    C3.Layer1.Back.mem_centralizerSection_of_centralizes hbJc (TwoThin.pPrimeCoreOf_le J₁)
  have hW₀cs : zpowers b ⊔ E₂ ≤ centralizerSection J₁ (pPrimeCoreOf 2 J₁) :=
    sup_le (zpowers_le.2 hbcs) hEβle
  have hW₀2 : IsPGroup 2 ↥(zpowers b ⊔ E₂) := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨S₀, hS₀J, hS₀p, hS₀card, hS₀norm⟩ :=
    IVK.Proofs2.exists_normalized_sylow_two J₁ (zpowers b ⊔ E₂) hW₀2 (fun w hw => (hW₀cs hw).1)
  have hSyl : IsSylowOf 2 S₀ J₁ := isSylowOf_of_card hS₀J hS₀card.symm
  have hS₀W : ∀ e ∈ S₀, ∀ w ∈ zpowers b ⊔ E₂, e * w = w * e := by
    intro e he w hw
    have h1 : ⁅e, w⁆ ∈ pPrimeCoreOf 2 J₁ := (hW₀cs hw).2.2 e (hS₀J he)
    have h2 : ⁅e, w⁆ ∈ S₀ := by
      have := hS₀norm w hw e⁻¹ (S₀.inv_mem he)
      rw [commutatorElement_def]
      have e1 : e * w * e⁻¹ * w⁻¹ = e * (w * e⁻¹ * w⁻¹) := by group
      rw [e1]
      exact S₀.mul_mem he this
    have h3 : ⁅e, w⁆ ∈ S₀ ⊓ pPrimeCoreOf 2 J₁ := ⟨h2, h1⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot J₁ hS₀p, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  obtain ⟨E', hE'S, hE'el, hE'rk⟩ := exists_elemAbelian_pRank S₀
  have hE'rk' : pRank 2 ↥E' = pRank 2 ↥J₁ := by rw [hE'rk, Th2.pRank_eq_of_isSylowOf hSyl]
  have hcd2 : CommDisj E' (zpowers b ⊔ E₂) := by
    refine ⟨fun p hp q hq => hS₀W p (hE'S hp) q hq, ?_⟩
    refine eq_bot_iff.2 fun u hu => ?_
    obtain ⟨huE, huW⟩ := hu
    have huS : u ∈ S₀ := hE'S huE
    have huJ : u ∈ J₁ := hS₀J huS
    have huO : u ∈ pPrimeCoreOf 2 J₁ :=
      mem_pPrimeCoreOf_of_commutators hJ₁cen huJ (fun k hk => (hW₀cs huW).2.2 k hk)
    have h3 : u ∈ S₀ ⊓ pPrimeCoreOf 2 J₁ := ⟨huS, huO⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot J₁ hS₀p] at h3
    exact h3
  have hrk := hcd2.pRank_sup hE'el hW₀el le_rfl le_rfl
  have h4 := pRank_le_top' (E' ⊔ (zpowers b ⊔ E₂))
  omega

theorem eq_of_isPCompIn_of_pRank_le_four (hG4 : pRank 2 G ≤ 4) {b : G} (hb2 : orderOf b = 2)
    {J₁ J₂ : Subgroup G} (hJ₁ : IsPCompIn 2 (centralizer ({b} : Set G)) J₁)
    (hJ₂ : IsPCompIn 2 (centralizer ({b} : Set G)) J₂) (hJ₁cen : CenterlessBar J₁)
    (hJ₂cen : CenterlessBar J₂) (h₁ : 2 ≤ pRank 2 ↥J₁) (h₂ : 2 ≤ pRank 2 ↥J₂) : J₂ = J₁ := by
  by_contra hne
  have := pRank_add_le_of_ne_comp hb2 hJ₁ hJ₂ hJ₁cen hJ₂cen hne
  omega

end Rank

section EndGame

variable {G : Type} [Group G]

theorem mem_of_inverted_of_commutator_mem {Γ : Type*} [Group Γ] (I : Subgroup Γ) {x b : Γ}
    (hodd : Odd (orderOf x)) (hinv : b * x * b⁻¹ = x⁻¹) (hcomm : ⁅b, x⁆ ∈ I) : x ∈ I := by
  have h1 : ⁅b, x⁆ = x⁻¹ * x⁻¹ := by
    rw [commutatorElement_def, hinv]
  have h2 : x ^ 2 ∈ I := by
    have : x ^ 2 = (⁅b, x⁆)⁻¹ := by rw [h1]; group
    rw [this]
    exact I.inv_mem hcomm
  obtain ⟨m, hm⟩ := hodd
  have h3 : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h3]
  exact I.pow_mem h2 _

theorem exists_mem_J_mul_cSec_of_inner [Finite G] {J : Subgroup G} {x : G}
    (hx : x ∈ normalizer (J : Set G))
    (hmem : barAct J ⟨x, hx⟩ ∈ (MulAut.conj : kBar J →* MulAut (kBar J)).range) :
    ∃ j ∈ J, x * j⁻¹ ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  obtain ⟨jbar, hja⟩ := MonoidHom.mem_range.1 hmem
  obtain ⟨⟨j, hjJ⟩, rfl⟩ := QuotientGroup.mk_surjective jbar
  refine ⟨j, hjJ, ?_⟩
  have hjN : j ∈ normalizer (J : Set G) := Subgroup.le_normalizer hjJ
  have hxj : x * j⁻¹ ∈ normalizer (J : Set G) := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hjN)
  have hact : barAct J ⟨j, hjN⟩ = barAct J ⟨x, hx⟩ := by rw [barAct_of_mem hjJ]; exact hja
  have h1 : (⟨x * j⁻¹, hxj⟩ : ↥(normalizer (J : Set G))) =
      ⟨x, hx⟩ * (⟨j, hjN⟩ : ↥(normalizer (J : Set G)))⁻¹ := rfl
  exact (barAct_eq_one_iff ⟨x * j⁻¹, hxj⟩).1 (by rw [h1, map_mul, map_inv, hact, mul_inv_cancel])

theorem exists_mem_J_mul_cSec_of_inverted [Finite G] {J : Subgroup G}
    (hOut : ∀ g h : ↥(normalizer (J : Set G)),
      ⁅barAct J g, barAct J h⁆ ∈ (MulAut.conj : kBar J →* MulAut (kBar J)).range)
    {x b : G} (hx : x ∈ normalizer (J : Set G)) (hb : b ∈ normalizer (J : Set G))
    (hodd : Odd (orderOf x)) (hinv : b * x * b⁻¹ = x⁻¹) :
    ∃ j ∈ J, x * j⁻¹ ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  set X : ↥(normalizer (J : Set G)) := ⟨x, hx⟩ with hX
  set Bb : ↥(normalizer (J : Set G)) := ⟨b, hb⟩ with hBb
  have hinv' : barAct J Bb * barAct J X * (barAct J Bb)⁻¹ = (barAct J X)⁻¹ := by
    have h1 : Bb * X * Bb⁻¹ = X⁻¹ := Subtype.ext hinv
    have h2 := congrArg (barAct J) h1
    simpa [map_mul, map_inv] using h2
  have hodd' : Odd (orderOf (barAct J X)) := by
    have h1 : orderOf (barAct J X) ∣ orderOf X := orderOf_map_dvd (barAct J) X
    have h2 : orderOf X = orderOf x := (Subgroup.orderOf_coe X).symm
    exact Odd.of_dvd_nat (h2 ▸ hodd) h1
  exact exists_mem_J_mul_cSec_of_inner hx
    (mem_of_inverted_of_commutator_mem _ hodd' hinv' (hOut Bb X))

theorem exists_mem_J_mul_cSec_of_odd_A7 [Finite G] {J : Subgroup G}
    (e : kBar J ≃* alternatingGroup (Fin 7)) {x : G} (hx : x ∈ normalizer (J : Set G))
    (hodd : Odd (orderOf x)) :
    ∃ j ∈ J, x * j⁻¹ ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  have h1 : orderOf (barAct J ⟨x, hx⟩) ∣ orderOf (⟨x, hx⟩ : ↥(normalizer (J : Set G))) :=
    orderOf_map_dvd (barAct J) _
  have h2 : orderOf (⟨x, hx⟩ : ↥(normalizer (J : Set G))) = orderOf x :=
    (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥(normalizer (J : Set G)))).symm
  exact exists_mem_J_mul_cSec_of_inner hx
    (Th2.Bal.a7_odd_orderOf_mem_innAut e (Odd.of_dvd_nat (h2 ▸ hodd) h1))

end EndGame

end CFSG.GH74.GLS.Th2.Obs

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem Th2Std.pRank_Q_le_two (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (h : Th2Std x y K T S) : pRank 2 ↥(T ⊓ CxK x K) ≤ 2 := by
  by_contra hlt
  obtain ⟨hcen, hP⟩ := h.centerless_and_shape hG hL34 h102
  exact false_of_three_le_rank_Q hG h hcen hP (by omega)

theorem Th2Std.pRank_le_two_of_le_Q (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (h : Th2Std x y K T S) {E : Subgroup G} (hE : E ≤ T ⊓ CxK x K) : pRank 2 ↥E ≤ 2 :=
  (C3.Layer1.Back.pRank_mono' hE).trans (h.pRank_Q_le_two hG hL34 h102)

theorem Th2Std.bar_facts (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (h : Th2Std x y K T S) {J : Subgroup G} (hbar : Nonempty (kBar J ≃* kBar K)) :
    CenterlessBar J ∧ 2 ≤ pRank 2 ↥J := by
  obtain ⟨eJK⟩ := hbar
  obtain ⟨hcen, hP⟩ := h.centerless_and_shape hG hL34 h102
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
  exact ⟨hJcen, by omega⟩

theorem Th2Std.eq_pumpup_of_isPCompIn (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (h : Th2Std x y K T S) {e : G} (he2 : orderOf e = 2) {Je : Subgroup G} (hJe : PumpUpLT 2 x K e Je)
    {J' : Subgroup G} (hJ' : IsPCompIn 2 (centralizer ({e} : Set G)) J')
    (hbar : Nonempty (kBar J' ≃* kBar K)) : J' = Je := by
  obtain ⟨hbarJe, hJecen, hJe2, -⟩ := h.pumpup_facts hG hL34 h102 he2 hJe
  obtain ⟨hJ'cen, hJ'2⟩ := h.bar_facts hG hL34 h102 hbar
  exact eq_of_isPCompIn_of_pRank_le_four hG.pRank_eq_four.le he2 hJe.2.1.2.2 hJ' hJecen hJ'cen hJe2 hJ'2

end Std

section Bookkeeping

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem seven_B_of_thetaHalf_eq_bot {B : Subgroup G} (hbal : IsKBal 3 B) (hθ : thetaHalf 2 B = ⊥) :
    (∀ W : Subgroup G, IsE 3 B W → AG W = ⊥) ∧ (∀ W : Subgroup G, IsE 2 B W → ⁅AG W, B⁆ = ⊥) := by
  have hcomm : ∀ W : Subgroup G, IsE 2 B W → ⁅AG W, B⁆ = ⊥ := fun W hW => by
    refine le_bot_iff.1 ?_
    rw [← hθ]
    exact le_sup_of_le_left (le_iSup₂_of_le W hW le_rfl)
  refine ⟨fun W hW => ?_, hcomm⟩
  have hW2 : IsE 2 B W := isE_mono_rank hW (by norm_num)
  have hc := hcomm W hW2
  refine le_bot_iff.1 ?_
  rw [← hθ]
  refine le_trans ?_ le_sup_right
  refine le_iInf₂ fun b hb => fun w hw => ?_
  have hwc : w ∈ centralizer ({b} : Set G) := by
    have h1 : ⁅w, b⁆ ∈ ⁅AG W, B⁆ := Subgroup.commutator_mem_commutator hw hb.1
    rw [hc, Subgroup.mem_bot] at h1
    exact mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h1)
  exact hbal W hW b hb.1 hb.2 ⟨hw, hwc⟩

omit [Finite G] in
theorem isElementaryAbelian_le {A B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) (hAB : A ≤ B) :
    CFSG.IsElementaryAbelian 2 ↥A := by
  obtain ⟨hc, hs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  exact C3.Layer1.Back.isElementaryAbelian_of_forall (fun u hu v hv => hc u (hAB hu) v (hAB hv))
    (fun u hu => hs u (hAB hu))

theorem lemma_7_10 {B W V Z : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hB4 : 4 ≤ pRank 2 ↥B) (hWV : W ≤ V) (hVB : V ≤ B) (hV : Nat.card ↥B = 2 * Nat.card ↥V)
    (hW : Nat.card ↥B = 4 * Nat.card ↥W) (hZ : Z ≠ ⊥)
    (h7B1 : ∀ W' : Subgroup G, IsE 3 B W' → AG W' = ⊥)
    (h7B2 : ∀ W' : Subgroup G, IsE 2 B W' → ⁅AG W', B⁆ = ⊥) :
    (∃ w ∈ W, w ≠ 1 ∧ ¬ Z ≤ pPrimeCoreOf 2 (centralizer ({w} : Set G))) ∨
      ((∀ z ∈ Z, ∀ b ∈ B, z * b = b * z) ∧
        ∃ v ∈ V, v ≠ 1 ∧ ¬ Z ≤ pPrimeCoreOf 2 (centralizer ({v} : Set G))) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hcon1, hcon2⟩ := hcon
  have hWel := isElementaryAbelian_le hBel (hWV.trans hVB)
  have hVel := isElementaryAbelian_le hBel hVB
  have hBc := C3.Layer1.Back.card_eq_two_pow_pRank hBel
  have hWc := C3.Layer1.Back.card_eq_two_pow_pRank hWel
  have hVc := C3.Layer1.Back.card_eq_two_pow_pRank hVel
  have h16 : 2 ^ 4 ≤ 2 ^ pRank 2 ↥B := Nat.pow_le_pow_right (by norm_num) hB4
  have hWrk : 2 ≤ pRank 2 ↥W := by
    by_contra hlt
    have : 2 ^ pRank 2 ↥W ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hVrk : 3 ≤ pRank 2 ↥V := by
    by_contra hlt
    have : 2 ^ pRank 2 ↥V ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hZW : Z ≤ AG W := le_iInf₂ fun b hb => hcon1 b hb.1 hb.2
  have hZB : ∀ z ∈ Z, ∀ b ∈ B, z * b = b * z := by
    intro z hz b hb
    have h1 : ⁅z, b⁆ ∈ ⁅AG W, B⁆ := Subgroup.commutator_mem_commutator (hZW hz) hb
    rw [h7B2 W ⟨hWV.trans hVB, hWel, hWrk⟩, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hZV : Z ≤ AG V := le_iInf₂ fun v hv => hcon2 hZB v hv.1 hv.2
  apply hZ
  exact le_bot_iff.1 ((h7B1 V ⟨hVB, hVel, hVrk⟩) ▸ hZV)

theorem exists_defect_centralizing_actors {B W V X₀ X₁ Z : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : 4 ≤ pRank 2 ↥B)
    (hWV : W ≤ V) (hVB : V ≤ B) (hV : Nat.card ↥B = 2 * Nat.card ↥V)
    (hW : Nat.card ↥B = 4 * Nat.card ↥W) (hZ : Z ≠ ⊥)
    (h7B1 : ∀ W' : Subgroup G, IsE 3 B W' → AG W' = ⊥)
    (h7B2 : ∀ W' : Subgroup G, IsE 2 B W' → ⁅AG W', B⁆ = ⊥)
    (hWX₀ : ∀ w ∈ W, ∀ z ∈ X₀, w * z = z * w)
    (hVX₁ : ∀ v ∈ V, ∀ z ∈ X₁, v * z = z * v)
    (hsep : (∀ v ∈ V, ∀ z ∈ X₀, v * z = z * v) ∨
      (∀ v ∈ V, v ∉ W → ∃ z ∈ Z, v * z ≠ z * v)) :
    ∃ u ∈ V, u ≠ 1 ∧ (∀ z ∈ X₀, u * z = z * u) ∧ (∀ z ∈ X₁, u * z = z * u) ∧
      ¬ Z ≤ pPrimeCoreOf 2 (centralizer ({u} : Set G)) := by
  rcases lemma_7_10 hBel hB4 hWV hVB hV hW hZ h7B1 h7B2 with
    ⟨w, hwW, hw1, hw⟩ | ⟨hBZ, v, hvV, hv1, hv⟩
  · exact ⟨w, hWV hwW, hw1, hWX₀ w hwW, hVX₁ w (hWV hwW), hw⟩
  · rcases hsep with hsep | hsep
    · exact ⟨v, hvV, hv1, hsep v hvV, hVX₁ v hvV, hv⟩
    · by_cases hvW : v ∈ W
      · exact ⟨v, hvV, hv1, hWX₀ v hvW, hVX₁ v hvV, hv⟩
      · obtain ⟨z, hz, hzv⟩ := hsep v hvV hvW
        exact absurd (hBZ z hz v (hVB hvV)).symm hzv

theorem exists_defect_centralizing_actors_of_thetaHalf {B W V X₀ X₁ Z : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : 4 ≤ pRank 2 ↥B)
    (hbal : IsKBal 3 B) (hθ : thetaHalf 2 B = ⊥)
    (hWV : W ≤ V) (hVB : V ≤ B) (hV : Nat.card ↥B = 2 * Nat.card ↥V)
    (hW : Nat.card ↥B = 4 * Nat.card ↥W) (hZ : Z ≠ ⊥)
    (hWX₀ : ∀ w ∈ W, ∀ z ∈ X₀, w * z = z * w)
    (hVX₁ : ∀ v ∈ V, ∀ z ∈ X₁, v * z = z * v)
    (hsep : (∀ v ∈ V, ∀ z ∈ X₀, v * z = z * v) ∨
      (∀ v ∈ V, v ∉ W → ∃ z ∈ Z, v * z ≠ z * v)) :
    ∃ u ∈ V, u ≠ 1 ∧ (∀ z ∈ X₀, u * z = z * u) ∧ (∀ z ∈ X₁, u * z = z * u) ∧
      ¬ Z ≤ pPrimeCoreOf 2 (centralizer ({u} : Set G)) := by
  obtain ⟨h7B1, h7B2⟩ := seven_B_of_thetaHalf_eq_bot hbal hθ
  exact exists_defect_centralizing_actors hBel hB4 hWV hVB hV hW hZ h7B1 h7B2 hWX₀ hVX₁ hsep

end Bookkeeping

end CFSG.GH74.GLS
