module

public import CFSG.GH74.GLS.C3.Layer1.Th2L74Main
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseISyl
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

theorem card_A7_eq_2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem lt_div_aux {X d k N : ℕ} (hd0 : 0 < d) (hdk : d ≤ k) (hX : k * (N + 1) ≤ X) :
    N < X / d := by
  have h1 : N + 1 ≤ X / k := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hX)
  have h2 : X / k ≤ X / d := Nat.div_le_div_left hdk hd0
  omega

theorem ordA_one_ne_2520_aux (m : ℕ) : CFSG.Open.ordA 1 m ≠ 2520 := by
  unfold CFSG.Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  rcases Nat.lt_or_ge m 18 with hm | hm
  · interval_cases m <;> decide
  · have hg : 0 < Nat.gcd 2 (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 2 (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hX : 2 * (2520 + 1) ≤ m * (m ^ 2 - 1) := by
      have h1 : 18 * 323 ≤ m * (m ^ 2 - 1) := by
        have h2 : 323 ≤ m ^ 2 - 1 := by
          have : 18 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
          omega
        exact Nat.mul_le_mul hm h2
      omega
    exact (lt_div_aux hg hle hX).ne'

variable {G : Type} [Group G]

theorem not_nonempty_A7_of_hasL2Model {K : Subgroup G} {Pr : ℕ → Prop}
    (h : HasL2Model (kBar K) Pr) : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨p, f, -, -, -, hmodel⟩ := h
  have h1 := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hmodel
  have h2 : Nat.card (kBar K) = 2520 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_A7_eq_2520
  rw [h2] at h1
  exact ordA_one_ne_2520_aux (p ^ f) (by simpa using h1.symm)

theorem isE_of_isSn {X B T : Subgroup G} {n m : ℕ} (hX : X ≤ T) (hB : IsSn n X B) (hnm : m ≤ n) :
    IsE m T B :=
  ⟨hB.1.1.trans hX, hB.1.2.1, hnm.trans hB.2⟩

theorem isKBal_one_of_balanced [Finite G] {A : Subgroup G} (hA : IsBalancedWrt A) : IsKBal 1 A := by
  intro D hD a ha ha1
  obtain ⟨hDA, hDel, hDrk⟩ := hD
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ d ∈ D, d = 1 := fun d hd => by
      by_contra h1
      exact hcon ⟨d, hd, h1⟩
    have hbot : D = ⊥ := eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (hcon' g hg)
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hDel
    rw [hbot] at h1 hDrk
    rw [Subgroup.card_bot] at h1
    have h2 : (2 : ℕ) ^ pRank 2 ↥(⊥ : Subgroup G) = 2 ^ 0 := by rw [← h1]; simp
    have h3 := Nat.pow_right_injective le_rfl h2
    omega
  intro c hc
  have h1 : AG D ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) := iInf₂_le d ⟨hdD, hd1⟩
  have hbal := hA d (hDA hdD) hd1 a ha ha1
  have hmem : c ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({a} : Set G) :=
    ⟨h1 hc.1, hc.2⟩
  rw [hbal] at hmem
  exact hmem.2

end CFSG.GH74.GLS.Th2

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_thm2_bal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ∀ ρ : Th2Row,
      (ρ = .r1b ∨ ρ = .r2 ∨ ρ = .r3b ∨ ρ = .r3c ∨ ρ = .r4b) → ρ.holds x y K T S →
        ∀ B ∈ ρ.BT x K T S, ρ.level.IsBal B

@[expose] def B_thm2_A7_3b_T : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      Nat.card ↥(T ⊓ CxK x K) = 4 → T < S → ∀ D : Subgroup G, IsDSub K (T ⊓ K) D →
        CFSG.IsElementaryAbelian 2 ↥(⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom) ∧
          4 ≤ pRank 2 ↥(⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom) ∧
          (⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom) ≤ T

theorem b_thm2_A7_3b_of_T (h : B_thm2_A7_3b_T) : B_thm2_A7_3b := by
  intro G _ _ hG x y K T S hs h7 hQ hTS D hD
  obtain ⟨h1, h2, -⟩ := h G hG x y K T S hs h7 hQ hTS D hD
  exact ⟨h1, h2⟩

section P73

variable {G : Type} [Group G] {x y : G} {K T S : Subgroup G}

theorem Th2Std.two_le_pRank_of_not_A7 (h : Th2Std x y K T S)
    (hnot : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) : 2 ≤ pRank 2 ↥(CxK x K) := by
  rcases h.v2ss.isV2Triple.2.2.1 with h1 | h1
  · exact h1
  · exact absurd h1.2.1 hnot

theorem Th2Std.exists_isS_Q' [Finite G] (h : Th2Std x y K T S) (h2 : 2 ≤ pRank 2 ↥(CxK x K)) :
    ∃ E : Subgroup G, IsS (T ⊓ CxK x K) E ∧ 2 ≤ pRank 2 ↥E := by
  obtain ⟨F, hFC, hFel, hFrk⟩ := exists_elemAbelian_pRank (CxK x K)
  obtain ⟨g, -, hgF⟩ := Th2.exists_cj_le_of_isSylowOf h.sylow_Q hFC
    (CFSG.IsElementaryAbelian.isPGroup 2 _)
  have hWel := isElementaryAbelian_cj g hFel
  obtain ⟨E, hWE, hE⟩ := exists_maximal_elemAbelian hgF hWel
  refine ⟨E, hE, ?_⟩
  have := C3.Layer1.Back.pRank_mono' hWE
  rw [pRank_cj, hFrk] at this
  omega

theorem Th2Std.exists_isSn_R [Finite G] (h : Th2Std x y K T S) (hcen : CenterlessBar K)
    (hP : RankTwoShape (T ⊓ K)) (h2 : 2 ≤ pRank 2 ↥(CxK x K)) :
    ∃ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B := by
  have hPQ := h.commDisj hcen
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  obtain ⟨E, hE, hErk⟩ := h.exists_isS_Q' h2
  exact ⟨U ⊔ E, (isS_sup_iff hPQ hP _).2 ⟨U, hU, E, hE, hErk, rfl⟩ |>.1,
    ((isS_sup_iff hPQ hP _).2 ⟨U, hU, E, hE, hErk, rfl⟩).2⟩

theorem Th2Std.exists_isSn_T [Finite G] (h : Th2Std x y K T S) (hcen : CenterlessBar K)
    (hP : RankTwoShape (T ⊓ K)) (hQ2 : 2 ≤ pRank 2 ↥(T ⊓ CxK x K)) :
    ∃ B : Subgroup G, IsSn 4 T B := by
  have hPQ := h.commDisj hcen
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  obtain ⟨E, hEQ, hEel, hErk⟩ := exists_elemAbelian_pRank (T ⊓ CxK x K)
  have hWel := hPQ.isElementaryAbelian_sup' hU.2.1 hEel hU.1 hEQ
  have hWrk : pRank 2 ↥(U ⊔ E) = 2 + pRank 2 ↥E := by
    rw [hPQ.pRank_sup hU.2.1 hEel hU.1 hEQ, pRank_of_isFourSub hU]
  have hWT : U ⊔ E ≤ T := sup_le (hU.1.trans inf_le_left) (hEQ.trans inf_le_left)
  obtain ⟨B₀, hWB, hB₀⟩ := exists_maximal_elemAbelian hWT hWel
  refine ⟨B₀, hB₀, ?_⟩
  have := C3.Layer1.Back.pRank_mono' hWB
  omega

theorem Th2Std.exceptional_A7_data [Finite G] (h : Th2Std x y K T S)
    (hex : IsExceptionalA7Triple x y K) : Nat.card ↥(T ⊓ CxK x K) = 4 ∧ T < S := by
  obtain ⟨-, -, T', S', a, hT', -, hQ', hS', hlt', -, -, -, -, -, -, -, -, -, ⟨eQ'⟩⟩ := hex
  have hQcard : Nat.card ↥(T ⊓ CxK x K) = Nat.card ↥(T' ⊓ CxK x K) :=
    h.sylow_Q.card_eq.trans hQ'.card_eq.symm
  refine ⟨?_, ?_⟩
  · rw [hQcard, Nat.card_congr eQ'.toEquiv]
    simp
  · have hT : Nat.card ↥T = Nat.card ↥T' := h.setup.sylowT.card_eq.trans hT'.card_eq.symm
    have hS : Nat.card ↥S = Nat.card ↥S' := h.sylowS.card_eq.trans hS'.card_eq.symm
    refine lt_of_le_of_ne h.T_le_S fun heq => ?_
    have h1 : Nat.card ↥T' ≤ Nat.card ↥S' := Subgroup.card_le_of_le hlt'.le
    have h2 : Nat.card ↥S ≤ Nat.card ↥T' := by rw [← hT, heq]
    have h3 : T' = S' := Subgroup.eq_of_le_of_card_ge hlt'.le (by omega)
    exact hlt'.ne h3

end P73

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

theorem b_thm2_p73_of (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (h3b : B_thm2_A7_3b_T)
    (hbal : B_thm2_bal) : B_thm2_p73 := by
  intro G _ _ hG x y K T S h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcen, hPsh⟩ := h.centerless_and_shape hG hL34 h102
  have hv : IsV2Triple x y K := h.v2ss.isV2Triple
  obtain ⟨-, hshape⟩ := h102 G hG x y K hv.1
  have hQ3 : ¬ 3 ≤ pRank 2 ↥(T ⊓ CxK x K) := fun h3 => false_of_three_le_rank_Q hG h hcen hPsh h3
  have hRT : (T ⊓ K) ⊔ (T ⊓ CxK x K) ≤ T := sup_le inf_le_left inf_le_left
  rcases hshape with hL2 | h7 | ⟨hL34', hel, hcard⟩
  · obtain ⟨p, f, hp, hf, hqodd, hmodel⟩ := hL2
    have hnotA7 := not_nonempty_A7_of_hasL2Model (K := K) (Pr := Odd) ⟨p, f, hp, hf, hqodd, hmodel⟩
    have h2 := h.two_le_pRank_of_not_A7 hnotA7
    have hQ2 : 2 ≤ pRank 2 ↥(T ⊓ CxK x K) := by
      rw [pRank_eq_of_isSylowOf h.sylow_Q]
      exact h2
    have hSnR := h.exists_isSn_R hcen hPsh h2
    by_cases h5 : p ^ f = 5
    · have hq5 : HasL2Model (kBar K) (fun q => q = 5) := ⟨p, f, hp, hf, h5, hmodel⟩
      have hQeq2 : pRank 2 ↥(CxK x K) = 2 := by
        have := pRank_eq_of_isSylowOf h.sylow_Q
        omega
      have hSnT := h.exists_isSn_T hcen hPsh hQ2
      by_cases hb : ∃ B : Subgroup G, IsE 4 ⊤ B ∧ ¬ IsBalancedWrt B
      · obtain ⟨hunb, hrk4⟩ := h.v2ss.2 hq5 hQeq2 hb
        have hrow : Th2Row.r4b.holds x y K T S := by
          simp only [Th2Row.holds]
          exact ⟨hq5, hG.pRank_eq_four, hrk4, hunb⟩
        exact ⟨.r4b, hrow, hSnT, fun B hB =>
          ⟨isE_of_isSn le_rfl hB le_rfl, hbal G hG x y K T S h .r4b
            (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hrow B hB⟩⟩
      · have hb' : ∀ E : Subgroup G, IsE 4 ⊤ E → IsBalancedWrt E := fun E hE => by
          by_contra hE'
          exact hb ⟨E, hE, hE'⟩
        have hrow : Th2Row.r4c.holds x y K T S := by
          simp only [Th2Row.holds]
          exact ⟨hq5, hG.pRank_eq_four, hb'⟩
        refine ⟨.r4c, hrow, hSnT, fun B hB => ⟨isE_of_isSn le_rfl hB (by decide), ?_⟩⟩
        exact isKBal_one_of_balanced (hb' B ⟨le_top, hB.1.2.1, hB.2⟩)
    · by_cases hfm : IsFM9 (p ^ f)
      · have hrow : Th2Row.r2.holds x y K T S := by
          simp only [Th2Row.holds]
          exact ⟨p, f, hp, hf, ⟨hqodd, hfm, h5⟩, hmodel⟩
        exact ⟨.r2, hrow, hSnR, fun B hB =>
          ⟨isE_of_isSn hRT hB le_rfl, hbal G hG x y K T S h .r2
            (Or.inr (Or.inl rfl)) hrow B hB⟩⟩
      · have hrow : Th2Row.r1b.holds x y K T S := by
          simp only [Th2Row.holds]
          exact ⟨⟨p, f, hp, hf, ⟨hqodd, hfm⟩, hmodel⟩, Or.inr (by omega)⟩
        exact ⟨.r1b, hrow, hSnR, fun B hB =>
          ⟨isE_of_isSn hRT hB le_rfl, hbal G hG x y K T S h .r1b (Or.inl rfl) hrow B hB⟩⟩
  · obtain ⟨D₀, hD₀⟩ := exists_isDSub h.sylow_P h7
    have hD₀P : D₀ ≤ T ⊓ K := hD₀.1
    have hD₀el : CFSG.IsElementaryAbelian 2 ↥D₀ := hD₀.2.2.1
    have hD₀four : IsFourSub (T ⊓ K) D₀ := ⟨hD₀P, hD₀el, hD₀.2.2.2.1⟩
    by_cases h3b' : Nat.card ↥(T ⊓ CxK x K) = 4 ∧ T < S
    · have hrow : Th2Row.r3b.holds x y K T S := by
        simp only [Th2Row.holds]
        exact ⟨h7, h3b'.1, h3b'.2⟩
      refine ⟨.r3b, hrow, ⟨_, D₀, hD₀, rfl⟩, fun B hB => ?_⟩
      obtain ⟨D, hD, hBeq⟩ := hB
      obtain ⟨hel, hrk, hle⟩ := h3b G hG x y K T S h h7 h3b'.1 h3b'.2 D hD
      subst hBeq
      exact ⟨⟨hle, hel, hrk⟩, hbal G hG x y K T S h .r3b (Or.inr (Or.inr (Or.inl rfl))) hrow _
        ⟨D, hD, rfl⟩⟩
    · have h2 : 2 ≤ pRank 2 ↥(CxK x K) := by
        rcases hv.2.2.1 with h2 | hex
        · exact h2
        · exact absurd (h.exceptional_A7_data hex) h3b'
      have hQ4 : 4 ≤ Nat.card ↥(T ⊓ CxK x K) := by
        obtain ⟨E, hEQ, hEel, hErk⟩ := exists_elemAbelian_pRank (T ⊓ CxK x K)
        have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hEel
        have h2' : Nat.card ↥E ≤ Nat.card ↥(T ⊓ CxK x K) := Subgroup.card_le_of_le hEQ
        have hQ2 : 2 ≤ pRank 2 ↥(T ⊓ CxK x K) := by
          rw [pRank_eq_of_isSylowOf h.sylow_Q]
          exact h2
        have h3 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥E := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hrow : Th2Row.r3c.holds x y K T S := by
        simp only [Th2Row.holds]
        refine ⟨h7, Or.inr (by omega), ?_⟩
        by_cases hc4 : Nat.card ↥(T ⊓ CxK x K) = 4
        · exact Or.inr (eq_of_le_of_not_lt h.T_le_S fun hlt => h3b' ⟨hc4, hlt⟩)
        · exact Or.inl (lt_of_le_of_ne hQ4 (Ne.symm hc4))
      have hPQ := h.commDisj hcen
      have hCD : CommDisj D₀ (T ⊓ CxK x K) :=
        ⟨fun a ha b hb => hPQ.comm a (hD₀P ha) b hb,
          eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (hPQ.eq_one_of_mem (hD₀P hz.1) hz.2)⟩
      obtain ⟨E, hE, hErk⟩ := h.exists_isS_Q' h2
      have hmem : D₀ ⊔ E ∈ {B'' : Subgroup G | IsSn 4 (D₀ ⊔ (T ⊓ CxK x K)) B''} := by
        refine ⟨hCD.isS_sup (isS_self hD₀el) hE, ?_⟩
        show 4 ≤ pRank 2 ↥(D₀ ⊔ E)
        rw [hCD.pRank_sup hD₀el hE.2.1 le_rfl hE.1, pRank_of_isFourSub hD₀four]
        omega
      have hmem' := (Set.ext_iff.1 (bt_3c_eq h h7 hD₀) (D₀ ⊔ E)).2 hmem
      exact ⟨.r3c, hrow, ⟨_, hmem'⟩, fun B hB =>
        ⟨isE_of_isSn hRT hB.1 le_rfl, hbal G hG x y K T S h .r3c
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hrow B hB⟩⟩
  · exact (hL34 G hG.gen4 x K h.orderOf_x h.comp ⟨hL34', hel, hcard⟩).elim

end CFSG.GH74.GLS
