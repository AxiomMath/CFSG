module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR1

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

section Row4c

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_le_thetaK_one {B : Subgroup G} {t : G} (htB : t ∈ B) (ht2 : orderOf t = 2) :
    pPrimeCoreOf 2 (centralizer ({t} : Set G)) ≤ thetaK 1 B := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  have hD : IsE 1 B (zpowers t) :=
    ⟨zpowers_le.2 htB, Th2.isElementaryAbelian_zpowers_of_orderOf_two ht2, by
      rw [Th2.pRank_zpowers_of_orderOf_two ht2]⟩
  have hAG : AG (zpowers t) = pPrimeCoreOf 2 (centralizer ({t} : Set G)) := by
    unfold AG
    apply le_antisymm
    · exact iInf₂_le t ⟨mem_zpowers t, ht1⟩
    · refine le_iInf₂ fun b hb => ?_
      rcases mem_zpowers_two ht2 hb.1 with h0 | h0
      · exact absurd h0 hb.2
      · rw [h0]
  rw [← hAG]
  exact le_iSup₂_of_le (zpowers t) hD le_rfl

variable {x y : G} {K T S : Subgroup G}

private theorem isS_of_isE_rank_of_pRank_eq_four
    (hr4 : pRank 2 G = 4) {X A : Subgroup G} (hAX : A ≤ X)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA4 : 4 ≤ pRank 2 ↥A) :
    IsS X A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAc, hAs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  refine ⟨hAX, hAel, le_antisymm ?_ ?_⟩
  · refine le_of_eq_of_le rfl ?_
    exact le_omega1_of_isElementaryAbelian hAel (le_inf hAX (fun a ha => by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hAc b hb a ha))
  · refine (Subgroup.closure_le A).2 ?_
    rintro u ⟨⟨huX, huC⟩, hu2⟩
    by_contra huA
    have hucomm : ∀ a ∈ A, a * u = u * a := fun a ha =>
      Subgroup.mem_centralizer_iff.1 huC a ha
    have hu1 : u ≠ 1 := fun h => huA (h ▸ A.one_mem)
    have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
    have hzel := isElementaryAbelian_zpowers_of_orderOf_two hu2'
    have hcd : CommDisj A (zpowers u) := by
      refine ⟨fun a ha z hz => ?_, eq_bot_iff.2 fun z hz => ?_⟩
      · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hz
        exact (Commute.zpow_right (hucomm a ha) m).eq
      · rcases mem_zpowers_two hu2' hz.2 with h0 | h0
        · simp [h0]
        · exact absurd (h0 ▸ hz.1) huA
    have hrk := hcd.pRank_sup hAel hzel le_rfl le_rfl
    rw [pRank_zpowers_of_orderOf_two hu2'] at hrk
    have h4 := pRank_le_top' (A ⊔ zpowers u)
    have h5 := hr4
    omega

theorem p72c_row4c
    (h : Th2Std x y K T S) (hnt : ¬ IsTerminalPair 2 x K)
    (hL2 : HasL2Model (kBar K) (fun q => q = 5))
    (hr4 : pRank 2 G = 4) :
    ∃ B ∈ Th2Row.r4c.BT x K T S, Th2Row.r4c.level.theta B ≠ ⊥ ∧
      pRank 2 ↥(B ⊓ (T ⊓ K)) = pRank 2 ↥(T ⊓ K) := by
  classical
  have hPr : ∀ q : ℕ, q = 5 → Odd q := by
    rintro q rfl
    decide
  have hcen := centerlessBar_of_hasL2Model hPr hL2
  have hP := rankTwoShape_sylow_L2 h.sylow_P (TwoThin.isQuasisimple_hat h.comp) hPr hL2
  have hPQ := h.commDisj hcen
  have hR : ∀ u ∈ T ⊓ CxK x K, orderOf u = 2 →
      3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) :=
    fun u hu hu2 => h.three_le_pRank_centralizer hcen hP hu hu2
  obtain ⟨t, htQ, ht2, J, hJlt, hJnq⟩ := h.exists_nonqs_pumpup hnt hR
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hJlt.2.1.2.2
  have hOJ : pPrimeCore 2 ↥J ≠ ⊥ := by
    intro hO
    apply hJnq
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdata :=
      (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff
        (p := 2) J (centralizer ({t} : Set G)) hJc.1).mp hJc.2
    have e : (↥J ⧸ pPrimeCore 2 ↥J) ≃* ↥J :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hdata.2.2
  have htO : pPrimeCoreOf 2 (centralizer ({t} : Set G)) ≠ ⊥ := by
    intro hO
    have hle : pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) := by
      obtain ⟨H, -, hsub, -⟩ := hJc.2
      exact Th2.pPrimeCoreOf_le_of_subnormal ⟨hJc.1, hsub⟩
    have hOJbot : pPrimeCore 2 ↥J = ⊥ := by
      apply CFSG.GH74.GLS.Th2.P72c.pPrimeCore_eq_bot_of_pPrimeCoreOf_eq_bot
      exact le_bot_iff.mp (hle.trans (le_of_eq hO))
    exact hOJ hOJbot
  have hP4 := card_sylow_L2_five h.sylow_P hL2
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  have hUP : U = T ⊓ K := Subgroup.eq_of_le_of_card_ge hU.1 (by rw [hU.2.2, hP4])
  have hPel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ K) := hUP ▸ hU.2.1
  have hPrk : pRank 2 ↥(T ⊓ K) = 2 := by rw [← hUP]; exact pRank_of_isFourSub hU
  have hQ : IsPGroup 2 ↥(T ⊓ CxK x K) := h.T_pGroup.to_le inf_le_left
  have hnot7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := by
    obtain ⟨e5⟩ := C3.Layer1.Back.nonempty_alt5_of_hasL2Model5 hL2
    rintro ⟨e7⟩
    have h1 := Nat.card_congr (e7.symm.trans e5).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at h1
    simp [Nat.factorial] at h1
  obtain ⟨E₀, hE₀, hE₀rk⟩ := h.exists_isS_Q hnot7
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
  have hBel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ K ⊔ E) :=
    hPQ.isElementaryAbelian_sup' hPel hE.2.1 le_rfl hE.1
  have hBrk : pRank 2 ↥(T ⊓ K ⊔ E) = 2 + pRank 2 ↥E := by
    rw [hPQ.pRank_sup hPel hE.2.1 le_rfl hE.1, hPrk]
  have hBT : T ⊓ K ⊔ E ≤ T := sup_le inf_le_left (hE.1.trans inf_le_left)
  have hB4 : 4 ≤ pRank 2 ↥(T ⊓ K ⊔ E) := by omega
  have htB : t ∈ T ⊓ K ⊔ E := Subgroup.mem_sup_right (htE (mem_zpowers t))
  refine ⟨T ⊓ K ⊔ E,
    ⟨isS_of_isE_rank_of_pRank_eq_four hr4 hBT hBel hB4, hB4⟩, ?_, ?_⟩
  · show thetaK 1 (T ⊓ K ⊔ E) ≠ ⊥
    intro h0
    apply htO
    exact le_bot_iff.1 (h0 ▸ pPrimeCoreOf_le_thetaK_one htB ht2)
  · rw [inf_eq_right.2 (le_sup_left : T ⊓ K ≤ T ⊓ K ⊔ E)]

end Row4c

section Reduction

@[expose] def B_thm2_p72c_rows : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ¬ IsTerminalPair 2 x K → ∀ ρ : Th2Row,
      (ρ = .r1b ∨ ρ = .r2 ∨ ρ = .r3b ∨ ρ = .r3c ∨ ρ = .r4b) → ρ.holds x y K T S →
        (∀ B ∈ ρ.BT x K T S, ρ.level.IsBal B) →
          ∃ B ∈ ρ.BT x K T S, ρ.level.theta B ≠ ⊥ ∧
            pRank 2 ↥(B ⊓ (T ⊓ K)) = pRank 2 ↥(T ⊓ K)

theorem b_thm2_p72c_of (hL34 : B_gen4_noL34_elem)
    (h102 : B_ivk_10_2) (hrows : B_thm2_p72c_rows) : B_thm2_p72c := by
  intro G _ _ hG x y K T S h hnt ρ hρ hbal
  obtain ⟨hcen, hP⟩ := h.centerless_and_shape hG hL34 h102
  cases ρ with
  | r1a => exact (false_of_three_le_rank_Q hG h hcen hP hρ.2.2).elim
  | r1b => exact hrows G hG x y K T S h hnt .r1b (Or.inl rfl) hρ hbal
  | r2 => exact hrows G hG x y K T S h hnt .r2 (Or.inr (Or.inl rfl)) hρ hbal
  | r3a => exact (false_of_three_le_rank_Q hG h hcen hP hρ.2.2).elim
  | r3b => exact hrows G hG x y K T S h hnt .r3b (Or.inr (Or.inr (Or.inl rfl))) hρ hbal
  | r3c => exact hrows G hG x y K T S h hnt .r3c (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hρ hbal
  | r4a => exact (false_of_three_le_rank_Q hG h hcen hP hρ.2).elim
  | r4b => exact hrows G hG x y K T S h hnt .r4b (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hρ hbal
  | r4c => exact p72c_row4c h hnt hρ.1 hρ.2.1
  | r5 => exact (hL34 G hG.gen4 x K h.orderOf_x h.comp hρ).elim

end Reduction

end CFSG.GH74.GLS
