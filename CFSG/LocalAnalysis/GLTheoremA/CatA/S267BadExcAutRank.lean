module

public import CFSG.LieType.SeitzGeneration.ExcHigh.CubePlanes
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Rank4
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSignalizer
import CFSG.GH74.Uniqueness.SU.SU7Gen3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.CrossChar (sylowTorus_of_blocks_of_three_lt not_dvd_of_blocks
  not_dvd_div_of_720 exists_hom_ringAut_E exists_hom_cyclic_F4 exists_hom_ringAut_twistedE6
  coprime_card_ringAut rankLE2_cat_E6 rankLE2_cat_E7 rankLE2_cat_E8 rankLE2_cat_twistedE6
  eq_of_three_le_degCount_E6 eq_of_three_le_degCount_E7 eq_of_three_le_degCount_E8
  eq_of_three_le_degCountTw)

theorem pRank_mulAut_le_of_hom {S N C : Type*} [Group S] [Finite S] [Group N] [Group C]
    [IsCyclic C] (e : S ≃* N) (Θ : MulAut N →* C) {p n f : ℕ} (hp : p.Prime)
    (hΘ : ∀ x ∈ Θ.ker, x ^ p = 1 → x ∈ (MulAut.conj : N →* MulAut N).range)
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    (hS : ∀ F : Subgroup S, IsElemAbelian p F → Nat.card F ≤ p ^ n)
    (hf : ¬ p ∣ f → Nat.Coprime p (Nat.card C)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ n + if p ∣ f then 1 else 0 := by
  refine CFSG.SectionRank.pRank_le (G := MulAut S) hp.one_lt fun E _ hE => ?_
  set Ψ : MulAut S →* C := Θ.comp (MulAut.congr e).toMonoidHom with hΨ
  have hin : E ⊓ Ψ.ker ≤ (MulAut.conj : S →* MulAut S).range := by
    intro x hx
    obtain ⟨m, hm⟩ := hΘ (MulAut.congr e x) hx.2 (by rw [← map_pow, hE.2 x hx.1, map_one])
    refine ⟨e.symm m, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hm
  have h2 : Nat.card ↥(E ⊓ Ψ.ker) ≤ p ^ n := by
    have hFE : ((E ⊓ Ψ.ker).comap (MulAut.conj : S →* MulAut S)).map
        (MulAut.conj : S →* MulAut S) = E ⊓ Ψ.ker := Subgroup.map_comap_eq_self hin
    rw [← hFE, Subgroup.card_map_of_injective hinj]
    exact hS _ (isElemAbelian_comap_of_injective _ hinj (CFSG.Open.IsElemAbelian.mono hE inf_le_left))
  have h3 := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Ψ E
  split_ifs with hpf
  ·
    have h1 : Nat.card (E.map Ψ) ≤ p := by
      haveI : Finite ↥(E.map Ψ) := Finite.of_surjective
        (fun x : ↥E => (⟨Ψ x, Subgroup.mem_map_of_mem Ψ x.2⟩ : ↥(E.map Ψ)))
        (fun y => by
          obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
          exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)
      refine CFSG.LocalAnalysis.RankFourTheoremC.card_le_of_isCyclic_of_pow_eq_one hp.pos
        fun y => ?_
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxy, ← map_pow, hE.2 x hx, map_one]
    calc Nat.card E = Nat.card (E.map Ψ) * Nat.card ↥(E ⊓ Ψ.ker) := h3.symm
      _ ≤ p * p ^ n := Nat.mul_le_mul h1 h2
      _ = p ^ (n + 1) := by rw [pow_succ, mul_comm]
  ·
    have h1 : E.map Ψ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (pow_eq_one_iff_of_coprime (hf hpf)).1
        ⟨by rw [← map_pow, hE.2 x hx, map_one], pow_card_eq_one'⟩
    rw [h1, Subgroup.card_bot, one_mul] at h3
    rw [add_zero, ← h3]
    exact h2

theorem five_le_of_three_le_orderOf {p Q : ℕ} (hp : p.Prime)
    (he : 3 ≤ orderOf ((Q : ℕ) : ZMod p)) : 5 ≤ p := by
  haveI := Fact.mk hp
  have h0 : ((Q : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at he
    omega
  have hd : orderOf ((Q : ℕ) : ZMod p) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h0)
  have hle := Nat.le_of_dvd (by have := hp.two_le; omega) hd
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  omega

theorem card_le_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p n : ℕ}
    (h : ∀ F : Subgroup Y, IsElemAbelian p F → Nat.card F ≤ p ^ n) (F : Subgroup X)
    (hF : IsElemAbelian p F) : Nat.card F ≤ p ^ n := by
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact h _ (CFSG.SectionRank.isElemAbelian_map hF e.toMonoidHom)

private theorem card_le_pow_of_le {G : Type*} [Group G] {p m n : ℕ} (hp : p.Prime) {F : Subgroup G}
    (h : Nat.card F ≤ p ^ m) (hmn : m ≤ n) : Nat.card F ≤ p ^ n :=
  h.trans (Nat.pow_le_pow_right hp.pos hmn)

section Cat

theorem sylowTorus_cat_E7_three {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 3) : SylowTorus (Cat ⟨.E7 q, hv⟩) p 3 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  have hS : SylowTorus (adjointGroup Tag.E7 K) p ([1, 3, 3, 3].count 3) :=
    sylowTorus_of_blocks_of_three_lt 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E7 e7ThreeWord) [1, 3, 3, 3] e7Three_charpoly e7Three_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
  exact (show SylowTorus (adjointGroup Tag.E7 K) p 3 from hS).of_mulEquiv e.symm

theorem sylowTorus_cat_E8_four {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 4) : SylowTorus (Cat ⟨.E8 q, hv⟩) p 4 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  have hS : SylowTorus (adjointGroup Tag.E8 K) p ([4, 4, 4, 4].count 4) :=
    sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E8 e8FourWord) [4, 4, 4, 4] e8Four_charpoly e8Four_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
  exact (show SylowTorus (adjointGroup Tag.E8 K) p 4 from hS).of_mulEquiv e.symm

theorem card_le_cat_F4 {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.F4 Q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p))
    {F : Subgroup (Cat ⟨.F4 Q, hv⟩)} (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ max 1 (degCount Tag.F4 (orderOf ((Q.card : ℕ) : ZMod p))) := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨e, he'⟩ : ∃ e, orderOf ((Q.card : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he'] at he ⊢
  have h2 : degCount Tag.F4 e ≤ 2 := by
    by_contra h3
    have h30 := le_thirty_of_degCount_pos (τ := Tag.F4) (e := e) (by simp) (by omega)
    have key : ∀ e ≤ 30, 3 ≤ e → degCount Tag.F4 e ≤ 2 := by decide
    exact h3 (key e h30 he)
  rcases (by omega : degCount Tag.F4 e ≤ 1 ∨ degCount Tag.F4 e = 2) with h1 | h2'
  · refine card_le_pow_of_le hp ?_ (le_max_left 1 _)
    rw [pow_one]
    exact rankLE1_cat_F4 Q hv hp hpq (he' ▸ h1) F hF
  · rw [h2']
    exact ExcHigh.rankLE2_cat_F4_of_degCount_le_two Q hv hp hp5 hpq (he' ▸ h2) F hF

theorem card_le_cat_E6 {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p))
    {F : Subgroup (Cat ⟨.E6 Q, hv⟩)} (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ max 1 (degCount Tag.E6 (orderOf ((Q.card : ℕ) : ZMod p))) := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨e, he'⟩ : ∃ e, orderOf ((Q.card : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he'] at he ⊢
  rcases lt_or_ge (degCount Tag.E6 e) 3 with h3 | h3
  · rcases (by omega : degCount Tag.E6 e ≤ 1 ∨ degCount Tag.E6 e = 2) with h1 | h2
    · refine card_le_pow_of_le hp ?_ (le_max_left 1 _)
      rw [pow_one]
      exact rankLE1_cat_E6 Q hv hp hpq (he' ▸ h1) F hF
    · rw [h2]
      exact rankLE2_cat_E6 Q hv hp (he' ▸ h2) F hF
  · rcases eq_of_three_le_degCount_E6 h3 with rfl | rfl | rfl
    · omega
    · omega
    · rw [show max 1 (degCount Tag.E6 3) = 3 by decide]
      exact (ExcHigh.sylowTorus_cat_E6_three hv hp (ExcHigh.seven_le_of_orderOf_three hp hp5 he') hpq
        he').rank_le hp hF

theorem card_le_cat_twistedE6 {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid) {p : ℕ} (hp : p.Prime) (hpq : p ≠ Q.p)
    (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p)) {F : Subgroup (Cat ⟨.twistedE6 Q, hv⟩)}
    (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ max 1 (degCountTw (orderOf ((Q.card : ℕ) : ZMod p))) := by
  obtain ⟨e, he'⟩ : ∃ e, orderOf ((Q.card : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he'] at he ⊢
  rcases lt_or_ge (degCountTw e) 3 with h3 | h3
  · rcases (by omega : degCountTw e ≤ 1 ∨ degCountTw e = 2) with h1 | h2
    · refine card_le_pow_of_le hp ?_ (le_max_left 1 _)
      rw [pow_one]
      exact rankLE1_cat_twistedE6 Q hv hp hpq (he' ▸ h1) F hF
    · rw [h2]
      exact rankLE2_cat_twistedE6 Q hv hp (he' ▸ h2) F hF
  · rcases eq_of_three_le_degCountTw h3 with rfl | rfl | rfl
    · omega
    · omega
    · rw [show max 1 (degCountTw 6) = 3 by decide]
      exact (ExcHigh.sylowTorus_cat_twE6_six hv hp (ExcHigh.seven_le_of_orderOf_six hp he') hpq
        he').rank_le hp hF

theorem card_le_cat_E7 {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 Q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p))
    {F : Subgroup (Cat ⟨.E7 Q, hv⟩)} (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ max 1 (degCount Tag.E7 (orderOf ((Q.card : ℕ) : ZMod p))) := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨e, he'⟩ : ∃ e, orderOf ((Q.card : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he'] at he ⊢
  rcases lt_or_ge (degCount Tag.E7 e) 3 with h3 | h3
  · rcases (by omega : degCount Tag.E7 e ≤ 1 ∨ degCount Tag.E7 e = 2) with h1 | h2
    · refine card_le_pow_of_le hp ?_ (le_max_left 1 _)
      rw [pow_one]
      exact rankLE1_cat_E7 Q hv hp hpq (he' ▸ h1) F hF
    · rw [h2]
      exact rankLE2_cat_E7 Q hv hp (he' ▸ h2) F hF
  · rcases eq_of_three_le_degCount_E7 h3 with rfl | rfl | rfl | rfl
    · omega
    · omega
    · rw [show max 1 (degCount Tag.E7 3) = 3 by decide]
      exact (sylowTorus_cat_E7_three hv hp (ExcHigh.seven_le_of_orderOf_three hp hp5 he') hpq
        he').rank_le hp hF
    · rw [show max 1 (degCount Tag.E7 6) = 3 by decide]
      exact (ExcHigh.sylowTorus_cat_E7_six hv hp (ExcHigh.seven_le_of_orderOf_six hp he') hpq
        he').rank_le hp hF

theorem card_le_cat_E8 {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 Q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p))
    (h54 : ¬ (p = 5 ∧ orderOf ((Q.card : ℕ) : ZMod p) = 4)) {F : Subgroup (Cat ⟨.E8 Q, hv⟩)}
    (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ max 1 (degCount Tag.E8 (orderOf ((Q.card : ℕ) : ZMod p))) := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨e, he'⟩ : ∃ e, orderOf ((Q.card : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he'] at he h54 ⊢
  rcases lt_or_ge (degCount Tag.E8 e) 3 with h3 | h3
  · rcases (by omega : degCount Tag.E8 e ≤ 1 ∨ degCount Tag.E8 e = 2) with h1 | h2
    · refine card_le_pow_of_le hp ?_ (le_max_left 1 _)
      rw [pow_one]
      exact rankLE1_cat_E8 Q hv hp hpq (he' ▸ h1) F hF
    · rw [h2]
      exact rankLE2_cat_E8 Q hv hp (he' ▸ h2) F hF
  · rcases eq_of_three_le_degCount_E8 h3 with rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · rw [show max 1 (degCount Tag.E8 3) = 4 by decide]
      exact (ExcHigh.sylowTorus_cat_E8_three hv hp (ExcHigh.seven_le_of_orderOf_three hp hp5 he')
        hpq he').rank_le hp hF
    ·
      have h7 : 7 ≤ p := by
        haveI := Fact.mk hp
        have h0 : ((Q.card : ℕ) : ZMod p) ≠ 0 := by
          intro h0
          rw [h0, orderOf_zero] at he'
          omega
        have h4 : 4 ∣ p - 1 := by
          rw [← he']
          exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h0)
        have h9 : p ≠ 9 := by
          rintro rfl
          norm_num at hp
        omega
      rw [show max 1 (degCount Tag.E8 4) = 4 by decide]
      exact (sylowTorus_cat_E8_four hv hp h7 hpq he').rank_le hp hF
    · rw [show max 1 (degCount Tag.E8 6) = 4 by decide]
      exact (ExcHigh.sylowTorus_cat_E8_six hv hp (ExcHigh.seven_le_of_orderOf_six hp he') hpq
        he').rank_le hp hF

theorem pRank_mulAut_le_F4 (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 Q).Valid)
    {X : Type} [Group X] [Finite X] (eX : X ≃* Cat ⟨.F4 Q, hv⟩) {p : ℕ} (hp : p.Prime)
    (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤
      max 1 (degCount Tag.F4 (orderOf ((Q.card : ℕ) : ZMod p))) +
        if p ∣ Q.exponent then 1 else 0 := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨K, _, _, hK, _, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 Q hv
  obtain ⟨C, _, _, Θ, hC, hker⟩ := exists_hom_cyclic_F4 Q K hK
  refine pRank_mulAut_le_of_hom (eX.trans e) Θ hp (fun x hx _ => hker ▸ hx)
    (conj_injective_of_mulEquiv eX (conj_injective_cat_F4 Q hv))
    (card_le_of_mulEquiv eX fun F hF => card_le_cat_F4 hv hp hpq he hF) fun hf => ?_
  exact Nat.Coprime.coprime_dvd_right hC
    (Nat.Coprime.mul_right (Nat.coprime_two_right.2 (hp.odd_of_ne_two (by omega)))
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hf))

theorem pRank_mulAut_le_E6 (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    {X : Type} [Group X] [Finite X] (eX : X ≃* Cat ⟨.E6 Q, hv⟩) {p : ℕ} (hp : p.Prime)
    (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤
      max 1 (degCount Tag.E6 (orderOf ((Q.card : ℕ) : ZMod p))) +
        if p ∣ Q.exponent then 1 else 0 := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 Q hv
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inl rfl) K hp hp5
  haveI : IsCyclic (RingAut K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  exact pRank_mulAut_le_of_hom (eX.trans e) Θ hp hΘ
    (conj_injective_of_mulEquiv eX (conj_injective_cat_E6 Q hv))
    (card_le_of_mulEquiv eX fun F hF => card_le_cat_E6 hv hp hpq he hF)
    fun hf => coprime_card_ringAut Q K hK hp hf

theorem pRank_mulAut_le_twistedE6 (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid) {X : Type} [Group X] [Finite X]
    (eX : X ≃* Cat ⟨.twistedE6 Q, hv⟩) {p : ℕ} (hp : p.Prime) (hpq : p ≠ Q.p)
    (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤
      max 1 (degCountTw (orderOf ((Q.card : ℕ) : ZMod p))) + if p ∣ Q.exponent then 1 else 0 := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 Q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ Q.prime_p.ne_zero))
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_twistedE6 Q.prime_p Q.exponent_pos K hK σ hσ hp
    (by omega)
  haveI : IsCyclic (RingAut K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  refine pRank_mulAut_le_of_hom (eX.trans e) Θ hp hΘ
    (conj_injective_of_mulEquiv eX (conj_injective_cat_twistedE6 Q hv))
    (card_le_of_mulEquiv eX fun F hF => card_le_cat_twistedE6 hv hp hpq he hF) fun hf => ?_
  have hK2 : Nat.card K = Q.p ^ (Q.exponent * 2) := by rw [hK, ← pow_mul]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Q.prime_p (by have := Q.exponent_pos; omega) hK2
  rw [hcard]
  exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hf)
    (Nat.coprime_two_right.2 (hp.odd_of_ne_two (by omega)))

theorem pRank_mulAut_le_E7 (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 Q).Valid)
    {X : Type} [Group X] [Finite X] (eX : X ≃* Cat ⟨.E7 Q, hv⟩) {p : ℕ} (hp : p.Prime)
    (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤
      max 1 (degCount Tag.E7 (orderOf ((Q.card : ℕ) : ZMod p))) +
        if p ∣ Q.exponent then 1 else 0 := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 Q hv
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inr (Or.inl rfl)) K hp hp5
  haveI : IsCyclic (RingAut K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  exact pRank_mulAut_le_of_hom (eX.trans e) Θ hp hΘ
    (conj_injective_of_mulEquiv eX (conj_injective_cat_E7 Q hv))
    (card_le_of_mulEquiv eX fun F hF => card_le_cat_E7 hv hp hpq he hF)
    fun hf => coprime_card_ringAut Q K hK hp hf

theorem pRank_mulAut_le_E8 (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 Q).Valid)
    {X : Type} [Group X] [Finite X] (eX : X ≃* Cat ⟨.E8 Q, hv⟩) {p : ℕ} (hp : p.Prime)
    (hpq : p ≠ Q.p) (he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p))
    (h54 : ¬ (p = 5 ∧ orderOf ((Q.card : ℕ) : ZMod p) = 4)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤
      max 1 (degCount Tag.E8 (orderOf ((Q.card : ℕ) : ZMod p))) +
        if p ∣ Q.exponent then 1 else 0 := by
  have hp5 := five_le_of_three_le_orderOf hp he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 Q hv
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inr (Or.inr rfl)) K hp hp5
  haveI : IsCyclic (RingAut K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  exact pRank_mulAut_le_of_hom (eX.trans e) Θ hp hΘ
    (conj_injective_of_mulEquiv eX (conj_injective_cat_E8 Q hv))
    (card_le_of_mulEquiv eX fun F hF => card_le_cat_E8 hv hp hpq he h54 hF)
    fun hf => coprime_card_ringAut Q K hK hp hf

end Cat

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
