module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTwE6
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesReeF4
public import CFSG.LocalAnalysis.GLTheoremA.NoSylowCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXKF4Two

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263

@[expose] def t263GHard2Vac (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q | .E7 q | .E8 q => q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 ∧ p ≠ 5 ∧ p ≠ 7
    | .twistedE6 q => q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GHard2Small (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q | .E7 q | .E8 q => q.card = 2 ∧ (p = 5 ∨ p = 7)
    | _ => False

section Vac


section Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

private theorem five_le_of_card_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hq : q.card = 2) (hpq : ¬ p ∣ q.card ^ 2 - 1) : 5 ≤ p :=
  hp.five_le_of_ne_two_of_ne_three hp2 (by rintro rfl; exact hpq (by rw [hq]; norm_num))

private theorem prime_dvd_fifteen {p : ℕ} (hp : p.Prime) (h : p ∣ 15) : p = 3 ∨ p = 5 := by
  have h' : p ∣ 3 * 5 := h
  rcases hp.dvd_mul.mp h' with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)

private theorem prime_dvd_sixtyThree {p : ℕ} (hp : p.Prime) (h : p ∣ 63) : p = 3 ∨ p = 7 := by
  have h' : p ∣ 3 ^ 2 * 7 := h
  rcases hp.dvd_mul.mp h' with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h1))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)

private theorem not_dvd_two_pow_sub_one {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpne5 : p ≠ 5)
    (hpne7 : p ≠ 7) (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6)
    (hdvd : p ∣ 2 ^ e - 1) : False := by
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact absurd (Nat.le_of_dvd one_pos hdvd) (by omega)
  · exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  · exact hpne7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hdvd)
  · rcases prime_dvd_fifteen hp hdvd with h | h
    · omega
    · exact hpne5 h
  · rcases prime_dvd_sixtyThree hp hdvd with h | h
    · omega
    · exact hpne7 h

private theorem degCount_mem_of_two {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {e : ℕ}
    (h : 2 ≤ degCount τ e) : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 : e ≤ 30 :=
    le_thirty_of_degCount_pos (τ := τ) (by rcases hτ with rfl | rfl <;> simp) (by omega)
  have key : ∀ e : Fin 31, 2 ≤ degCount τ (e : ℕ) →
      ((e : ℕ) = 1 ∨ (e : ℕ) = 2 ∨ (e : ℕ) = 3 ∨ (e : ℕ) = 4 ∨ (e : ℕ) = 6) := by
    rcases hτ with rfl | rfl <;> decide
  exact key ⟨e, by omega⟩ h

private theorem degCount_E8_mem {e : ℕ} (h : 2 ≤ degCount Tag.E8 e) :
    (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) ∨ (e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12) := by
  have h30 : e ≤ 30 := le_thirty_of_degCount_pos (τ := Tag.E8) (by simp) (by omega)
  have key : ∀ e : Fin 31, 2 ≤ degCount Tag.E8 (e : ℕ) →
      (((e : ℕ) = 1 ∨ (e : ℕ) = 2 ∨ (e : ℕ) = 3 ∨ (e : ℕ) = 4 ∨ (e : ℕ) = 6) ∨
        ((e : ℕ) = 5 ∨ (e : ℕ) = 8 ∨ (e : ℕ) = 10 ∨ (e : ℕ) = 12)) := by decide
  exact key ⟨e, by omega⟩ h

private theorem degCountTw_mem {e : ℕ} (h : 2 ≤ degCountTw e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h60 : e ≤ 60 := le_sixty_of_degCountTw_pos (by omega)
  have key : ∀ e : Fin 61, 2 ≤ degCountTw (e : ℕ) →
      ((e : ℕ) = 1 ∨ (e : ℕ) = 2 ∨ (e : ℕ) = 3 ∨ (e : ℕ) = 4 ∨ (e : ℕ) = 6) := by decide
  exact key ⟨e, by omega⟩ h

private theorem prime_mem_of_dvd_E8 {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpne5 : p ≠ 5)
    (hpne7 : p ≠ 7) (he : e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12) (hdvd : p ∣ 2 ^ e - 1) :
    p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 31 := by
  have hp31 : Nat.Prime 31 := by norm_num
  rcases he with rfl | rfl | rfl | rfl
  · rw [show (2 : ℕ) ^ 5 - 1 = 31 by norm_num] at hdvd
    exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hp31).1 hdvd)))
  · rw [show (2 : ℕ) ^ 8 - 1 = 15 * 17 by norm_num] at hdvd
    rcases hp.dvd_mul.mp hdvd with h | h
    · rcases prime_dvd_fifteen hp h with h3 | h5
      · omega
      · exact absurd h5 hpne5
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)))
  · rw [show (2 : ℕ) ^ 10 - 1 = 3 * 341 by norm_num] at hdvd
    rcases hp.dvd_mul.mp hdvd with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · rw [show (341 : ℕ) = 11 * 31 by norm_num] at h
      rcases hp.dvd_mul.mp h with h11 | h31
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h11)
      · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hp31).1 h31)))
  · rw [show (2 : ℕ) ^ 12 - 1 = 63 * 65 by norm_num] at hdvd
    rcases hp.dvd_mul.mp hdvd with h | h
    · rcases prime_dvd_sixtyThree hp h with h3 | h7
      · omega
      · exact absurd h7 hpne7
    · rw [show (65 : ℕ) = 5 * 13 by norm_num] at h
      rcases hp.dvd_mul.mp h with h5 | h13
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5) hpne5
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h13))

private theorem card_le_of_noSylowNormalizesTwo {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime)
    (hN : NoSylowNormalizesTwo p X) (hfac : (Nat.card X).factorization p ≤ 2) {E U : Subgroup X}
    (hE : IsElemAbelian p E) (hU2 : IsPGroup 2 U) (hU : U ≠ ⊥)
    (hEU : E ≤ Subgroup.normalizer (U : Set X)) : Nat.card E ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  calc Nat.card E ≤ p ^ ((Nat.card X).factorization p - 1) :=
        hN.card_le_pow_factorization_sub_one hp
          (CFSG.LieType.SeitzGeneration.isPGroup_of_isElemAbelian hE) hU hU2 hEU
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    _ = p := pow_one p

private theorem e6_card_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpne5 : p ≠ 5)
    (hpne7 : p ≠ 7) {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) {X : Type*} [Group X]
    (eX : Cat ⟨.E6 q, hv⟩ ≃* X) {E U : Subgroup X} (hE : IsElemAbelian p E)
    (hU2 : IsPGroup 2 U) (hU : U ≠ ⊥) (hEU : E ≤ Subgroup.normalizer (U : Set X)) :
    Nat.card E ≤ p := by
  obtain ⟨K, hfield, hfin, hK, -, ⟨eA⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  letI := hfield
  letI := hfin
  have hqp : q.p = 2 :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.primePower_p_eq_two_of_card_eq_two hq
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp (by rw [hqp]; omega)
  have hrd : orderOf ((2 : ℕ) : ZMod p) = orderOf ((Nat.card K : ℕ) : ZMod p) := by
    rw [hK, hq]
  have hcnt : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by
    by_contra hlt
    have hdvd := (CFSG.Timmesfeld.Bang.primitive_of_orderOf hrd).1
    exact not_dvd_two_pow_sub_one hp hp5 hpne5 hpne7
      (degCount_mem_of_two (Or.inl rfl) (by omega)) hdvd
  exact (RankLE1.of_mulEquiv (eA.symm.trans eX) (rankLE1_E6 K hp hpK hcnt)) E hE

private theorem e7_card_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpne5 : p ≠ 5)
    (hpne7 : p ≠ 7) {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) {X : Type*} [Group X]
    (eX : Cat ⟨.E7 q, hv⟩ ≃* X) {E U : Subgroup X} (hE : IsElemAbelian p E)
    (hU2 : IsPGroup 2 U) (hU : U ≠ ⊥) (hEU : E ≤ Subgroup.normalizer (U : Set X)) :
    Nat.card E ≤ p := by
  obtain ⟨K, hfield, hfin, hK, -, ⟨eA⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  letI := hfield
  letI := hfin
  have hqp : q.p = 2 :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.primePower_p_eq_two_of_card_eq_two hq
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp (by rw [hqp]; omega)
  have hrd : orderOf ((2 : ℕ) : ZMod p) = orderOf ((Nat.card K : ℕ) : ZMod p) := by
    rw [hK, hq]
  have hcnt : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by
    by_contra hlt
    have hdvd := (CFSG.Timmesfeld.Bang.primitive_of_orderOf hrd).1
    exact not_dvd_two_pow_sub_one hp hp5 hpne5 hpne7
      (degCount_mem_of_two (Or.inr rfl) (by omega)) hdvd
  exact (RankLE1.of_mulEquiv (eA.symm.trans eX) (rankLE1_E7 K hp hpK hcnt)) E hE

private theorem e8_card_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpne5 : p ≠ 5)
    (hpne7 : p ≠ 7) {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {X : Type*} [Group X]
    (eX : Cat ⟨.E8 q, hv⟩ ≃* X) {E U : Subgroup X} (hE : IsElemAbelian p E)
    (hU2 : IsPGroup 2 U) (hU : U ≠ ⊥) (hEU : E ≤ Subgroup.normalizer (U : Set X)) :
    Nat.card E ≤ p := by
  obtain ⟨K, hfield, hfin, hK, hKchar, ⟨eA⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  letI := hfield
  letI := hfin
  have hq2 : q.p = 2 :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.primePower_p_eq_two_of_card_eq_two hq
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp (by rw [hq2]; omega)
  haveI : CharP K 2 := by rw [← hq2]; exact hKchar
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  have hrd : orderOf ((2 : ℕ) : ZMod p) = e := by
    rw [← he, hK, hq]
  have hdvd : p ∣ 2 ^ e - 1 := (CFSG.Timmesfeld.Bang.primitive_of_orderOf hrd).1
  haveI : Finite X := Finite.of_equiv (adjointGroup Tag.E8 K) (eA.symm.trans eX).toEquiv
  by_cases hcnt : degCount Tag.E8 e ≤ 1
  · rw [← he] at hcnt
    exact (RankLE1.of_mulEquiv (eA.symm.trans eX) (rankLE1_E8 K hp hpK hcnt)) E hE
  · have h2 : 2 ≤ degCount Tag.E8 e := by omega
    have hbig : e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by
      rcases degCount_E8_mem h2 with h | h
      · exact (not_dvd_two_pow_sub_one hp hp5 hpne5 hpne7 h hdvd).elim
      · exact h
    have hpE : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 31 :=
      prime_mem_of_dvd_E8 hp hp5 hpne5 hpne7 hbig hdvd
    have hN : NoSylowNormalizesTwo p (adjointGroup Tag.E8 K) :=
      noSylowNormalizesTwo_E8 hp hp5 hpK he hbig
    have hNX : NoSylowNormalizesTwo p X :=
      noSylowNormalizesTwo_of_mulEquiv (eA.symm.trans eX).symm hN
    have hcardX : Nat.card X = ordE8 2 := by
      rw [← Nat.card_congr (eA.symm.trans eX).toEquiv,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hK, hq]
    have hfac : (Nat.card X).factorization p ≤ 2 := by
      rw [hcardX]
      have hne : ordE8 2 ≠ 0 := by norm_num [ordE8]
      have h3 : ¬ p ^ 3 ∣ ordE8 2 := by
        rcases hpE with rfl | rfl | rfl | rfl <;> norm_num [ordE8]
      by_contra h
      exact h3 ((hp.pow_dvd_iff_le_factorization hne).2 (by omega))
    exact card_le_of_noSylowNormalizesTwo hp hNX hfac hE hU2 hU hEU

private theorem twE6_class {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ 3)
    (he : orderOf (((2 ^ 1 : ℕ)) : ZMod p) = e) (h : 2 ≤ degCountTw e) : e = 3 ∨ e = 4 := by
  rcases degCountTw_mem h with h1 | h1 | h1 | h1 | h1
  · rw [h1] at he
    have hdvd : p ∣ 2 ^ (1 : ℕ) - 1 := (CFSG.Timmesfeld.Bang.primitive_of_orderOf he).1
    exact absurd (Nat.le_of_dvd one_pos hdvd) (by omega)
  · refine absurd ?_ hpq
    rw [h1] at he
    simpa using (CFSG.Timmesfeld.Bang.primitive_of_orderOf he).1
  · exact Or.inl h1
  · exact Or.inr h1
  · subst h1
    have h63 : p ∣ 63 := by
      have := (CFSG.Timmesfeld.Bang.primitive_of_orderOf he).1
      simpa using this
    rcases prime_dvd_sixtyThree hp h63 with h3 | h7
    · subst h3
      exact absurd (dvd_refl 3) hpq
    · subst h7
      have he6 : orderOf (2 : ZMod 7) = 6 := by simpa using he
      have hpow : (2 : ZMod 7) ^ 3 = 1 := by decide
      have hdvd3 : orderOf (2 : ZMod 7) ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hpow
      rw [he6] at hdvd3
      omega

private theorem twE6_card_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {q : TauCeti.PrimePower}
    (hq : q.card = 2) (hpq : ¬ p ∣ q.card ^ 2 - 1)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {X : Type*} [Group X]
    (eX : Cat ⟨.twistedE6 q, hv⟩ ≃* X) {E U : Subgroup X} (hE : IsElemAbelian p E)
    (hU2 : IsPGroup 2 U) (hU : U ≠ ⊥) (hEU : E ≤ Subgroup.normalizer (U : Set X)) :
    Nat.card E ≤ p := by
  obtain ⟨K, hfield, σ, hK0, hσ0, ⟨eK⟩⟩ := exists_catEquiv_twistedE6 q hv
  letI := hfield
  have hq2 : q.p = 2 :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.primePower_p_eq_two_of_card_eq_two hq
  have hqcard : q.p ^ q.exponent = 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  have hK4 : Nat.card K = 2 ^ 2 := by rw [hK0, hqcard]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK4]; norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 2) hK4
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK4
  have hσc : ∀ c, σ c = c ^ 2 ^ 1 := by
    intro c
    rw [hσ0 c, hqcard]
    norm_num
  have hpq' : ¬ p ∣ 2 ^ 1 := by
    have h2 : (2 : ℕ) ^ 1 = q.card := by rw [pow_one, hq]
    rw [h2]
    exact not_dvd_card_of_ne hp (by omega)
  obtain ⟨e, he⟩ : ∃ e, orderOf (((2 ^ 1 : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  have hq3 : q.card ^ 2 - 1 = 3 := by rw [hq]; norm_num
  have h3eq : ¬ p ∣ 3 := fun h3 => hpq (hq3.symm ▸ h3)
  by_cases hcnt : degCountTw e ≤ 1
  · rw [← he] at hcnt
    exact (RankLE1.of_mulEquiv (eK.symm.trans eX)
      (rankLE1_twistedE6 Nat.prime_two le_rfl K hK σ hσc hp hpq' hcnt)) E hE
  · have h2 : 2 ≤ degCountTw e := by omega
    have h34 : e = 3 ∨ e = 4 := twE6_class hp hp5 h3eq he h2
    have hTCM : CFSG.Blueprint.TwistedChevalleyModel (Cat ⟨.twistedE6 q, hv⟩) TwistTag.E6
        (q.p ^ q.exponent) :=
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq2 (by decide)
        (MulEquiv.refl _)
    have hH0 : CFSG.LieType.BorelTits.Holds (Cat ⟨.twistedE6 q, hv⟩) 2 := by
      have hF2 : Fact (Nat.Prime q.p) := ⟨q.prime_p⟩
      have h := CFSG.LieType.BorelTits.holds_of_twistedChevalleyModel q.exponent_pos hTCM
      rwa [hq2] at h
    haveI : Finite (Cat ⟨.twistedE6 q, hv⟩) :=
      (CFSG.Assembly.lie_finite_simple ⟨.twistedE6 q, hv⟩).1
    have hH : CFSG.LieType.BorelTits.Holds
        (CFSG.LieType.Chevalley.twistedE6RootGroup K σ) 2 := hH0.of_mulEquiv eK
    have hN : NoSylowNormalizesTwo p (CFSG.LieType.Chevalley.twistedE6RootGroup K σ) :=
      noSylowNormalizesTwo_twE6 σ le_rfl hK hσc hH hp hp5 hpq' he h34
    have hNX : NoSylowNormalizesTwo p X :=
      noSylowNormalizesTwo_of_mulEquiv (eK.symm.trans eX).symm hN
    have hp57 : p = 5 ∨ p = 7 := by
      rcases h34 with rfl | rfl
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1
          (by simpa using (CFSG.Timmesfeld.Bang.primitive_of_orderOf he).1))
      · have hdvd : p ∣ 2 ^ (4 : ℕ) - 1 := (CFSG.Timmesfeld.Bang.primitive_of_orderOf he).1
        rcases prime_dvd_fifteen hp (by simpa using hdvd) with h | h
        · subst h
          exact absurd (dvd_refl 3) h3eq
        · exact Or.inl h
    have hcardX : Nat.card X = ordTwistedE6 2 := by
      rw [← Nat.card_congr (eK.symm.trans eX).toEquiv]
      have h := CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 (p := 2) (f := 1)
        Nat.prime_two le_rfl (K := K) hK σ.toRingHom (fun c => by simpa using hσc c)
      simpa [CFSG.LieType.Chevalley.twistedE6RootGroup] using h
    have hfac : (Nat.card X).factorization p ≤ 2 := by
      rw [hcardX]
      have hne : ordTwistedE6 2 ≠ 0 := by norm_num [ordTwistedE6]
      have h3 : ¬ p ^ 3 ∣ ordTwistedE6 2 := by
        rcases hp57 with rfl | rfl <;> norm_num [ordTwistedE6]
      by_contra h
      exact h3 ((hp.pow_dvd_iff_le_factorization hne).2 (by omega))
    haveI : Finite X :=
      Finite.of_equiv (CFSG.LieType.Chevalley.twistedE6RootGroup K σ)
        (eK.symm.trans eX).toEquiv
    exact card_le_of_noSylowNormalizesTwo hp hNX hfac hE hU2 hU hEU

end Aux

theorem t263SelWP_hard2Vac : T263SelWP t263GHard2Vac := by
  refine DXW.t263SelWP_of_innerRank (fun p hp hp2 Ω _ _ S hSn hSq hSp hcat b hbp hInn => ?_)
    (fun p hp hp2 X _ hcat E U hE hU2 hU hEU => ?_)
  · obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d
      case E6 q =>
        obtain ⟨hq, hpq, -, -⟩ : q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 ∧ p ≠ 5 ∧ p ≠ 7 := hi
        have hqp : q.p = 2 :=
          CFSG.HardMathSupport.Timmesfeld.CrossChar.primePower_p_eq_two_of_card_eq_two hq
        have h3 : ¬ (p = 3 ∧ 3 ∣ q.card - 1) := by
          rintro ⟨rfl, h3⟩
          exact hpq (by rw [hq]; norm_num)
        exact inducesInnerMod_e6Inner hp hp2 hSn hSq hSp
          ⟨.lie ⟨.E6 q, hv⟩, ⟨hqp, h3⟩, ⟨e⟩⟩ hbp hInn
      case E7 q =>
        obtain ⟨hq, -, -, -⟩ : q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 ∧ p ≠ 5 ∧ p ≠ 7 := hi
        have hqp : q.p = 2 :=
          CFSG.HardMathSupport.Timmesfeld.CrossChar.primePower_p_eq_two_of_card_eq_two hq
        exact inducesInnerMod_excInner hp hp2 hSn hSq hSp
          ⟨.lie ⟨.E7 q, hv⟩, hqp, ⟨e⟩⟩ hbp hInn
      case E8 q =>
        obtain ⟨hq, -, -, -⟩ : q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 ∧ p ≠ 5 ∧ p ≠ 7 := hi
        have hqp : q.p = 2 :=
          CFSG.HardMathSupport.Timmesfeld.CrossChar.primePower_p_eq_two_of_card_eq_two hq
        exact inducesInnerMod_excInner hp hp2 hSn hSq hSp
          ⟨.lie ⟨.E8 q, hv⟩, hqp, ⟨e⟩⟩ hbp hInn
      case twistedE6 q =>
        obtain ⟨hq, hpq⟩ : q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 := hi
        have hqp : q.p = 2 :=
          CFSG.HardMathSupport.Timmesfeld.CrossChar.primePower_p_eq_two_of_card_eq_two hq
        have h3 : ¬ (p = 3 ∧ 3 ∣ q.card + 1) := by
          rintro ⟨rfl, h3⟩
          exact hpq (by rw [hq]; norm_num)
        exact inducesInnerMod_e6Inner hp hp2 hSn hSq hSp
          ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨hqp, h3⟩, ⟨e⟩⟩ hbp hInn
      all_goals exact False.elim hi
    | cyclic r hr => exact False.elim hi
    | alternating n hn => exact False.elim hi
    | sporadic s => exact False.elim hi
  · obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d
      case E6 q =>
        obtain ⟨hq, hpq, hpne5, hpne7⟩ :
          q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 ∧ p ≠ 5 ∧ p ≠ 7 := hi
        exact e6_card_le hp (five_le_of_card_two hp hp2 hq hpq) hpne5 hpne7 hq hv e.symm
          hE hU2 hU hEU
      case E7 q =>
        obtain ⟨hq, hpq, hpne5, hpne7⟩ :
          q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 ∧ p ≠ 5 ∧ p ≠ 7 := hi
        exact e7_card_le hp (five_le_of_card_two hp hp2 hq hpq) hpne5 hpne7 hq hv e.symm
          hE hU2 hU hEU
      case E8 q =>
        obtain ⟨hq, hpq, hpne5, hpne7⟩ :
          q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 ∧ p ≠ 5 ∧ p ≠ 7 := hi
        exact e8_card_le hp (five_le_of_card_two hp hp2 hq hpq) hpne5 hpne7 hq hv e.symm
          hE hU2 hU hEU
      case twistedE6 q =>
        obtain ⟨hq, hpq⟩ : q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 := hi
        exact twE6_card_le hp (five_le_of_card_two hp hp2 hq hpq) hq hpq hv e.symm
          hE hU2 hU hEU
      all_goals exact False.elim hi
    | cyclic r hr => exact False.elim hi
    | alternating n hn => exact False.elim hi
    | sporadic s => exact False.elim hi

theorem t263SelWP_e6Hard2_of (h : T263SelWP t263GHard2Small) : T263SelWP t263GE6Hard2 := by
  refine T263SelWP.of_cover ?_ t263SelWP_hard2Vac h
  intro p i hi
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;> simp only [t263GE6Hard2, t263GHard2Vac, t263GHard2Small, onLie] at hi ⊢ <;>
      first | exact hi.elim | tauto
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

theorem t263SelWP_excHard2E_of (h : T263SelWP t263GHard2Small) : T263SelWP t263GExcHard2E := by
  refine T263SelWP.of_cover ?_ t263SelWP_hard2Vac h
  intro p i hi
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;> simp only [t263GExcHard2E, t263GHard2Vac, t263GHard2Small, onLie] at hi ⊢ <;>
      first | exact hi.elim | tauto
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

end Vac

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end
