module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRSz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRRee
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FROmegaMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRTD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQRee
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOmegaMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat7

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.Blueprint.Chevalley (Tag)

@[expose] def SubfieldExc {R : Type} [Group R] (p : ℕ) (lab : LargeEvenLabel) (D : Subgroup R) : Prop :=
  (lab.tag = .twB2 ∧ lab.n = p ∧ Group.IsSolvable ↥D) ∨ (lab.tag = .twF4 ∧ lab.n = p)

@[expose] def SubfieldBody (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ _ F =>
  ∀ f ∈ F, orderOf f = p → p ∣ lab.n ∧ ∃ D : Subgroup R, SubfieldGrp f D ∧
    (CFSG.Assembly.LargeEvenRawDatum ⟨lab.tag, lab.rank, lab.n / p⟩ (fun R' _ _ _ => Nonempty (↥D ≃* R')) ∨
      SubfieldExc p lab D)

@[expose] def SubCond (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  InnFree p F → LargeEvenSimpleGuard (SubfieldBody p lab) R I F


section Dispatch



theorem recLinear_sub {rank n : ℕ} (hrank : 1 ≤ rank) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeLinear (rank + 1) (2 ^ n) Q) :
    LargeEvenRecipeLinear (rank + 1) (2 ^ n) (fun R _ I F => Q R I F ∧ SubCond p ⟨.A, rank, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun _ _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_linear (by omega) hn hK hp ∅ f hf hord
  exact ⟨h1, D, h2, Or.inl h3⟩

theorem recUnitary_sub {rank n : ℕ} (hrank : 2 ≤ rank) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : LargeEvenRawCont) (h : LargeEvenRecipeUnitary (rank + 1) (2 ^ n) Q) :
    LargeEvenRecipeUnitary (rank + 1) (2 ^ n)
      (fun R _ I F => Q R I F ∧ SubCond p ⟨.twA, rank, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * n)
    (by rw [hK, ← pow_mul, mul_comm])
  refine ⟨K, hF, hfin, hK, hQ, fun _ _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_unitary (by omega) hn hK hp hp2 ∅ f hf hord
  exact ⟨h1, D, h2, Or.inl h3⟩

theorem recSymplectic_sub {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C) {rank n : ℕ}
    (hrank : 2 ≤ rank) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeSymplectic rank (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic rank (2 ^ n) false
      (fun R _ I F => Q R I F ∧ SubCond p ⟨t, rank, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun _ _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_symplectic (by omega) hn hK hp ∅ f hf hord
  rcases ht with rfl | rfl <;> exact ⟨h1, D, h2, Or.inl h3⟩

theorem recD3_sub {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeLinear 4 (2 ^ n) Q) :
    LargeEvenRecipeLinear 4 (2 ^ n) (fun R _ I F => Q R I F ∧ SubCond p ⟨.D, 3, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun _ _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_linear (d := 4) (by omega) hn hK hp ∅ f hf hord
  exact ⟨h1, D, h2, Or.inl (by simpa [CFSG.Assembly.LargeEvenRawDatum] using h3)⟩

theorem recOmegaPlus_sub {rank n : ℕ} (hrank : 4 ≤ rank) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeOmegaPlus rank (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus rank (2 ^ n)
      (fun R _ I F => Q R I F ∧ SubCond p ⟨.D, rank, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun _ _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_omegaPlus hrank hn hK hp ∅ f hf hord
  refine ⟨h1, D, h2, Or.inl ?_⟩
  simpa [CFSG.Assembly.LargeEvenRawDatum, show rank ≠ 3 by omega] using h3

theorem recTwD2_sub {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeLinear 2 ((2 ^ n) ^ 2) Q) :
    LargeEvenRecipeLinear 2 ((2 ^ n) ^ 2)
      (fun R _ I F => Q R I F ∧ SubCond p ⟨.twD, 2, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  refine ⟨K, hF, hfin, hK, hQ, fun _ _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, ⟨K', hF', hfin', hK'', hQ'⟩⟩ := subBody_linear (d := 2) (by norm_num)
    (m := 2 * n) (by omega) hK' hp ∅ f hf hord
  have hpn : p ∣ n :=
    ((Nat.coprime_primes hp Nat.prime_two).2 hp2).dvd_of_dvd_mul_left h1
  have hdiv : 2 * n / p = 2 * (n / p) := by
    obtain ⟨c, rfl⟩ := hpn
    rw [show 2 * (p * c) = p * (2 * c) by ring, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hp.pos]
  refine ⟨hpn, D, h2, Or.inl ?_⟩
  simp only [CFSG.Assembly.LargeEvenRawDatum, if_true]
  exact ⟨K', hF', hfin', by rw [hK'', hdiv, ← pow_mul, mul_comm], hQ'⟩

theorem recTwD3_sub {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeUnitary 4 (2 ^ n) Q) :
    LargeEvenRecipeUnitary 4 (2 ^ n) (fun R _ I F => Q R I F ∧ SubCond p ⟨.twD, 3, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * n)
    (by rw [hK, ← pow_mul, mul_comm])
  refine ⟨K, hF, hfin, hK, hQ, fun _ _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_unitary (d := 4) (by omega) hn hK hp hp2 ∅ f hf hord
  exact ⟨h1, D, h2, Or.inl (by simpa [CFSG.Assembly.LargeEvenRawDatum] using h3)⟩

theorem recOmegaMinus_sub {rank n : ℕ} (hrank : 4 ≤ rank) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : LargeEvenRawCont) (h : LargeEvenRecipeOmegaMinus (rank - 1) (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus (rank - 1) (2 ^ n)
      (fun R _ I F => Q R I F ∧ SubCond p ⟨.twD, rank, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, b, c, hbc, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, b, c, hbc, hQ, fun hInn _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_omegaMinus hrank hn hK hbc hp hp2 ∅ _ hInn f hf hord
  refine ⟨h1, D, h2, Or.inl ?_⟩
  simpa [CFSG.Assembly.LargeEvenRawDatum, show rank ≠ 2 by omega, show rank ≠ 3 by omega] using h3

theorem recChevalley_sub {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {t : LargeEvenLieTag} {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (Q : LargeEvenRawCont)
    (hdat : ∀ (m : ℕ) (Q' : LargeEvenRawCont), CFSG.Assembly.LargeEvenRawDatum ⟨t, 0, m⟩ Q' ↔
      LargeEvenRecipeChevalley τ.cartan (2 ^ m) false Q')
    (h : LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q) :
    LargeEvenRecipeChevalley τ.cartan (2 ^ n) false
      (fun R _ I F => Q R I F ∧ SubCond p ⟨t, 0, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun _ _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_chevalley hτ hn hK hp ∅ f hf hord
  exact ⟨h1, D, h2, Or.inl ((hdat _ _).2 h3)⟩

theorem recSuzuki_sub {a : ℕ} (ha : 1 ≤ a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a (fun R _ I F => Q R I F ∧ SubCond p ⟨.twB2, 0, 2 * a + 1⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun hInn _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_suzuki ha hK hp hp2 ∅ _ hInn f hf hord
  refine ⟨h1, D, h2, ?_⟩
  rcases h3 with h3 | ⟨h4, h5⟩
  · exact Or.inl h3
  · exact Or.inr (Or.inl ⟨rfl, h4, h5⟩)

theorem recTwF4_sub {a : ℕ} (ha : 1 ≤ a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwF4Inherited a Q) :
    LargeEvenRecipeTwF4Inherited a
      (fun R _ I F => Q R I F ∧ SubCond p ⟨.twF4, 0, 2 * a + 1⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun hInn _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_ree ha hK hp hp2 ∅ _ hInn f hf hord
  refine ⟨h1, D, h2, ?_⟩
  rcases h3 with h3 | h4
  · exact Or.inl h3
  · exact Or.inr (Or.inr ⟨rfl, h4⟩)

theorem recTwE6_sub {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 n Q) :
    LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 n
      (fun R _ I F => Q R I F ∧ SubCond p ⟨.twE6, 0, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun _ _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_twE6 hn hK hp hp2 ∅ f hf hord
  exact ⟨h1, D, h2, Or.inl h3⟩

theorem recTD4_sub {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwisted LargeEvenCartanD4 LargeEvenRhoD4 3 n Q) :
    LargeEvenRecipeTwisted LargeEvenCartanD4 LargeEvenRhoD4 3 n
      (fun R _ I F => Q R I F ∧ SubCond p ⟨.triD4, 0, n⟩ R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, hQ, fun hInn _ _ f hf hord => ?_⟩
  obtain ⟨h1, D, h2, h3⟩ := subBody_td4 hn hK hp hp2 hp3 ∅ _ hInn f hf hord
  exact ⟨h1, D, h2, Or.inl h3⟩

theorem canonSub_derived {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (hd : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) :
    CAll lab (LargeEvenSimpleGuard (SubfieldBody p lab)) := by
  refine (canonFieldDeg hlab).mono ?_
  intro R _ I F h hs hna f hf hord
  exfalso
  have h1 := h f hf
  rw [hord] at h1
  have hfd : fieldDeg lab = 1 := by
    have hn : lab.n = 1 := by
      obtain ⟨t, l, n⟩ := lab
      obtain ⟨-, h2⟩ := hlab
      rcases hd with h3 | h3 | h3 <;> (dsimp only at h3; subst h3; exact h2.2)
    obtain ⟨t, l, n⟩ := lab
    dsimp only at hd hn ⊢
    rcases hd with h3 | h3 | h3 <;> (subst h3; simpa [fieldDeg] using hn)
  rw [hfd] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem canonSubCond {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h3 : ¬ (lab.tag = .triD4 ∧ p = 3)) :
    CAll lab (SubCond p lab) := by
  by_cases hd : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der
  · exact (canonSub_derived hp hlab hd).mono fun R _ I F h _ => h
  intro Q h
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  push Not at hd
  dsimp only at hd h3 hn hl
  cases tag
  case A =>
    obtain ⟨hl1, hl2⟩ := hl
    exact recLinear_sub hl1 hn hp _ h
  case twA =>
    obtain ⟨hl1, hl2⟩ := hl
    exact recUnitary_sub hl1 hn hp hp2 _ h
  case B => exact recSymplectic_sub (Or.inl rfl) (by have := hl.1; omega) hn hp _ h
  case C => exact recSymplectic_sub (Or.inr rfl) (by have := hl.1; omega) hn hp _ h
  case D =>
    dsimp only at hl hn
    unfold CFSG.Assembly.LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with h4
    · subst h4
      exact recD3_sub hn hp _ h
    · exact recOmegaPlus_sub (by omega) hn hp _ h
  case twD =>
    dsimp only at hl hn
    unfold CFSG.Assembly.LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with h2 h3'
    · subst h2
      exact recTwD2_sub hn hp hp2 _ h
    · subst h3'
      exact recTwD3_sub hn hp hp2 _ h
    · exact recOmegaMinus_sub (by omega) hn hp hp2 _ h
  case E6 =>
    obtain rfl := hl
    exact recChevalley_sub (τ := .E6) (Or.inr (Or.inr (Or.inl rfl))) hn hp _
      (fun _ _ => Iff.rfl) h
  case E7 =>
    obtain rfl := hl
    exact recChevalley_sub (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hn hp _
      (fun _ _ => Iff.rfl) h
  case E8 =>
    obtain rfl := hl
    exact recChevalley_sub (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hn hp _
      (fun _ _ => Iff.rfl) h
  case F4 =>
    obtain rfl := hl
    exact recChevalley_sub (τ := .F4) (Or.inr (Or.inl rfl)) hn hp _ (fun _ _ => Iff.rfl) h
  case G2 =>
    obtain ⟨rfl, -⟩ := hl
    exact recChevalley_sub (τ := .G2) (Or.inl rfl) hn hp _ (fun _ _ => Iff.rfl) h
  case twE6 =>
    obtain rfl := hl
    exact recTwE6_sub hn hp hp2 _ h
  case triD4 =>
    obtain rfl := hl
    exact recTD4_sub hn hp hp2 (fun h => h3 ⟨rfl, h⟩) _ h
  case twB2 =>
    obtain ⟨rfl, ⟨k, hk⟩, hn3⟩ := hl
    subst hk
    have e : (2 * k + 1 - 1) / 2 = k := by omega
    unfold CFSG.Assembly.LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    rw [e] at h ⊢
    exact recSuzuki_sub (by omega) hp hp2 _ h
  case twF4 =>
    obtain ⟨rfl, ⟨k, hk⟩, hn3⟩ := hl
    subst hk
    have e : (2 * k + 1 - 1) / 2 = k := by omega
    unfold CFSG.Assembly.LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    have hk0 : (2 * k + 1 - 1) / 2 ≠ 0 := by omega
    rw [e] at h ⊢
    exact recTwF4_sub (by omega) hp hp2 _ h
  case B2der => exact absurd rfl hd.1
  case G2der => exact absurd rfl hd.2.1
  case twF4der => exact absurd rfl hd.2.2

theorem canonSubfield {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h3 : ¬ (lab.tag = .triD4 ∧ p = 3)) :
    CAll lab (LargeEvenSimpleGuard (SubfieldBody p lab)) := by
  have h1 := canonSubCond hp hp2 hlab h3
  have h2 := canonRawInnAny hp.ne_one hlab
  refine (h1.and h2).mono ?_
  rintro R _ I F ⟨hc, hi⟩ hs hna
  refine hc ?_ hs hna
  obtain ⟨-, -, hconj, hF⟩ := hi hs hna
  exact fun f hf hord ⟨r, hr⟩ => hF f hf hord (hr ▸ hconj r)

end Dispatch

end FR

end CFSG.LocalAnalysis.GLTheoremA
