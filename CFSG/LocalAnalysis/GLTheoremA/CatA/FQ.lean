module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQSz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQRee
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQTD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOmega
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOmegaMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMarking
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat7

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.Blueprint.Chevalley (Tag)


theorem canonStOrder_derived {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (hd : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) :
    CAll lab (LargeEvenSimpleGuard (StOrderBody p)) := by
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

@[expose] def StOrderCond (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  InnFree p F → LargeEvenSimpleGuard (StOrderBody p) R I F

section Dispatch

theorem recLinear_stOrder {d N m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) (hN : N = 2 ^ m) {p : ℕ}
    (hp : p.Prime) (Q : LargeEvenRawCont) (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, hQ, fun _ _ _ => stOrderBody_linear hd hm (hK.trans hN) hp _⟩

theorem recUnitary_stOrder {d n : ℕ} (hd : 3 ≤ d) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : LargeEvenRawCont) (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * n)
    (by rw [hK, ← pow_mul, mul_comm])
  exact ⟨K, hF, hfin, hK, hQ, fun _ _ _ => stOrderBody_unitary hd hn hK hp hp2 _⟩

theorem recSymplectic_stOrder {m N n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hN : N = 2 ^ n) {p : ℕ}
    (hp : p.Prime) (Q : LargeEvenRawCont) (h : LargeEvenRecipeSymplectic m N false Q) :
    LargeEvenRecipeSymplectic m N false (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, hQ, fun _ _ _ => stOrderBody_symplectic hm hn (hK.trans hN) hp _⟩

theorem recChevalley_stOrder {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {q n : ℕ} (hn : 1 ≤ n)
    (hq : q = 2 ^ n) {p : ℕ} (hp : p.Prime) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeChevalley τ.cartan q false Q) :
    LargeEvenRecipeChevalley τ.cartan q false (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, hQ, fun _ _ _ => stOrderBody_chevalley hτ hn (hK.trans hq) hp _⟩

theorem recOmegaPlus_stOrder {m n : ℕ} {p : ℕ} (hp : p.Prime) (hm : 4 ≤ m) (hn : 1 ≤ n)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeOmegaPlus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus m (2 ^ n) (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, hQ, fun _ _ _ => stOrderBody_omegaPlus hm hn hK hp _⟩

theorem recOmegaMinus_stOrder {l n : ℕ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hl : 4 ≤ l)
    (hn : 1 ≤ n) (Q : LargeEvenRawCont) (h : LargeEvenRecipeOmegaMinus (l - 1) (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus (l - 1) (2 ^ n) (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, b, c, hbc, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, b, c, hbc, hQ,
    fun hInn _ _ => stOrderBody_omegaMinus hl hn hK hbc hp hp2 _ _ hInn⟩

theorem recSuzuki_stOrder {a : ℕ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, hQ, fun hInn _ _ => stOrderBody_suzuki ha hK hp hp2 _ _ hInn⟩

theorem recTwF4_stOrder {a : ℕ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwF4Inherited a Q) :
    LargeEvenRecipeTwF4Inherited a (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, hQ, fun hInn _ _ => stOrderBody_ree ha hK hp hp2 _ _ hInn⟩

theorem recTwE6_stOrder {n : ℕ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 n Q) :
    LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 n
      (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, hQ, fun _ _ _ => stOrderBody_twE6 hn hK hp hp2 _⟩

theorem recTD4_stOrder {n : ℕ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hn : 1 ≤ n)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwisted LargeEvenCartanD4 LargeEvenRhoD4 3 n Q) :
    LargeEvenRecipeTwisted LargeEvenCartanD4 LargeEvenRhoD4 3 n
      (fun R _ I F => Q R I F ∧ StOrderCond p R I F) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, hQ, fun hInn _ _ => stOrderBody_td4 hn hK hp hp2 hp3 _ _ hInn⟩

theorem canonStOrderCond {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h3 : ¬ (lab.tag = .triD4 ∧ p = 3)) :
    CAll lab (StOrderCond p) := by
  by_cases hd : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der
  · exact (canonStOrder_derived hp hlab hd).mono fun R _ I F h _ => h
  intro Q h
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  push Not at hd
  dsimp only at hd h3
  cases tag
  case A =>
    obtain ⟨hl1, hl2⟩ := hl
    exact recLinear_stOrder (by omega) hn rfl hp _ h
  case twA =>
    obtain ⟨hl1, hl2⟩ := hl
    exact recUnitary_stOrder (by omega) hn hp hp2 _ h
  case B => exact recSymplectic_stOrder (by have := hl.1; omega) hn rfl hp _ h
  case C => exact recSymplectic_stOrder (by have := hl.1; omega) hn rfl hp _ h
  case D =>
    dsimp only at hl hn
    unfold CFSG.Assembly.LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with h4
    · exact recLinear_stOrder (by omega) hn rfl hp _ h
    · exact recOmegaPlus_stOrder hp (by omega) hn _ h
  case twD =>
    dsimp only at hl hn
    unfold CFSG.Assembly.LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with h2 h3'
    · exact recLinear_stOrder (m := 2 * n) (by omega) (by omega) (by rw [← pow_mul, mul_comm])
        hp _ h
    · exact recUnitary_stOrder (by omega) hn hp hp2 _ h
    · exact recOmegaMinus_stOrder (l := rank) hp hp2 (by omega) hn _ h
  case E6 => exact recChevalley_stOrder (τ := .E6) (Or.inr (Or.inr (Or.inl rfl))) hn rfl hp _ h
  case E7 =>
    exact recChevalley_stOrder (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hn rfl hp _ h
  case E8 =>
    exact recChevalley_stOrder (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hn rfl hp _ h
  case F4 => exact recChevalley_stOrder (τ := .F4) (Or.inr (Or.inl rfl)) hn rfl hp _ h
  case G2 => exact recChevalley_stOrder (τ := .G2) (Or.inl rfl) hn rfl hp _ h
  case twE6 => exact recTwE6_stOrder hp hp2 hn _ h
  case triD4 => exact recTD4_stOrder hp hp2 (fun h => h3 ⟨rfl, h⟩) hn _ h
  case twB2 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    exact recSuzuki_stOrder hp hp2 (by omega) _ h
  case twF4 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    exact recTwF4_stOrder hp hp2 (by omega) _ h
  case B2der => exact absurd rfl hd.1
  case G2der => exact absurd rfl hd.2.1
  case twF4der => exact absurd rfl hd.2.2

theorem s10StOrderAt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    _root_.CFSG.LocalAnalysis.GLTheoremA.S10StOrderAt p := by
  intro lab hlab h3
  have h1 := canonStOrderCond hp hp2 hlab h3
  have h2 := canonRawInnAny hp.ne_one hlab
  refine (h1.and h2).mono ?_
  rintro R _ I F ⟨hc, hi⟩ hs hna
  refine hc ?_ hs hna
  obtain ⟨-, -, hconj, hF⟩ := hi hs hna
  exact fun f hf hord ⟨r, hr⟩ => hF f hf hord (hr ▸ hconj r)

end Dispatch

end FQ

end CFSG.LocalAnalysis.GLTheoremA
