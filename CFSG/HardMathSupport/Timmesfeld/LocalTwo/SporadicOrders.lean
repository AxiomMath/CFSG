module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Timmesfeld.Tables.Census

@[expose] def SporadicTwoPair (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (p = 7 ∧ name ∈ ({.He, .ONan, .Fi24Prime, .Co1, .Th, .B, .M} : Finset TauCeti.SporadicName)) ∨
  (p = 11 ∧ name ∈ ({.J4, .M} : Finset TauCeti.SporadicName)) ∨ (p = 13 ∧ name = .M)

instance (name : TauCeti.SporadicName) (p : ℕ) : Decidable (SporadicTwoPair name p) := by
  unfold SporadicTwoPair
  infer_instance

@[expose] def SporadicTwoOrders : Prop :=
  ∀ (name : TauCeti.SporadicName) (p : ℕ), p.Prime → 5 < p →
    p ^ 2 ∣ Nat.card (NativeSporadic.Carrier name) → SporadicTwoPair name p

theorem sqdvd_two_of {name : TauCeti.SporadicName} {n : ℕ} (hn : n ≠ 0) (L : Finset ℕ)
    (hL : n.primeFactors = L)
    (hcase : ∀ q ∈ L, 5 < q → q ^ 2 ∣ n → SporadicTwoPair name q) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 < p) (h : p ^ 2 ∣ n) : SporadicTwoPair name p := by
  have hmem : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, hn⟩
  rw [hL] at hmem
  exact hcase p hmem hp5 h

theorem sqdvd_two_M11 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 7920) :
    SporadicTwoPair .M11 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 11} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_M12 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 95040) :
    SporadicTwoPair .M12 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 11} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_M22 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 443520) :
    SporadicTwoPair .M22 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_M23 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 10200960) :
    SporadicTwoPair .M23 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 23} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_M24 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 244823040) :
    SporadicTwoPair .M24 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 23} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_J1 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 175560) :
    SporadicTwoPair .J1 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 19} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_J2 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 604800) :
    SporadicTwoPair .J2 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_J3 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 50232960) :
    SporadicTwoPair .J3 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 17, 19} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_J4 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 86775571046077562880) :
    SporadicTwoPair .J4 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_HS {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 44352000) :
    SporadicTwoPair .HS p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_McL {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 898128000) :
    SporadicTwoPair .McL p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_He {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 4030387200) :
    SporadicTwoPair .He p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 17} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Ru {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 145926144000) :
    SporadicTwoPair .Ru p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 13, 29} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Suz {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 448345497600) :
    SporadicTwoPair .Suz p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 13} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_ONan {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 460815505920) :
    SporadicTwoPair .ONan p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 19, 31} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Co1 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 4157776806543360000) :
    SporadicTwoPair .Co1 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 13, 23} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Co2 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 42305421312000) :
    SporadicTwoPair .Co2 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 23} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Co3 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 495766656000) :
    SporadicTwoPair .Co3 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 23} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Fi22 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 64561751654400) :
    SporadicTwoPair .Fi22 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 13} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Fi23 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 4089470473293004800) :
    SporadicTwoPair .Fi23 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 13, 17, 23} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Fi24Prime {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 1255205709190661721292800) :
    SporadicTwoPair .Fi24Prime p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 13, 17, 23, 29} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_HN {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 273030912000000) :
    SporadicTwoPair .HN p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 19} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Ly {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 51765179004000000) :
    SporadicTwoPair .Ly p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 31, 37, 67} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_Th {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 90745943887872000) :
    SporadicTwoPair .Th p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 13, 19, 31} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_B {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 4154781481226426191177580544000000) :
    SporadicTwoPair .B p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 47} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

theorem sqdvd_two_M {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ monsterOrder) :
    SporadicTwoPair .M p :=
  sqdvd_two_of (by norm_num [monsterOrder])
    {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}
    (by norm_num [monsterOrder, Nat.primeFactors, Nat.primeFactorsList])
    (by simp only [monsterOrder]; decide) hp hp5 h

theorem sporadicTwoPair_of_sq_dvd
    (hBM : SporadicBMData) : SporadicTwoOrders := by
  intro name p hp hp5 h
  cases name with
  | M11 => exact sqdvd_two_M11 hp hp5 (by rw [← CFSG.Sporadic.Mathieu.card_M11]; exact h)
  | M12 => exact sqdvd_two_M12 hp hp5 (by rw [← CFSG.Sporadic.Mathieu.card_M12]; exact h)
  | M22 => exact sqdvd_two_M22 hp hp5 (by rw [← CFSG.Sporadic.Mathieu.card_M22]; exact h)
  | M23 => exact sqdvd_two_M23 hp hp5 (by rw [← CFSG.Sporadic.Schreier.m23_card]; exact h)
  | M24 => exact sqdvd_two_M24 hp hp5 (by rw [← CFSG.Sporadic.Mathieu.card_M24]; exact h)
  | J1 => exact sqdvd_two_J1 hp hp5 (by rw [← CFSG.Sporadic.J1.card_J1]; exact h)
  | J2 => exact sqdvd_two_J2 hp hp5 (by rw [← CFSG.Sporadic.J2.card_J2]; exact h)
  | J3 => exact sqdvd_two_J3 hp hp5 (by rw [← CFSG.Sporadic.J3.card_J3]; exact h)
  | J4 => exact sqdvd_two_J4 hp hp5 (by rw [← CFSG.Sporadic.J4.card_J4]; exact h)
  | HS => exact sqdvd_two_HS hp hp5 (by rw [← CFSG.Sporadic.HS.card_HS]; exact h)
  | McL => exact sqdvd_two_McL hp hp5 (by rw [← CFSG.Sporadic.McL.card_McL]; exact h)
  | He => exact sqdvd_two_He hp hp5 (by rw [← CFSG.Sporadic.He.card_He]; exact h)
  | Ru => exact sqdvd_two_Ru hp hp5 (by rw [← CFSG.Sporadic.Ru.card_Ru]; exact h)
  | Suz => exact sqdvd_two_Suz hp hp5 (by rw [← CFSG.Sporadic.Suz.card_Suz]; exact h)
  | ONan => exact sqdvd_two_ONan hp hp5 (by rw [← CFSG.Sporadic.ON.card_ON]; exact h)
  | Co1 => exact sqdvd_two_Co1 hp hp5 (by rw [← CFSG.Sporadic.Co1.card_Co1]; exact h)
  | Co2 => exact sqdvd_two_Co2 hp hp5 (by rw [← CFSG.Sporadic.Co2.card_Co2]; exact h)
  | Co3 => exact sqdvd_two_Co3 hp hp5 (by rw [← CFSG.Sporadic.Co3.card_Co3]; exact h)
  | Fi22 => exact sqdvd_two_Fi22 hp hp5 (by rw [← CFSG.Sporadic.Fi22.card_Fi22]; exact h)
  | Fi23 => exact sqdvd_two_Fi23 hp hp5 (by rw [← CFSG.Sporadic.Fi23.card_Fi23]; exact h)
  | Fi24Prime => exact sqdvd_two_Fi24Prime hp hp5 (by rw [← CFSG.Sporadic.Fi24.card_Fi24prime]; exact h)
  | HN => exact sqdvd_two_HN hp hp5 (by rw [← CFSG.Sporadic.HN.card_HN]; exact h)
  | Ly => exact sqdvd_two_Ly hp hp5 (by rw [← CFSG.Sporadic.Ly.card_Ly']; exact h)
  | Th => exact sqdvd_two_Th hp hp5 (by rw [← CFSG.RankThree.PartOne.CTP.card_Th]; exact h)
  | B => exact sqdvd_two_B hp hp5 (by rw [← hBM.1]; exact h)
  | M => exact sqdvd_two_M hp hp5 (by rw [← hBM.2.1]; exact h)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
