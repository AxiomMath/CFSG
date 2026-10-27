module

public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

@[expose] noncomputable def rk2Ord (p n : ℕ) : ℕ := orderOf ((2 : ZMod p) ^ n)

@[expose] def rk2Cnt (fs : List (ℕ × Bool)) (m : ℕ) : ℕ :=
  fs.countP fun f => if f.2 then decide (m ∣ f.1) else decide (m ∣ 2 * f.1 ∧ ¬ m ∣ f.1)

@[expose] def rk2Mult (lab : GLALabel) (m : ℕ) : ℕ :=
  match lab.tag with
  | .A => if m = 1 then lab.rank else (lab.rank + 1) / m
  | .twA =>
    if m = 2 then lab.rank
    else if m % 4 = 2 then 2 * (lab.rank + 1) / m
    else if m % 2 = 1 then (lab.rank + 1) / (2 * m)
    else (lab.rank + 1) / m
  | .B => if m % 2 = 0 then 2 * lab.rank / m else lab.rank / m
  | .C => if m % 2 = 0 then 2 * lab.rank / m else lab.rank / m
  | .D =>
    if m % 2 = 0 then (if m ∣ 2 * lab.rank ∧ ¬ m ∣ lab.rank then 2 * lab.rank / m - 1 else 2 * lab.rank / m)
    else lab.rank / m
  | .twD =>
    (if m % 2 = 0 then 2 * lab.rank / m else lab.rank / m) - (if m ∣ lab.rank then 1 else 0)
  | .E6 => rk2Cnt [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)] m
  | .E7 => rk2Cnt [(2, true), (6, true), (8, true), (10, true), (12, true), (14, true), (18, true)] m
  | .E8 => rk2Cnt [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true), (30, true)] m
  | .F4 => rk2Cnt [(2, true), (6, true), (8, true), (12, true)] m
  | .twE6 => rk2Cnt [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)] m
  | .triD4 => rk2Cnt [(2, true), (6, true), (12, true)] m - rk2Cnt [(4, true)] m
  | .G2 => rk2Cnt [(2, true), (6, true)] m
  | .twB2 => rk2Cnt [(1, true), (2, false)] m
  | .twF4 => rk2Cnt [(1, true), (3, false), (4, true), (6, false)] m
  | .B2der => if m % 2 = 0 then 4 / m else 2 / m
  | .G2der => rk2Cnt [(2, true), (6, true)] m
  | .twF4der => rk2Cnt [(1, true), (3, false), (4, true), (6, false)] m

@[expose] def rk2LieRank (lab : GLALabel) : ℕ :=
  match lab.tag with
  | .B => lab.rank
  | .D => lab.rank
  | .F4 => 4
  | .E7 => 7
  | .E8 => 8
  | _ => 0

@[expose] def rk2SmallTag (lab : GLALabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
    lab.tag = .G2der ∨ lab.tag = .twF4der

structure Rk2ELowAt (lab : GLALabel) (c : Prop) (e : ℕ) : Prop where
  bcd_ge : (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) → 2 ≤ lab.n → lab.rank ≤ e
  bcd_one : (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) → lab.n = 1 → lab.rank - 1 ≤ e
  f4 : lab.tag = .F4 → 2 ≤ lab.n → 4 ≤ e
  e7 : lab.tag = .E7 → 2 ≤ lab.n → 7 ≤ e
  e7_one : lab.tag = .E7 → lab.n = 1 → 6 ≤ e
  e8 : lab.tag = .E8 → 2 ≤ lab.n → 8 ≤ e
  e8_one : lab.tag = .E8 → lab.n = 1 → 7 ≤ e
  e6_one : lab.tag = .E6 → lab.n = 1 → 4 ≤ e
  e6_two : lab.tag = .E6 → 2 ≤ lab.n → 5 ≤ e
  e6_big : lab.tag = .E6 → (3 ≤ lab.n ∨ (lab.n = 2 ∧ ¬ c)) → 6 ≤ e
  a_ge : lab.tag = .A → 2 ≤ lab.n → lab.rank - 1 ≤ e
  a_five : (lab.tag = .A ∧ lab.rank = 5 ∧ 2 ≤ lab.n) → (3 ≤ lab.n ∨ ¬ c) → 5 ≤ e
  a_one : lab.tag = .A → lab.n = 1 → (lab.rank + 1) / 2 ≤ e
  twa_two : lab.tag = .twA → lab.rank - 2 ≤ e
  twa_one : lab.tag = .twA → ¬ (2 ^ lab.n + 1 ∣ lab.rank + 1) → lab.rank - 1 ≤ e
  twd : lab.tag = .twD → lab.rank - 1 ≤ e
  twe6_one : lab.tag = .twE6 → lab.n = 1 → 4 ≤ e
  twe6 : lab.tag = .twE6 → 2 ≤ lab.n → 5 ≤ e

structure Rk2EUpAt (lab : GLALabel) (c : Prop) (e : ℕ) : Prop where
  bd : (lab.tag = .B ∨ lab.tag = .D) → 2 ≤ lab.n → e ≤ lab.rank
  f4 : lab.tag = .F4 → 2 ≤ lab.n → e ≤ 4
  e7 : lab.tag = .E7 → 2 ≤ lab.n → e ≤ 7
  e8 : lab.tag = .E8 → 2 ≤ lab.n → e ≤ 8
  a5 : lab = ⟨.A, 5, 2⟩ → c → e ≤ 4
  e6_two : lab = ⟨.E6, 0, 2⟩ → c → e ≤ 5
  a8 : lab = ⟨.A, 8, 1⟩ → e ≤ 4
  e6_one : lab = ⟨.E6, 0, 1⟩ → e ≤ 4
  twa5 : (lab.tag = .twA ∧ lab.rank = 5) → 2 ≤ lab.n → c → e ≤ 4
  twe6 : lab.tag = .twE6 → 2 ≤ lab.n → c → e ≤ 5

@[expose] def Rk2IsLabel (K : Type) [Group K] (lab : GLALabel) : Prop :=
  GLAMarking K fun lab' _ _ _ _ _ => lab' = lab

@[expose] def Rk2LabelAll (lab : GLALabel) (P : CFSG.Assembly.LargeEvenRawCont) : Prop :=
  ∀ Q : CFSG.Assembly.LargeEvenRawCont, GLARawDatum lab Q → GLARawDatum lab fun R _ I F => Q R I F ∧ P R I F

@[expose] def Rk2InnRankOn (S : GLALabel → Prop) : Prop :=
  ∀ (lab : GLALabel), GLAInLambda2 lab → S lab → ∀ p : ℕ, p.Prime → p ≠ 2 →
    Rk2LabelAll lab fun R [Group R] I _ => IsSimpleGroup R →
      ∀ E : Subgroup (MulAut R), E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) →
        IsElemAbelian p E → Nat.card E ≤ p ^ rk2Mult lab (rk2Ord p lab.n)

@[expose] def Rk2InnRank : Prop := Rk2InnRankOn fun _ => True

@[expose] def Rk2KRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab → p.Prime → p ≠ 2 →
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n)

@[expose] def Rk2Lower : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel), Rk2IsLabel K lab →
    Rk2ELowAt lab (Subgroup.center K = ⊥) (evenRank K)

@[expose] def Rk2Upper : Prop :=
  (∀ (K : Type) [Group K] [Finite K] (lab : GLALabel), Rk2IsLabel K lab →
    (lab = ⟨.A, 5, 2⟩ → Subgroup.center K = ⊥ → evenRank K ≤ 4) ∧
    (lab = ⟨.E6, 0, 2⟩ → Subgroup.center K = ⊥ → evenRank K ≤ 5) ∧
    ((lab.tag = .twA ∧ lab.rank = 5) → 2 ≤ lab.n → Subgroup.center K = ⊥ → evenRank K ≤ 4) ∧
    (lab.tag = .twE6 → 2 ≤ lab.n → Subgroup.center K = ⊥ → evenRank K ≤ 5)) ∧
  (∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab → p.Prime → p ≠ 2 →
    (lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) → 2 ≤ lab.n →
      p ∣ 2 ^ lab.n + 1 → GLATwoLocalRank p K < rk2LieRank lab)

@[expose] def Rk2Split : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab → p.Prime → p ≠ 2 →
    GLASplit16 p lab → 5 ≤ evenRank K →
      evenRank K + CFSG.Open.pRank p (Subgroup.center K) ≤ GLATwoLocalRank p K + 1

structure Rk2Tables : Prop where
  inn : Rk2InnRank
  kRank : Rk2KRank
  lower : Rk2Lower
  upper : Rk2Upper
  split : Rk2Split

end CFSG.LocalAnalysis.GLTheoremA
