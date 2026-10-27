module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm
open scoped commutatorElement

@[expose] def commTab (tx ty txi tyi : Array ℕ) : Array ℕ :=
  compArr (compArr (compArr tx ty) txi) tyi

@[expose] def commOf (n : ℕ) (L : List (Array ℕ)) (q b : QuotGen) : Array ℕ :=
  commTab (quotGt n L q) (quotGt n L b) (quotGi n L q) (quotGi n L b)

@[expose] def Wit3Ok {Lab : Type} [DecidableEq Lab] (n : ℕ) (act : Array ℕ → Lab → Lab)
    (L : List (Array ℕ)) (lbls : List Lab) (b q₁ q₂ : QuotGen) : Prop :=
  (∀ x ∈ [b, q₁, q₂], (∀ l ∈ x.w, l < L.length) ∧ 0 < x.m) ∧
  b.m = 3 ∧ quotGt n L b ≠ idTab n ∧ powTab n (quotGt n L b) 3 = idTab n ∧
  (∀ q ∈ [q₁, q₂], powTab n (quotGt n L q) q.m = idTab n ∧
      ∀ x ∈ lbls, act (quotGt n L q) x = x) ∧
  (compArr (commOf n L q₁ b) (commOf n L q₂ b) ≠ compArr (commOf n L q₂ b) (commOf n L q₁ b) ∨
    compArr (commOf n L q₁ b) (commOf n L q₁ b) ≠ idTab n)

instance {Lab : Type} [DecidableEq Lab] (n : ℕ) (act : Array ℕ → Lab → Lab)
    (L : List (Array ℕ)) (lbls : List Lab) (b q₁ q₂ : QuotGen) :
    Decidable (Wit3Ok n act L lbls b q₁ q₂) := by
  unfold Wit3Ok; infer_instance

@[expose] def WitPOk {Lab : Type} [DecidableEq Lab] (n : ℕ) (act : Array ℕ → Lab → Lab)
    (L : List (Array ℕ)) (lbls : List Lab) (p : ℕ) (b q : QuotGen) : Prop :=
  (∀ x ∈ [b, q], ∀ l ∈ x.w, l < L.length) ∧
  quotGt n L b ≠ idTab n ∧ powTab n (quotGt n L b) p = idTab n ∧
  (∀ x ∈ lbls, act (quotGt n L q) x = x) ∧
  compArr (quotGt n L q) (quotGt n L b) ≠ compArr (quotGt n L b) (quotGt n L q)

instance {Lab : Type} [DecidableEq Lab] (n : ℕ) (act : Array ℕ → Lab → Lab)
    (L : List (Array ℕ)) (lbls : List Lab) (p : ℕ) (b q : QuotGen) :
    Decidable (WitPOk n act L lbls p b q) := by
  unfold WitPOk; infer_instance

@[expose] def rijTab (n : ℕ) (t₁ t₂ : Array ℕ) (i j : ℕ) : Array ℕ :=
  compArr (powTab n t₁ i) (powTab n t₂ j)

@[expose] def CntOk {Lab : Type} [DecidableEq Lab] (n : ℕ) (act : Array ℕ → Lab → Lab)
    (L : List (Array ℕ)) (lbls : List Lab) (r₁ r₂ : QuotGen) (qs : List QuotGen) : Prop :=
  (∀ l ∈ r₁.w, l < L.length) ∧ (∀ l ∈ r₂.w, l < L.length) ∧
  quotGt n L r₁ ≠ idTab n ∧ quotGt n L r₂ ≠ idTab n ∧
  powTab n (quotGt n L r₁) 3 = idTab n ∧ powTab n (quotGt n L r₂) 3 = idTab n ∧
  compArr (quotGt n L r₁) (quotGt n L r₂) = compArr (quotGt n L r₂) (quotGt n L r₁) ∧
  quotGt n L r₂ ≠ quotGt n L r₁ ∧ quotGt n L r₂ ≠ powTab n (quotGt n L r₁) 2 ∧
  4 < qs.length ∧
  (∀ q ∈ qs, (∀ l ∈ q.w, l < L.length) ∧ 0 < q.m ∧
      powTab n (quotGt n L q) q.m = idTab n ∧ ∀ x ∈ lbls, act (quotGt n L q) x = x) ∧
  ∀ i < 3, ∀ j < 3, (i ≠ 0 ∨ j ≠ 0) →
    (qs.map fun q => commTab (quotGt n L q) (rijTab n (quotGt n L r₁) (quotGt n L r₂) i j)
      (quotGi n L q) (powTab n (rijTab n (quotGt n L r₁) (quotGt n L r₂) i j) 2)).Nodup

instance {Lab : Type} [DecidableEq Lab] (n : ℕ) (act : Array ℕ → Lab → Lab)
    (L : List (Array ℕ)) (lbls : List Lab) (r₁ r₂ : QuotGen) (qs : List QuotGen) :
    Decidable (CntOk n act L lbls r₁ r₂ qs) := by
  unfold CntOk; infer_instance

end CFSG.QuasithinUnique.Vol2Native.L239
