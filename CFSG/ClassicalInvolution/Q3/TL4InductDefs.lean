module

public import CFSG.ClassicalInvolution.Q3.TL4SepDefs
public import CFSG.ClassicalInvolution.Q3.TL3T20
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def ThmD1RBelow (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ Δ : Set (Subgroup G), T4Hyp r G Δ →
    (∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → TightInO2 z) →
    ∀ J ∈ Δ, ∀ L ∈ Δ, (¬ ∃ g : G, conjSub g J = L) → Commutes J L

structure ThmDGenRBelow (r n : ℕ) : Prop where
  d1 : ThmD1RBelow r n
  d2 : TC.Thin.ThmDAbsBelow r n

theorem thmDAbs_of_below {r : ℕ} (h : ∀ n, ThmDGenRBelow r n) : TC.Thin.ThmDAbs r :=
  fun G _ _ => (h (Nat.card G + 1)).d2 G (Nat.lt_succ_self _)

theorem thmDGenBelow_of_gen {r n : ℕ} (h : ThmDGenRBelow r n) : TC.Thin.ThmDGenBelow r n :=
  TC.Thin.thmDGenBelow_of_absBelow h.d2

theorem thmD1RBelow_of_gen {r n : ℕ} (h : ThmDGenRBelow r n) : ThmD1RBelow r n :=
  h.d1

abbrev FStarQuot (Y : Type) [Group Y] : Type :=
  ↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y)

@[expose] def Thm6Exit (Y : Type) [Group Y] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((Even f ∧ CFSG.Blueprint.LieModel (FStarQuot Y) .PSL 2 p f ∧
          (genFittingFStar Y).index ≤ 2) ∨
        ((CFSG.Blueprint.LieModel (FStarQuot Y) .PSL 3 p f ∨
            CFSG.Blueprint.LieModel (FStarQuot Y) .PSU 3 p f) ∧
          (genFittingFStar Y).index ∣ 6))) ∨
    (CFSG.Blueprint.NativeSporadic.IsSporadic (FStarQuot Y) .M12 ∧ (genFittingFStar Y).index ≤ 2)

@[expose] def Thm6RBelow (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightClsR r Y R S t → ¬ TightInO2 t → TightFStarQuasisimple Y →
      TightEdgeless R → GoodThreeElement R t ∨ Thm6Exit Y

@[expose] def Thm8RBelow (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ →
    (∀ L ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g L = M) →
    IsSimpleGroup ↥(genFittingFStar X) → (∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) →
    ¬ Disconnected.DEdgeless Φ → Disconnected.DConnected Φ

@[expose] def Thm5RBelow (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → (∀ L ∈ Φ, AEmpty Φ L) →
    ∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, ∀ z t : X, IsUniqueInvolution K z → IsUniqueInvolution J t →
      alphaOf (Subgroup.closure ({z, t} : Set X)) = ⊥

@[expose] def Thm5RBelowF (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → IsSimpleGroup ↥(genFittingFStar X) →
    (∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) →
    (∀ L ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g L = M) →
    ∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, ∀ z t : X, IsUniqueInvolution K z → IsUniqueInvolution J t →
      alphaOf (Subgroup.closure ({z, t} : Set X)) = ⊥

structure TightBelowRPlus (r n : ℕ) : Prop where
  tbelow : TightBelowR r n
  thmD : ThmDGenRBelow r n
  thm6 : Thm6RBelow r n
  thm5 : Thm5RBelowF r n
  twin : r = 3 → PhilipHall.Frame.Thm1RTwinLiftSetEBelow n

namespace Induct

variable {r m n : ℕ}

theorem tightBelowR_mono (hmn : m ≤ n) (h : TightBelowR r n) : TightBelowR r m :=
  fun Y _ _ hY => h Y (lt_of_lt_of_le hY hmn)

theorem thmDGenRBelow_mono (hmn : m ≤ n) (h : ThmDGenRBelow r n) : ThmDGenRBelow r m where
  d1 := fun G _ _ hG => h.d1 G (lt_of_lt_of_le hG hmn)
  d2 := fun G _ _ hG => h.d2 G (lt_of_lt_of_le hG hmn)

theorem thm6RBelow_mono (hmn : m ≤ n) (h : Thm6RBelow r n) : Thm6RBelow r m :=
  fun Y _ _ hY => h Y (lt_of_lt_of_le hY hmn)

theorem thm5RBelow_mono (hmn : m ≤ n) (h : Thm5RBelow r n) : Thm5RBelow r m :=
  fun X _ _ hX => h X (lt_of_lt_of_le hX hmn)

theorem thm8RBelow_mono (hmn : m ≤ n) (h : Thm8RBelow r n) : Thm8RBelow r m :=
  fun X _ _ hX => h X (lt_of_lt_of_le hX hmn)

theorem thm5RBelowF_mono (hmn : m ≤ n) (h : Thm5RBelowF r n) : Thm5RBelowF r m :=
  fun X _ _ hX => h X (lt_of_lt_of_le hX hmn)

end Induct

theorem TightBelowRPlus.mono {r m n : ℕ} (hmn : m ≤ n) (h : TightBelowRPlus r n) :
    TightBelowRPlus r m where
  tbelow := Induct.tightBelowR_mono hmn h.tbelow
  thmD := Induct.thmDGenRBelow_mono hmn h.thmD
  thm6 := Induct.thm6RBelow_mono hmn h.thm6
  thm5 := Induct.thm5RBelowF_mono hmn h.thm5
  twin := fun h3 => (h.twin h3).mono hmn

theorem TightBelowRPlus.zero (r : ℕ) : TightBelowRPlus r 0 where
  tbelow := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  thmD := ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _),
    fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  thm6 := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  thm5 := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  twin := fun _ => PhilipHall.Frame.thm1RTwinLiftSetEBelow_zero

theorem tightBelowR_of_plus {r n : ℕ} (h : TightBelowRPlus r n) : TightBelowR r n :=
  h.tbelow

theorem tightBelow_of_plus {n : ℕ} (h : TightBelowRPlus 3 n) : TightBelow n :=
  tightBelowR_three_iff.mp h.tbelow

section Cit3


@[expose] def TightPlusStep (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus r n → TightBelowRPlus r (n + 1)

theorem tightBelowRPlus_of_step {r : ℕ} (h : ∀ n, TightPlusStep r n) :
    ∀ n, CIT3Below n → TightBelowRPlus r n := by
  intro n
  induction n with
  | zero => exact fun _ => TightBelowRPlus.zero r
  | succ k ih =>
    intro hA
    have hA' : CIT3Below k := fun Y _ _ hY => hA Y (Nat.lt_succ_of_lt hY)
    exact h k hA' (ih hA')

theorem tightInductive_of_plus (h : ∀ n, CIT3Below n → TightBelowRPlus 3 n) (N : ℕ) :
    TightInductive N :=
  fun hA => tightBelow_of_plus (h N hA)

theorem thmD_step {r n : ℕ}
    (h2 : CIT3Below n → TightBelowRPlus r n → TC.Thin.ThmDAbsBelow r (n + 1))
    (h1 : CIT3Below n → TightBelowRPlus r n → TC.Thin.ThmDAbsBelow r (n + 1) →
      ThmD1RBelow r (n + 1)) :
    CIT3Below n → TightBelowRPlus r n → ThmDGenRBelow r (n + 1) :=
  fun hA hP => ⟨h1 hA hP (h2 hA hP), h2 hA hP⟩

theorem tightBelowR_succ_of_tightStep {n : ℕ} (hS : TightStep n) (hA : CIT3Below n)
    (h : TightBelowRPlus 3 n) : TightBelowR 3 (n + 1) := by
  intro Y _ _ hY R S t hd hc
  rcases (Nat.lt_succ_iff.mp hY).lt_or_eq with hlt | heq
  · exact h.tbelow Y hlt R S t hd hc
  · exact hS hA (tightBelow_of_plus h) Y heq R S t hd hc

theorem twinLift_of_steps (h : ∀ n, TightPlusStep 3 n) :
    ∀ n, CIT3Below n → TightBelow n → PhilipHall.Frame.Thm1RTwinLiftSetEBelow (n + 1) :=
  fun n hA _ => (h n hA (tightBelowRPlus_of_step h n hA)).twin rfl

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
