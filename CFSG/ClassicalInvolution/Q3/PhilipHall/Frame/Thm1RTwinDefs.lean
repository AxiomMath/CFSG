module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Q8Twin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

@[expose] def CentOmega3 (Y : Type) [Group Y] : Prop :=
  let M := Y ⧸ Subgroup.center Y
  CFSG.Blueprint.LieModel M .PSp 2 3 1 ∨ CFSG.Blueprint.LieModel M .PSL 4 3 1 ∨
    CFSG.Blueprint.LieModel M .PSU 4 3 1 ∨
    (∃ k, 3 ≤ k ∧ CFSG.Blueprint.LieModel M .POmegaOdd k 3 1) ∨
    (∃ k, 4 ≤ k ∧ CFSG.Blueprint.LieModel M .POmegaPlus k 3 1) ∨
    (∃ k, 4 ≤ k ∧ CFSG.Blueprint.LieModel M .POmegaMinus k 3 1)

@[expose] def TwinE4 (Y : Type) [Group Y] : Prop :=
  ∃ (Q : Type) (_ : Group Q) (f : Y →* Q), Function.Surjective f ∧ IsPGroup 2 ↥f.ker ∧
    (CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1)

@[expose] def LongFundPair3 {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∀ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R →
    ∃ L L' : Subgroup Y, tightCore R ≤ L ∧ K' ≤ L' ∧ IsClassicalMember3 L t ∧
      IsClassicalMember3 L' t ∧ (∀ x ∈ L, ∀ y ∈ L', x * y = y * x) ∧
      ((L ⊔ L').subgroupOf (Subgroup.centralizer ({t} : Set Y))).Normal

@[expose] def Thm1RTwinBelow (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), QuaternionBridge.Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R → TightOddFree Y →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) →
      TightInO2 t ∨ TwinE4 Y ∨ (CentOmega3 Y ∧ LongFundPair3 R t)

theorem Thm1RTwinBelow.mono {m n : ℕ} (h : m ≤ n) (H : Thm1RTwinBelow n) : Thm1RTwinBelow m :=
  fun Y _ _ hlt => H Y (lt_of_lt_of_le hlt h)

theorem thm1RTwinBelow_zero : Thm1RTwinBelow 0 :=
  fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)

@[expose] def Thm1RTwinLiftBelow (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), QuaternionBridge.Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R → TightOddFree Y →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) →
      TightInO2 t ∨ TwinE4 Y ∨ LongFundPair3 R t

theorem Thm1RTwinLiftBelow.mono {m n : ℕ} (h : m ≤ n) (H : Thm1RTwinLiftBelow n) :
    Thm1RTwinLiftBelow m :=
  fun Y _ _ hlt => H Y (lt_of_lt_of_le hlt h)

theorem thm1RTwinLiftBelow_zero : Thm1RTwinLiftBelow 0 :=
  fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)

theorem Thm1RTwinBelow.lift {n : ℕ} (H : Thm1RTwinBelow n) : Thm1RTwinLiftBelow n := by
  intro Y _ _ hlt R S t hd hq hg hO hΩ hA htw
  rcases H Y hlt R S t hd hq hg hO hΩ hA htw with h | h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem LongFundPair3.hasLift {Y : Type} [Group Y] {R : Subgroup Y} {t : Y}
    (h : LongFundPair3 R t)
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R) :
    TightHasLift R t := by
  obtain ⟨K', hK', hne⟩ := htw
  obtain ⟨L, -, hL, -, hLm, -⟩ := h K' hK' hne
  exact ⟨L, hL, hLm⟩

theorem TightE4.twinE4 {Y : Type} [Group Y] (h : TightE4 Y) : TwinE4 Y := by
  obtain ⟨Q, _, f, hfs, hf2, -, hQ⟩ := h
  exact ⟨Q, inferInstance, f, hfs, hf2, hQ⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
