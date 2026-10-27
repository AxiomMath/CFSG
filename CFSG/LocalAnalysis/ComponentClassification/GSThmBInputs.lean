module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Open.AschbacherComponentTypeTheorem5MilestoneDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def GSRestricted (Y : Type) [Group Y] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel Y .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (Blueprint.LieModel Y .PSL 2 p (2 * f) ∨ Blueprint.LieModel Y .PSL 3 p f ∨
        Blueprint.LieModel Y .PSU 3 p f ∨ Blueprint.LieModel Y .PSL 4 p f ∨
        Blueprint.LieModel Y .PSU 4 p f ∨ Blueprint.LieModel Y .PSp 2 p f ∨
        Blueprint.LieModel Y .POmegaMinus 4 p f)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Blueprint.LieModel Y .twistedG2 0 3 (2 * m + 1)) ∨
    Blueprint.LieModel Y .PSL 2 2 4 ∨ Blueprint.LieModel Y .PSL 3 2 2 ∨
    Blueprint.LieModel Y .PSU 3 2 2 ∨ Blueprint.LieModel Y .PSp 2 2 2 ∨
    Blueprint.LieModel Y .PSL 5 2 1 ∨ Blueprint.LieModel Y .PSU 5 2 1 ∨
    Blueprint.LieModel Y .PSL 3 2 4 ∨
    (∃ n : ℕ, 7 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
    Blueprint.NativeSporadic.IsSporadic Y .J1 ∨ Blueprint.NativeSporadic.IsSporadic Y .J2 ∨
    Blueprint.NativeSporadic.IsSporadic Y .J3 ∨ Blueprint.NativeSporadic.IsSporadic Y .M12 ∨
    Blueprint.NativeSporadic.IsSporadic Y .HS ∨ Blueprint.NativeSporadic.IsSporadic Y .He ∨
    Blueprint.NativeSporadic.IsSporadic Y .ONan ∨ Blueprint.NativeSporadic.IsSporadic Y .Suz

@[expose] def RestrictedStandardInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H → pPrimeCore 2 H = ⊥ →
    ∀ J : Subgroup H, IsStandardSubgroup J → ¬ J.Normal →
      ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
        Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
        Blueprint.LieModel (J ⧸ center J) .PSL 3 2 2) →
      ∀ K : Subgroup H, IsComponent K → GSRestricted (K ⧸ center K)

@[expose] def Solomon2AnInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], ∀ z : G, orderOf z = 2 →
    ∀ (L : Subgroup G) (n : ℕ), 8 ≤ n → L ≤ centralizer ({z} : Set G) →
      IsPComponent 2 (L.subgroupOf (centralizer ({z} : Set G))) → z ∈ L →
      Group.IsPerfect (L ⧸ pPrimeCore 2 L) → Nat.card (center (L ⧸ pPrimeCore 2 L)) = 2 →
      Nonempty ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L) ≃*
        alternatingGroup (Fin n)) →
      Nonempty (G ≃* Blueprint.NativeSporadic.McL) ∨ Nonempty (G ≃* Blueprint.NativeSporadic.Ly)

@[expose] def L34StandardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ∀ L : Subgroup G, IsStandardSubgroup L →
      Blueprint.LieModel (L ⧸ center L) .PSL 3 2 2 →
      Nonempty (G ≃* Blueprint.NativeSporadic.Suz) ∨
        Nonempty (G ≃* Blueprint.NativeSporadic.He) ∨
        Nonempty (G ≃* Blueprint.NativeSporadic.ON)

@[expose] def AschbacherTheorem5Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ) (_hr : 1 ≤ r)
    (Abar : Fin r → Subgroup (D ⧸ Open.aschbacherThm5OddCore D)),
    Function.Injective Abar → (∀ i, Open.aschbacherThm5IsSemisimple (Abar i)) →
    (∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x) → ⨆ i, Abar i = ⊤ →
    (∀ h ∈ normalizer (D : Set G), ∀ i, ∃ j,
      (Open.aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        Open.aschbacherThm5Preimage D (Abar j)) →
    (∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ center G →
      Open.aschbacherThm5Centralizes (Open.aschbacherThm5Core D)
        (Open.aschbacherThm5Preimage D (Abar i)) t →
      Open.aschbacherThm5Centralizes (Open.aschbacherThm5Core D)
        (Open.aschbacherThm5Preimage D (Abar j)) (g⁻¹ * t * g) →
      g ∈ normalizer (D : Set G)) →
    (∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ Open.aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ Open.aschbacherThm5Core D,
        a = x * o) →
      g ∈ normalizer (D : Set G)) →
    normalizer (D : Set G) ≠ ⊤ →
    r = 1 ∨
      (r = 2 ∧ ∀ i j : Fin r, i ≠ j →
        (∀ d ∈ D, ∃ a ∈ Open.aschbacherThm5Preimage D (Abar i),
          ∃ b ∈ Open.aschbacherThm5Preimage D (Abar j), d = a * b) ∧
        Open.pRank 2 (Open.aschbacherThm5Preimage D (Abar i)) = 1 ∧
        ∀ a₁ ∈ Open.aschbacherThm5Preimage D (Abar i),
          ∀ a₂ ∈ Open.aschbacherThm5Preimage D (Abar j),
          orderOf a₁ = 2 → orderOf a₂ = 2 → a₁ * a₂ = a₂ * a₁ →
          Open.aschbacherThm5Centralizes (Open.aschbacherThm5Core D)
            (Open.aschbacherThm5Preimage D (Abar i)) a₁ →
          Open.aschbacherThm5Centralizes (Open.aschbacherThm5Core D)
            (Open.aschbacherThm5Preimage D (Abar j)) a₂ →
          a₁ = a₂ ∨ a₁ * a₂ ∈ center G)

@[expose] def SolomonSignalizerInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (b : X) (n : ℕ) (K : Subgroup X), orderOf b = 2 → Odd n → 7 ≤ n →
      K ≤ centralizer ({b} : Set X) → IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set X))) →
      Nonempty (K ⧸ Open.fusionZStar K ≃* alternatingGroup (Fin n)) →
      Open.fusionZStar K = pPrimeCore 2 K

end CFSG.ComponentClassification.GSThmB
