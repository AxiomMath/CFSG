module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Defs

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] def borelK (M L : Subgroup G) : Subgroup G := pResidualOf 2 (M ⊓ L)

@[expose] def borelP (M L : Subgroup G) : Subgroup G := pCoreOf 2 (borelK M L)

@[expose] def IsQ8Square (P : Subgroup G) : Prop :=
  Nat.card P = 32 ∧ ∃ A B : Subgroup G, A ≤ P ∧ B ≤ P ∧ A ⊔ B = P ∧ ⁅A, B⁆ = ⊥ ∧
    Nonempty (↥A ≃* QuaternionGroup 2) ∧ Nonempty (↥B ≃* QuaternionGroup 2)

@[expose] def IsInternalDirect (A B X : Subgroup G) : Prop :=
  ⁅A, B⁆ = ⊥ ∧ A ⊓ B = ⊥ ∧ A ⊔ B = X

@[expose] def quadHyp (v : Fin 4 → ZMod 2) : ZMod 2 := v 0 * v 1 + v 2 * v 3

@[expose] def O4PlusTwo : Subgroup (GL (Fin 4) (ZMod 2)) where
  carrier := {g | ∀ v, quadHyp ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = quadHyp v}
  mul_mem' := by
    intro g h hg hh v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hg _).trans (hh v)
  one_mem' := by
    intro v
    simp
  inv_mem' := by
    intro g hg v
    have h := hg ((↑g⁻¹ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm

@[expose] def ActsAsO4Plus (M₁ X N : Subgroup G) : Prop :=
  ∃ (θ : ↥X →* Multiplicative (Fin 4 → ZMod 2)) (ρ : ↥M₁ →* GL (Fin 4) (ZMod 2)),
    Function.Surjective θ ∧ θ.ker = N.subgroupOf X ∧
    (∀ (m : M₁) (x y : X), (y : G) = m * x * m⁻¹ →
      Multiplicative.toAdd (θ y) =
        (ρ m : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (θ x))) ∧
    ρ.range = O4PlusTwo

@[expose] def pElementsGen (p : ℕ) (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ p ^ k = 1}

@[expose] def Kc3Group (X : Type) [Group X] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ (StatedClassicalModel X .PSL 3 2 f ∨ StatedClassicalModel X .PSp 2 2 f)) ∨
  (∃ f : ℕ, (2 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 f) ∨
    (1 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel X .twistedF4 2 f)) ∨
  CFSG.Blueprint.ReeTitsModel X .Tits 2 1 ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel X .PSL n 2 1) ∨
  (∃ s : TauCeti.SporadicName,
    (s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier s))

@[expose] def s2I (S L : Subgroup G) : Subgroup G := baum S ⊓ Subgroup.centralizer (L : Set G)

@[expose] def s2SI (S L : Subgroup G) : Subgroup G := S ⊓ Subgroup.normalizer (L : Set G)

@[expose] def s2Q1 (S L : Subgroup G) : Subgroup G := pCoreOf 2 (L ⊔ baum S)

@[expose] def s2Phi (S L : Subgroup G) : Subgroup G :=
  frattiniOf (s2I S L) ⊓ Subgroup.centralizer (s2SI S L : Set G)

structure A5Cfg (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) : Prop where
  cs : ConstrainedSetting G T M H S L
  alt5 : IsAltType L 5
  single : conjJoin S L = L

structure A5Cfg2 (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) : Prop where
  cs : ConstrainedSetting G T M H S L
  alt5 : IsAltType L 5
  double : conjJoin S L ≠ L

end CFSG.QuasithinUnique.A5
