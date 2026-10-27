module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Irred
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Thompson
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A]

structure CampbellHyp (X K R P : Subgroup A) : Prop where
  charTwo : X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X
  K_le : K ≤ X
  K_normal : X ≤ normalizer (K : Set A)
  K_perfect : ⁅K, K⁆ = K
  X_eq : X = K ⊔ pCoreOf 2 X
  quot : ∃ f : ↥K →* GL32, Function.Surjective f ∧
    ∀ k : ↥K, f k = 1 ↔ (k : A) ∈ pCoreOf 2 X
  R_le : R ≤ X
  R_two : IsPGroup 2 R
  R_sylow : ¬ 2 ∣ (R.subgroupOf X).index
  R_le_P : R ≤ P
  P_le : P ≤ X
  P_index : (P.subgroupOf X).index = 7
  cent_le : X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) ≤ P
  pushUp : ∀ Q₀ : Subgroup A, Q₀ ≤ pCoreOf 2 P → Q₀ ≠ ⊥ →
    (Q₀.subgroupOf (pCoreOf 2 P)).Characteristic → ¬ X ≤ normalizer (Q₀ : Set A)

@[expose] def CampbellConclusion (X K : Subgroup A) : Prop :=
  ∃ A₀ B₀ : Subgroup A, A₀ ≤ B₀ ∧ B₀ ≤ omegaCenter (K ⊓ pCoreOf 2 X) ∧
    X ≤ normalizer (A₀ : Set A) ∧ X ≤ normalizer (B₀ : Set A) ∧
    K ≤ centralizer (A₀ : Set A) ∧
    (∀ w ∈ omegaCenter (K ⊓ pCoreOf 2 X), ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ B₀) ∧
    A₀.relIndex B₀ = 8 ∧
    ∀ g ∈ X, (∀ u ∈ B₀, g * u * g⁻¹ * u⁻¹ ∈ A₀) → g ∈ pCoreOf 2 X

@[expose] def HasNatSection (K D C₀ : Subgroup A) : Prop :=
  K ≤ normalizer (D : Set A) ∧ C₀ ≤ D ∧
    ∃ (a : ↥K →* GL32) (b : ↥D →* Multiplicative (Fin 3 → ZMod 2)),
      Function.Surjective a ∧ a.ker = CFSG.pCore 2 ↥K ∧ Function.Surjective b ∧
      b.ker = C₀.subgroupOf D ∧
      ∀ (k : ↥K) (u v : ↥D), (v : A) = k * u * k⁻¹ →
        Multiplicative.toAdd (b v) = ((a k : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (Multiplicative.toAdd (b u))

@[expose] def HasNatSum2 (K Q : Subgroup A) : Prop :=
  K ≤ normalizer (Q : Set A) ∧
    ∃ (a : ↥K →* GL32) (b : ↥Q →* Multiplicative (Fin 2 → Fin 3 → ZMod 2)),
      Function.Surjective a ∧ a.ker = CFSG.pCore 2 ↥K ∧ Function.Surjective b ∧
      Function.Injective b ∧
      ∀ (k : ↥K) (u v : ↥Q), (v : A) = k * u * k⁻¹ → ∀ i : Fin 2,
        Multiplicative.toAdd (b v) i = ((a k : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (Multiplicative.toAdd (b u) i)

@[expose] def vecStab (e : Fin 3 → ZMod 2) : Subgroup GL32 where
  carrier := {g | ((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e = e}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    simp [Units.val_mul, ← Matrix.mulVec_mulVec, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h : ((a⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((a : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e) = e := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rwa [ha] at h

@[expose] def stabSub (K : Subgroup A) (a : ↥K →* GL32) (e : Fin 3 → ZMod 2) (Q : Subgroup A) :
    Subgroup A :=
  ((vecStab e).comap a).map K.subtype ⊔ Q

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
