module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def oTwoRes (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ X ∧ Odd (orderOf x)}

@[expose] def twoCoreIn (X : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup (CFSG.pCore 2) X

@[expose] def JElem (S : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ A : Subgroup G, IsMaxElemAbelianIn S A ∧ x ∈ A}

@[expose] def IsOuterOn (x : G) (X N : Subgroup G) : Prop :=
  x ∈ normalizer (X : Set G) ∧
    ¬ ∃ k ∈ X, ∀ y ∈ X, x * y * x⁻¹ * (k * y * k⁻¹)⁻¹ ∈ N

@[expose] def IsWeaklyClosedWrt (A T H : Subgroup G) : Prop :=
  ∀ h ∈ H, CFSG.conjugate A h ≤ T → CFSG.conjugate A h = A

@[expose] def IsZ4Pow4 (V : Subgroup G) : Prop :=
  Nonempty (↥V ≃* (Fin 4 → Multiplicative (ZMod 4)))

@[expose] def IsDih2 (P : Subgroup G) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥P ≃* DihedralGroup (2 ^ m))

@[expose] def IsDihSd (P : Subgroup G) : Prop :=
  IsDih2 P ∨ ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup n)

@[expose] def IsD8 (P : Subgroup G) : Prop :=
  Nonempty (↥P ≃* DihedralGroup 4)

@[expose] def IsNormalE32In (S A : Subgroup G) : Prop :=
  A ≤ S ∧ IsElemAb2 A 5 ∧ (A.subgroupOf S).Normal

@[expose] abbrev WrZ2 (X : Type) [Group X] : Type :=
  RegularWreathProduct X (Multiplicative (ZMod 2))

@[expose] def IsPermModuleMod {n : ℕ} (P : (Fin n → ZMod 2) → Prop) (N : Set (Fin n → ZMod 2))
    (φ : (Fin n → ZMod 2) → G) (V B H : Subgroup G)
    (Alt : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  B ≤ V ∧ (B.subgroupOf V).Normal ∧ H ≤ normalizer (V : Set G) ∧ H ≤ normalizer (B : Set G) ∧
    (∀ v, P v → φ v ∈ V) ∧
    (∀ v w, P v → P w → (φ v * φ w)⁻¹ * φ (v + w) ∈ B) ∧
    (∀ v, P v → (φ v ∈ B ↔ v ∈ N)) ∧
    (∀ x ∈ V, ∃ v, P v ∧ (φ v)⁻¹ * x ∈ B) ∧
    (∀ h ∈ H, ∃ σ ∈ Alt, ∀ v, P v → (h * φ v * h⁻¹)⁻¹ * φ (permVec σ v) ∈ B) ∧
    (∀ σ ∈ Alt, ∃ h ∈ H, ∀ v, P v → (h * φ v * h⁻¹)⁻¹ * φ (permVec σ v) ∈ B)

@[expose] def IsNatModA5 (V B H : Subgroup G) : Prop :=
  ∃ φ : (Fin 5 → ZMod 2) → G,
    IsPermModuleMod (n := 5) IsEvenVec {0} φ V B H (alternatingGroup (Fin 5))

@[expose] def IsNatModS5 (V B H : Subgroup G) : Prop :=
  ∃ φ : (Fin 5 → ZMod 2) → G,
    IsPermModuleMod (n := 5) IsEvenVec {0} φ V B H ⊤

@[expose] def IsZ4AugModuleMod (Pm : Subgroup (Equiv.Perm (Fin 5))) (V O X : Subgroup G) : Prop :=
  X ≤ normalizer ((V ⊔ O : Subgroup G) : Set G) ∧ X ≤ normalizer (O : Set G) ∧
    ∃ (ρ : ↥X →* Equiv.Perm (Fin 5)) (e : ↥V →* Multiplicative (Fin 5 → ZMod 4)),
      ρ.range = Pm ∧ Function.Injective e ∧
      (∀ v : ↥V, ∑ i, (Multiplicative.toAdd (e v)) i = 0) ∧
      (∀ w : Fin 5 → ZMod 4, ∑ i, w i = 0 → ∃ v : ↥V, e v = Multiplicative.ofAdd w) ∧
      ∀ (x : ↥X) (v v' : ↥V) (o : G), o ∈ O → (x : G) * v * (x : G)⁻¹ = v' * o →
        e v' = Multiplicative.ofAdd (Multiplicative.toAdd (e v) ∘ (ρ x).symm)

open Matrix in
@[expose] def IsNatOmega4Plus (V : Subgroup G) (Y : Subgroup (MulAut ↥V)) : Prop :=
  ∃ (e : ↥V ≃* Multiplicative (Matrix (Fin 2) (Fin 2) (GaloisField 2 2)))
    (φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) →* MulAut ↥V),
    Function.Injective φ ∧ φ.range = Y ∧
      ∀ (A B : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) (v : ↥V),
        Multiplicative.toAdd (e (φ (A, B) v)) =
          (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * Multiplicative.toAdd (e v) *
            (B : Matrix (Fin 2) (Fin 2) (GaloisField 2 2))ᵀ

@[expose] def IsElemAbelianMod (z : G) (U : Subgroup G) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ zpowers z ∧ a * a ∈ zpowers z

@[expose] def IsMaxElemAbelianMod (z : G) (T U : Subgroup G) : Prop :=
  U ≤ T ∧ z ∈ U ∧ IsElemAbelianMod z U ∧
    ∀ V : Subgroup G, V ≤ T → z ∈ V → IsElemAbelianMod z V → Nat.card V ≤ Nat.card U

@[expose] def JMod (z : G) (T : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ U : Subgroup G, IsMaxElemAbelianMod z T U ∧ x ∈ U}

@[expose] def Asc82SchurOmega5 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
    LieModel (L ⧸ oddCore L) .PSp 2 3 1 → oddCore L = ⊥

end CFSG.OddStandard.SmallF3.Omega
