module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrFact
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyPair
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

abbrev SoMat5 : Type := Matrix (Fin 5) (Fin 5) (ZMod 5)

@[expose] def soGram5 : SoMat5 :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 2]

@[expose] def soGroup5 : Subgroup (GL (Fin 5) (ZMod 5)) where
  carrier := {M | (M : SoMat5)ᵀ * soGram5 * (M : SoMat5) = soGram5 ∧ (M : SoMat5).det = 1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · simp only [Units.val_mul, Matrix.transpose_mul]
      calc (b : SoMat5)ᵀ * (a : SoMat5)ᵀ * soGram5 * ((a : SoMat5) * (b : SoMat5))
          = (b : SoMat5)ᵀ * ((a : SoMat5)ᵀ * soGram5 * (a : SoMat5)) * (b : SoMat5) := by
            simp only [Matrix.mul_assoc]
        _ = soGram5 := by rw [ha1, hb1]
    · simp [Matrix.det_mul, ha2, hb2]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have hab : (a : SoMat5) * ((a⁻¹ : GL (Fin 5) (ZMod 5)) : SoMat5) = 1 := by simp
    refine ⟨?_, ?_⟩
    · calc ((a⁻¹ : GL (Fin 5) (ZMod 5)) : SoMat5)ᵀ * soGram5 *
            ((a⁻¹ : GL (Fin 5) (ZMod 5)) : SoMat5)
          = ((a⁻¹ : GL (Fin 5) (ZMod 5)) : SoMat5)ᵀ *
            ((a : SoMat5)ᵀ * soGram5 * (a : SoMat5)) *
            ((a⁻¹ : GL (Fin 5) (ZMod 5)) : SoMat5) := by rw [ha1]
        _ = ((a : SoMat5) * ((a⁻¹ : GL (Fin 5) (ZMod 5)) : SoMat5))ᵀ * soGram5 *
            ((a : SoMat5) * ((a⁻¹ : GL (Fin 5) (ZMod 5)) : SoMat5)) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = soGram5 := by rw [hab]; simp
    · have h1 := congrArg Matrix.det hab
      rw [Matrix.det_mul, ha2, one_mul, Matrix.det_one] at h1
      exact h1

abbrev PGSp45 : Type := ↥soGroup5

@[expose] def GH312Fixed : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.pPrimeCore 2 X = ⊥ → center X = ⊥ →
    (∃ P : Sylow 2 X,
      Nonempty (↥P ≃* RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2)))) →
    (∃ u : X, u * u = 1 ∧ u ≠ 1 ∧
      Nonempty (↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))) →
    Nonempty (X ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (↥(CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup X)) ≃*
        alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
      Nonempty (X ≃* PGSp45)

@[expose] def GH312WrFixed : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.pPrimeCore 2 X = ⊥ → center X = ⊥ →
    (∃ P : Sylow 2 X, Nonempty (↥P ≃* W8)) →
    (∃ u : X, u * u = 1 ∧ u ≠ 1 ∧
      Nonempty (↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))) →
    Nonempty (X ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (X ≃* RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) ∨
      Nonempty (X ≃* PGSp45)

@[expose] def SignDataPGSpXS : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (_φ : X ≃* PGSp45) (τ : X) (D S : Subgroup X)
    (eD : D ≃* DihedralGroup 4) (eS : S ≃* Equiv.Perm (Fin 5)),
    (∃ P : Sylow 2 X, Nonempty (↥P ≃* W8)) → LocalPair τ D S eD eS →
    ∃ χ : X →* ℤˣ, (∀ d ∈ D, orderOf d = 4 → χ d = -1) ∧
      (∀ s : S, Equiv.Perm.sign (eS s) = -1 → χ s = -1) ∧
      (∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → ¬ ∃ g : X, d = g * τ * g⁻¹) ∧
      (∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → χ d = -1 →
        ∀ s ∈ S, s ≠ 1 → s * s = 1 → χ s = -1 → ∃ g : X, d * s = g * τ * g⁻¹)

end CFSG.EvenSporadicStandard.TwoHS
