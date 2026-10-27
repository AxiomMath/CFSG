module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Singer
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E6ThreeLines

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open scoped MatrixGroups

section Frame

variable {Ω : Type} [Field Ω]
  (ψ : Fin 3 → SL(3, Ω) →* adjointGroup Tag.E6 Ω)

@[expose] def frameBlock (i : Fin 3) : SL(3, Ω) →* ModGL Tag.E6 Ω :=
  (adjointGroup Tag.E6 Ω).subtype.comp (ψ i)

variable {ψ}

theorem frameBlock_commute (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B))
    {i j : Fin 3} (hij : i ≠ j) (A B : SL(3, Ω)) :
    Commute (frameBlock ψ i A) (frameBlock ψ j B) :=
  (hcomm i j hij A B).map (adjointGroup Tag.E6 Ω).subtype

variable (ψ)

@[expose] def frameHom (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) :
    SL(3, Ω) →* ModGL Tag.E6 Ω where
  toFun A := frameBlock ψ 0 A * frameBlock ψ 1 A * frameBlock ψ 2 A
  map_one' := by simp
  map_mul' A B := by
    have h01 := frameBlock_commute hcomm (i := 1) (j := 0) (by decide) A B
    have h02 := frameBlock_commute hcomm (i := 2) (j := 0) (by decide) A B
    have h12 := frameBlock_commute hcomm (i := 2) (j := 1) (by decide) A B
    simp only [map_mul]
    set A0 := frameBlock ψ 0 A
    set A1 := frameBlock ψ 1 A
    set A2 := frameBlock ψ 2 A
    set B0 := frameBlock ψ 0 B
    set B1 := frameBlock ψ 1 B
    set B2 := frameBlock ψ 2 B
    calc A0 * B0 * (A1 * B1) * (A2 * B2) = A0 * B0 * A1 * (B1 * A2) * B2 := by
          simp only [mul_assoc]
      _ = A0 * B0 * A1 * (A2 * B1) * B2 := by rw [h12.eq]
      _ = A0 * (B0 * A1) * A2 * B1 * B2 := by simp only [mul_assoc]
      _ = A0 * (A1 * B0) * A2 * B1 * B2 := by rw [h01.eq]
      _ = A0 * A1 * (B0 * A2) * B1 * B2 := by simp only [mul_assoc]
      _ = A0 * A1 * (A2 * B0) * B1 * B2 := by rw [h02.eq]
      _ = A0 * A1 * A2 * (B0 * B1 * B2) := by simp only [mul_assoc]

end Frame

section Transfer

variable {Ω : Type} [Field Ω] {ψ : Fin 3 → SL(3, Ω) →* adjointGroup Tag.E6 Ω}

theorem frameBlock_frob (hψ : IsSignedFrame Ω ψ) (Fr : Ω →+* Ω) (i : Fin 3) (A : SL(3, Ω)) :
    frameBlock ψ i (Matrix.SpecialLinearGroup.map Fr A) =
      Units.map (entrywiseHom Fr) (frameBlock ψ i A) := by
  have e : Units.map (entrywiseHom Fr) (frameBlock ψ i A) = baseChangeGL Fr (frameBlock ψ i A) :=
    Units.ext rfl
  rw [e]
  exact sl3Hom_map_eq_of_pinnedX Fr (e6A2Frame i) (e6A2Sign i) (frameBlock ψ i)
    (frameBlock ψ i) (hψ i) (hψ i) A

theorem frameBlock_map {K : Type} [Field K] (f : K →+* Ω)
    {ψK : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K} (hψK : IsSignedFrame K ψK)
    (hψ : IsSignedFrame Ω ψ) (i : Fin 3) (A : SL(3, K)) :
    frameBlock ψ i (Matrix.SpecialLinearGroup.map f A) =
      baseChangeGL f (frameBlock ψK i A) :=
  sl3Hom_map_eq_of_pinnedX f (e6A2Frame i) (e6A2Sign i) (frameBlock ψK i) (frameBlock ψ i)
    (hψK i) (hψ i) A

theorem frameHom_frob (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B))
    (hψ : IsSignedFrame Ω ψ) (Fr : Ω →+* Ω) (A : SL(3, Ω)) :
    frameHom ψ hcomm (Matrix.SpecialLinearGroup.map Fr A) =
      Units.map (entrywiseHom Fr) (frameHom ψ hcomm A) := by
  change frameBlock ψ 0 _ * frameBlock ψ 1 _ * frameBlock ψ 2 _ =
    Units.map (entrywiseHom Fr) (frameBlock ψ 0 A * frameBlock ψ 1 A * frameBlock ψ 2 A)
  rw [map_mul, map_mul, frameBlock_frob hψ, frameBlock_frob hψ, frameBlock_frob hψ]

theorem frameHom_eq_mul (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (i : Fin 3)
    (A : SL(3, Ω)) :
    ∃ c : ModGL Tag.E6 Ω, frameHom ψ hcomm A = frameBlock ψ i A * c ∧
      ∀ X : SL(3, Ω), Commute c (frameBlock ψ i X) := by
  have hc := fun (i j : Fin 3) (hij : i ≠ j) (A B : SL(3, Ω)) => frameBlock_commute hcomm hij A B
  fin_cases i
  · refine ⟨frameBlock ψ 1 A * frameBlock ψ 2 A, by
      change frameBlock ψ 0 A * frameBlock ψ 1 A * frameBlock ψ 2 A = _
      simp only [mul_assoc, Fin.zero_eta], fun X => ?_⟩
    exact ((hc 1 0 (by decide) A X).mul_left (hc 2 0 (by decide) A X))
  · refine ⟨frameBlock ψ 0 A * frameBlock ψ 2 A, by
      change frameBlock ψ 0 A * frameBlock ψ 1 A * frameBlock ψ 2 A = _
      rw [(hc 0 1 (by decide) A A).eq]
      simp only [mul_assoc]
      rfl, fun X => ?_⟩
    exact ((hc 0 1 (by decide) A X).mul_left (hc 2 1 (by decide) A X))
  · refine ⟨frameBlock ψ 0 A * frameBlock ψ 1 A, by
      change frameBlock ψ 0 A * frameBlock ψ 1 A * frameBlock ψ 2 A = _
      rw [mul_assoc, (hc 1 2 (by decide) A A).eq, ← mul_assoc, (hc 0 2 (by decide) A A).eq,
        mul_assoc]
      rfl, fun X => ?_⟩
    exact ((hc 0 2 (by decide) A X).mul_left (hc 1 2 (by decide) A X))

theorem frameHom_conj (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (i : Fin 3)
    (Q B : SL(3, Ω)) :
    (frameHom ψ hcomm Q)⁻¹ * frameBlock ψ i B * frameHom ψ hcomm Q =
      frameBlock ψ i (Q⁻¹ * B * Q) := by
  obtain ⟨c, hQ, hcc⟩ := frameHom_eq_mul hcomm i Q
  rw [hQ]
  have h1 : Commute c (frameBlock ψ i (Q⁻¹ * B * Q)) := hcc _
  calc (frameBlock ψ i Q * c)⁻¹ * frameBlock ψ i B * (frameBlock ψ i Q * c)
      = c⁻¹ * ((frameBlock ψ i Q)⁻¹ * frameBlock ψ i B * frameBlock ψ i Q) * c := by group
    _ = c⁻¹ * frameBlock ψ i (Q⁻¹ * B * Q) * c := by simp only [map_mul, map_inv]
    _ = _ := by rw [mul_assoc, ← h1.eq]; group

end Transfer

end CFSG.HardMathSupport.Malle.SeitzCube
