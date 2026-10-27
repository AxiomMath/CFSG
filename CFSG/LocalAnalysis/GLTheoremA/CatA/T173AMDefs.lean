module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement MatrixGroups

@[expose] def MElemMod (p d : ℕ) (F : Type) [Field F] (G : Subgroup (GL (Fin d) F)) : Prop :=
  (∀ g ∈ G, g ^ p ∈ LargeEvenScalars (Fin d) F) ∧
    ∀ g ∈ G, ∀ h ∈ G, ⁅g, h⁆ ∈ LargeEvenScalars (Fin d) F

@[expose] def MToral (p d : ℕ) (F : Type) [Field F] (G : Subgroup (GL (Fin d) F)) : Prop :=
  (∀ g ∈ G, ∀ h ∈ G, g * h = h * g) ∧
    ∀ g ∈ G, ∃ a : Fˣ, (Matrix.GeneralLinearGroup.scalar (Fin d) a * g) ^ p = 1

@[expose] def MDiagAt (d : ℕ) (F : Type) [Field F] (P : GL (Fin d) F)
    (G : Subgroup (GL (Fin d) F)) : Prop :=
  ∀ g ∈ G, ∃ D : Fin d → F,
    ((P * g * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.diagonal D

@[expose] def LinDiagTors (p d : ℕ) (F : Type) [Field F] : Set (GL (Fin d) F) :=
  {t | t ∈ LargeEvenSLGroup (Fin d) F ∧
    (∀ i j : Fin d, i ≠ j → (t : Matrix (Fin d) (Fin d) F) i j = 0) ∧
    ∀ i : Fin d, ((t : Matrix (Fin d) (Fin d) F) i i) ^ p = 1}

@[expose] def GInduced {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type} [Field F]
    {U : Subgroup (GL (Fin d) F)}
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U) (b : Ω) (A : GL (Fin d) F) : Prop :=
  ∃ φ : MulAut (LargeEvenProj U),
    LargeEvenGraphAut (LargeEvenProjMk U)
      (fun h h' : ↥U => (h' : GL (Fin d) F) = A * h * A⁻¹) φ ∧
    LargeEvenInduces θ (fun l l' : ↥S => (l' : Ω) = b⁻¹ * l * b) φ

@[expose] def GActs {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type} [Field F]
    {U : Subgroup (GL (Fin d) F)} (ψ : ↥U →* ↥S) (b : Ω) (A : GL (Fin d) F) : Prop :=
  ∀ u u' : ↥U, (u' : GL (Fin d) F) = A * u * A⁻¹ → (ψ u' : Ω) = b⁻¹ * (ψ u : Ω) * b

@[expose] def GLifts {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type} [Field F]
    {U : Subgroup (GL (Fin d) F)}
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U) (ψ : ↥U →* ↥S) : Prop :=
  ∀ u : ↥U, θ (QuotientGroup.mk (ψ u)) = LargeEvenProjMk U u

@[expose] def GDiagAct {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type} [Field F]
    {U : Subgroup (GL (Fin d) F)} (p : ℕ) (ψ : ↥U →* ↥S) (P : GL (Fin d) F) (b : Ω) : Prop :=
  ∃ A : GL (Fin d) F, GActs ψ b A ∧ A ^ p ∈ LargeEvenScalars (Fin d) F ∧
    ∃ D : Fin d → F, ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.diagonal D

@[expose] def MWt {d : ℕ} {F : Type} [Field F] (P A : GL (Fin d) F) (i : Fin d) : F :=
  ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i

@[expose] def MGU (n d : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin d) F) :=
  Subgroup.closure (LargeEvenGUSet (Fin d) F (2 ^ n))

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
