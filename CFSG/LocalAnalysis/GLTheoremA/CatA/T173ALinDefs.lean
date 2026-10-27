module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

abbrev LinSL (d : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin d) F) :=
  LargeEvenSLGroup (Fin d) F

abbrev LinPSL (d : ℕ) (F : Type) [Field F] : Type :=
  LargeEvenProj (LinSL d F)

abbrev LinMk (d : ℕ) (F : Type) [Field F] : ↥(LinSL d F) →* LinPSL d F :=
  LargeEvenProjMk (LinSL d F)

@[expose] def LinArith (p n d : ℕ) (F : Type) [Field F] : Prop :=
  p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 ∧ ¬ p ∣ d ∧ Nat.card F = 2 ^ n ∧ 2 ≤ n ∧ 2 ≤ d

@[expose] def LinBlockSet (d : ℕ) (F : Type) [Field F] (I : Finset (Fin d)) :
    Set (GL (Fin d) F) :=
  {g | g ∈ LinSL d F ∧ ∀ i j : Fin d, (i ∉ I ∨ j ∉ I) →
    (g : Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0}

@[expose] def LinBlockImage (d : ℕ) (F : Type) [Field F] (I : Finset (Fin d)) :
    Set (LinPSL d F) :=
  LinMk d F '' {g : ↥(LinSL d F) | (g : GL (Fin d) F) ∈ LinBlockSet d F I}

@[expose] def LinDiagTorsion (p d : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin d) F) :=
  Subgroup.closure {a | a ∈ LinSL d F ∧ a ^ p = 1 ∧
    ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0}

@[expose] def LinTorsionImage (p d : ℕ) (F : Type) [Field F] : Subgroup (LinPSL d F) :=
  ((LinDiagTorsion p d F).subgroupOf (LinSL d F)).map (LinMk d F)

@[expose] def LinDiagFrame (p d : ℕ) (F : Type) [Field F] {Q : Type} [Group Q]
    (ψ : Q ≃* LinPSL d F) (Bbar : Subgroup Q) (A : Subgroup (GL (Fin d) F)) : Prop :=
  A ≤ LinSL d F ∧ IsElemAbelian p A ∧
    (∀ a ∈ A, ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0) ∧
    Bbar.map ψ.toMonoidHom = (A.subgroupOf (LinSL d F)).map (LinMk d F)

@[expose] def InducesInnerModCentre {Ω : Type} [Group Ω] (S : Subgroup Ω) (b : Ω) (s : ↥S) :
    Prop :=
  ∀ l : ↥S, ∃ z ∈ Subgroup.center ↥S, b⁻¹ * (l : Ω) * b = ((s * l * s⁻¹ * z : ↥S) : Ω)

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
