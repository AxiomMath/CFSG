module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

abbrev UniSU (n d : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin d) F) :=
  LargeEvenSUGroup (Fin d) F (2 ^ n)

abbrev UniPSU (n d : ℕ) (F : Type) [Field F] : Type :=
  LargeEvenProj (UniSU n d F)

abbrev UniMk (n d : ℕ) (F : Type) [Field F] : ↥(UniSU n d F) →* UniPSU n d F :=
  LargeEvenProjMk (UniSU n d F)

@[expose] def UniArith (p n d : ℕ) (F : Type) [Field F] : Prop :=
  p.Prime ∧ p ∣ 2 ^ n + 1 ∧ ¬ p ∣ d ∧ Nat.card F = (2 ^ n) ^ 2 ∧ 1 ≤ n ∧ 3 ≤ d ∧
    (d = 3 → 2 ≤ n)

@[expose] def UniBlockSet (n d : ℕ) (F : Type) [Field F] (I : Finset (Fin d)) :
    Set (GL (Fin d) F) :=
  {g | g ∈ UniSU n d F ∧ ∀ i j : Fin d, (i ∉ I ∨ j ∉ I) →
    (g : Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0}

@[expose] def UniBlockImage (n d : ℕ) (F : Type) [Field F] (I : Finset (Fin d)) :
    Set (UniPSU n d F) :=
  UniMk n d F '' {g : ↥(UniSU n d F) | (g : GL (Fin d) F) ∈ UniBlockSet n d F I}

@[expose] def UniDiagFrame (p n d : ℕ) (F : Type) [Field F] {Q : Type} [Group Q]
    (ψ : Q ≃* UniPSU n d F) (Bbar : Subgroup Q) (A : Subgroup (GL (Fin d) F)) : Prop :=
  A ≤ UniSU n d F ∧ IsElemAbelian p A ∧
    (∀ a ∈ A, ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0) ∧
    Bbar.map ψ.toMonoidHom = (A.subgroupOf (UniSU n d F)).map (UniMk n d F)

@[expose] def modCentreImage {Ω : Type} [Group Ω] (S A : Subgroup Ω) :
    Subgroup (↥S ⧸ Subgroup.center ↥S) :=
  (A.subgroupOf S).map (QuotientGroup.mk' (Subgroup.center ↥S))

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
