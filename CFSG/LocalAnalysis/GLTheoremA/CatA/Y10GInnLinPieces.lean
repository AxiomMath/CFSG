module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def LinPCompIsComp : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n p : ℕ), p.Prime → ∀ s : GL (Fin n) F, (orderOf s : F) ≠ 0 →
    ∀ M : Subgroup (GL (Fin n) F),
      GLAPComponent p (Subgroup.centralizer ({s} : Set (GL (Fin n) F)) ⊓ StatedSL n F) M →
        CFSG.Open.IsComponentOf M (Subgroup.centralizer ({s} : Set (GL (Fin n) F)) ⊓ StatedSL n F)

@[expose] def LinLabelDict : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (labJ : GLALabel) (a m : ℕ) (E : Type) [Field E] [Finite E],
    2 ≤ a → Nat.card E = 2 ^ m → HasLabel J (fun l : GLALabel => l = labJ) →
      Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL a E)) →
        canonLabel labJ = ⟨.A, a - 1, m⟩

@[expose] def LinAutDecomp3 : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [Finite K], (2 : K) = 0 → 3 ≤ d →
    ∀ β : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)), β ^ 3 = 1 →
      ∃ u f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)), β = u * f ∧
        u ∈ LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ ∧
        f ∈ LargeEvenMatFieldImage (LargeEvenProjMk _) ∧ f ^ 3 = 1

@[expose] def FieldLinComp3 : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [Finite K], (2 : K) = 0 → 3 ≤ d →
    ∀ u f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
      u ∈ LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ → f ∈ LargeEvenMatFieldImage (LargeEvenProjMk _) →
        f ^ 3 = 1 → (u * f) ^ 3 = 1 → f ≠ 1 →
          ∀ J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
            GLAPComponent 3 (fixSubgroup (u * f)) J →
              ∃ (a m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ m ∧
                Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL a E))

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
