module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniRange

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {t s ε : ℕ}

noncomputable abbrev projFlag (h : UnitaryFieldData p f K) (r ε : ℕ) (I : Finset ℕ) :
    Subgroup (hypPSU h r ε) :=
  (flagStabilizer h r ε ↑I).map (hypProj h r ε)

noncomputable abbrev projUni (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) : Subgroup (hypPSU h (t + s) ε) :=
  (((uniLeviHom (s := s) h hε hI).ker).map (flagStabilizer h (t + s) ε ↑I).subtype).map
    (hypProj h (t + s) ε)

@[expose] def IsBigBlock (s ε : ℕ) (I : Finset ℕ) : Option ↥I → Prop
  | none => 2 ≤ 2 * s + ε
  | some b => 2 ≤ b.1 - predCut I b.1

section NormFix

variable (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}

@[expose] def UniNormFix (hI : IsTopCut I t) (α : MulAut (hypPSU h (t + s) ε)) : Prop :=
  (projFlag h (t + s) ε I).map α.toMonoidHom = projFlag h (t + s) ε I ∧
    ∀ j : Option ↥I, IsBigBlock s ε I j → ∀ x : ↥(flagStabilizer h (t + s) ε ↑I),
      (∀ k, k ≠ j → uniLeviHom (s := s) h hε hI x k = 1) →
      uniLeviHom (s := s) h hε hI x j ∈ uniBlockSub (s := s) (ε := ε) h I j →
      α (hypProj h (t + s) ε x) * (hypProj h (t + s) ε x)⁻¹ ∈ projUni h hε hI

end NormFix

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
