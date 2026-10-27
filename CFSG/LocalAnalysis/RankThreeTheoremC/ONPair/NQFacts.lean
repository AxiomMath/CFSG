module

public import CFSG.Sporadic.Schreier.ONActions
public import CFSG.Sporadic.Schreier.ONPermArr
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelData
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.FixCheck
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.AlphaCheck
public import CFSG.Sporadic.ON.Lines
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier

@[expose] noncomputable def nqEv2 {G : Type*} [Group G] (a b : G) (w : List ℤ) : G :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 2 => if (h : ℕ) = 0 then a else b) (ptoLetters 2 w)

@[expose] noncomputable def nqWitL {G : Type*} [Group G] (S R : List ℤ → G)
    (g n m : ℕ → List ℤ) (a i : ℕ) (h : Fin 5) : G :=
  if (h : ℕ) < 4 then S (n h) else R (g (a + 1)) * S (m i)

section Facts


@[expose] noncomputable def nqRho (w : List ℤ) : Equiv.Perm (Fin nL) := nqEv2 d0 d1 w

@[expose] noncomputable def nqAP : Equiv.Perm (Fin nL) := nqRho alphaWordA

@[expose] noncomputable def nqRhoA (w : List ℤ) : Equiv.Perm (Fin nL) := nqEv2 nqAP d1 w

@[expose] noncomputable def nqSig (w : List ℤ) : Equiv.Perm (Fin nL) :=
  nqEv2 (nqRho h1Word) (nqRho h2Word) w

@[expose] noncomputable def nqSigA (w : List ℤ) : Equiv.Perm (Fin nL) :=
  nqEv2 (nqRhoA h1Word) (nqRhoA h2Word) w

@[expose] noncomputable def nqL2 : Fin nL := nqRho u2Word 0

structure NQFactsAt (g n m : ℕ → List ℤ) (u : ℕ → ℕ → List (Fin 5 × Bool)) : Prop where
  stab : ∀ k < 4, nqSigA (n k) nqL2 = nqL2
  base : nqRho (g 0) 0 = 0
  forest : ∀ y : Fin nL, ∃ ks : List ℕ, (∀ k ∈ ks, k < 4) ∧ ∃ a < 36,
    (ks.map fun k => nqSig (n k)).prod (nqRho (g a) 0) = y
  orbit0 : nqSigA (m 0) nqL2 = nqL2
  orbit1 : nqSigA (m 1) nqL2 ≠ nqL2
  orbit : ∀ i < 456, ∀ q ∈ [qWords[0]!, qWords[1]!, qWords[2]!, tWord], ∃ j < 456,
    nqSigA q (nqSigA (m i) nqL2) = nqSigA (m j) nqL2
  wit : ∀ a < 35, ∀ i < 456,
    (Quiver.SchreierGraph.evalWord (nqWitL nqSig nqRho g n m a i) (u a i) 0 = 0 ∧
        Quiver.SchreierGraph.evalWord (nqWitL nqSigA nqRhoA g n m a i) (u a i) nqL2 ≠ nqL2) ∨
      (Quiver.SchreierGraph.evalWord (nqWitL nqSigA nqRhoA g n m a i) (u a i) nqL2 = nqL2 ∧
        Quiver.SchreierGraph.evalWord (nqWitL nqSig nqRho g n m a i) (u a i) 0 ≠ 0)

@[expose] def OnanNQFacts : Prop := ∃ g n m u, NQFactsAt g n m u

end Facts

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
