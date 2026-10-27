module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Model

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open CFSG.EvenSmallLie.OmegaEight.Stage2

@[expose] def commCons (ρs : List ℕ) : List (ℕ × ℕ) := (ρs.map fun ρ => (ρ, ρ)) ++ [(phiK, phiK)]

@[expose] def relPair (a b c d : ℕ) : Bool :=
  ((mulK a b == mulK b a) == (mulK c d == mulK d c)) &&
    ((powK (mulK a b) 3 == idK) == (powK (mulK c d) 3 == idK))

@[expose] def chainAux (keys : Array ℕ) (R : List ℕ) :
    List ℕ → List ℕ → List (List (ℕ × ℕ)) → Bool
  | _, [], _ => true
  | _, _ :: _, [] => false
  | fx, ρ :: ρs, ks :: kss =>
    (R.all fun σ => !(fx.all fun φ => relPair φ ρ φ σ) ||
      ks.any fun p => p.1 == σ && memK keys p.2 && (fx.all fun φ => mulK p.2 φ == mulK φ p.2) &&
        mulK p.2 ρ == mulK σ p.2) && chainAux keys R (fx ++ [ρ]) ρs kss

end CFSG.EvenSmallLie.OmegaEight.N3Split
