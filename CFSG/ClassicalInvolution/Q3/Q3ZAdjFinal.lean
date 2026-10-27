module

public import CFSG.ClassicalInvolution.Q3.Q3ZAdjMain
public import CFSG.ClassicalInvolution.Q3.Q3ZPres

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank

theorem weakCT3_symplectic_chain (hU : V6Universal) (hC : V6Collapse) {G : Type} [Group G]
    (U : Fin 3 → Subgroup G) (hcomm : ∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a)
    (hA : ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1))
    (hB : ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U 2)
      (U 1)) :
    ∃ Ψ : StatedSp 3 (GaloisField 3 1) →* G,
      Ψ.ker ≤ Subgroup.center (StatedSp 3 (GaloisField 3 1)) ∧
      (Models.SymplecticPairs.longBlock (GaloisField 3 1) 3 2).range.map Ψ = U 2 :=
  weakCT3_symplectic_chain_of (fun g hg => hU g hg) (fun k hk g hg i => hC k hk g hg i) U hcomm
    hA hB

theorem weakCT3_symplectic_chain_of_checks (hV : V6Check) (hVC : V6CollapseCheck) {G : Type}
    [Group G] (U : Fin 3 → Subgroup G) (hcomm : ∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a)
    (hA : ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1))
    (hB : ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U 2)
      (U 1)) :
    ∃ Ψ : StatedSp 3 (GaloisField 3 1) →* G,
      Ψ.ker ≤ Subgroup.center (StatedSp 3 (GaloisField 3 1)) ∧
      (Models.SymplecticPairs.longBlock (GaloisField 3 1) 3 2).range.map Ψ = U 2 :=
  weakCT3_symplectic_chain (v6Universal_of_check hV) (v6Collapse_of_check hVC) U hcomm hA hB

end CFSG.ClassicalInvolution.Q3.Q3Z
