module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

theorem exists_elemAbelian_of_diagGen {n : ℕ} {F : Type} [Field F] [Finite F]
    (hn : 4 ≤ n) {q : ℕ} (hq : q.Prime) (t : Fˣ) (ht : orderOf t = q)
    (H : Subgroup (SpecialLinearGroup (Fin n) F))
    (hmem : ∀ i : Fin 3, diagGen (n := n) (F := F) t hn i ∈ H) :
    ∃ T : Subgroup (SpecialLinearGroup (Fin n) F), T ≤ H ∧ CFSG.Open.IsElemAbelian q T ∧
      Nat.card T = q ^ 3 := by
  obtain ⟨T, hTH, hTelem, hTcard, -⟩ :=
    CFSG.exists_elemAbelian_of_commuting_moving (F := F) (X := Fin n → F)
      (G := SpecialLinearGroup (Fin n) F) (ι := Fin 3) (r := q) hq
      (fun i : Fin 3 => diagGen (n := n) (F := F) t hn i)
      (fun i : Fin 3 => Pi.single (threeToFin hn i) 1)
      (SpecialLinearGroup.toLin' : SpecialLinearGroup (Fin n) F →*
        ((Fin n → F) ≃ₗ[F] (Fin n → F)))
      hmem
      (fun i => orderOf_diagGen (n := n) (F := F) t hn i hq ht)
      (fun i j => commute_diagGen (n := n) (F := F) t hn i j)
      (fun i a h => dvd_of_diagGen_zpow_fixes (n := n) (F := F) t hn i ht h)
      (fun i j hij => toLin'_diagGen_single_of_ne (n := n) (F := F) t hn hij)
  exact ⟨T, hTH, hTelem, by simpa using hTcard⟩

end CFSG.ClassicalGroups.SpecialLinear

end
