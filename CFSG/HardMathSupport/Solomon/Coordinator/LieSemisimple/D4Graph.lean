module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOuterFull
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three


variable {K : Type} [Field K] [Finite K]

theorem perfectInLayer_d4_graph (hK3 : ringChar K ≠ 3) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) ^ 3 = 1) :
    PerfectInLayer (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hpr⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    D4Dual.exists_dual_fixEquiv n.pos K hK _ hα g a hε rfl
  exact perfectInLayer_of_fixEquiv e
    (D4Dual.perfectInLayer_triality_outer_three hK3 n.pos hK₃ Fr hFr φ hφ3 hφout)

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
