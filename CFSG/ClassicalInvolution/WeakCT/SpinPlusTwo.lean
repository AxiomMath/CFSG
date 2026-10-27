module

public import CFSG.ClassicalInvolution.WeakCT.FieldTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogD

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint
  CFSG.Assembly.LowTwoRank

theorem weakCT_spinPlus_two {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, edgeD n i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : spinGroup (Spin.quadPlus n F) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (spinGroup (Spin.quadPlus n F))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaPlus n 2 1 := by
  have hroot : ∃ c : Fin n, edgeD n ⟨0, by omega⟩ c ∨ edgeD n c ⟨0, by omega⟩ :=
    ⟨⟨1, by omega⟩, Or.inl (Or.inl ⟨rfl, by change 1 + 1 < n; omega⟩)⟩
  obtain ⟨ρ, hρ, hψ⟩ :=
    exists_frame_of_tree_two hF (rootedTree_edgeD hn) hroot hcomm hpair
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.weakCT_spinPlus_of_frame
    ⟨Nat.prime_two, le_rfl, hn⟩ (by omega)
    (by rw [hF, pow_one]) U hgen hcomm hρ hψ

end CFSG.ClassicalInvolution.WeakCT
