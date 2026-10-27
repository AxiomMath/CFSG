module

public import CFSG.ClassicalInvolution.WeakCT.FieldTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogE
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.Timmesfeld CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank

theorem weakCT_e7_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {X : Type} [Group X]
    (U : Fin 7 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 1)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E7 0 2 1 := by
  have hroot : ∃ c : Fin 7, edgeE 7 ⟨0, by norm_num⟩ c ∨ edgeE 7 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  obtain ⟨ρ, hρ, hψ⟩ :=
    exists_frame_of_tree_two hF (rootedTree_edgeE (r := 7) (by norm_num)) hroot hcomm hpair
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.weakCT_e7_of_frame 2 1
    ⟨Nat.prime_two, le_rfl, rfl⟩ (by rw [hF, pow_one]) U hgen hcomm hρ hψ

theorem weakCT_e8_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {X : Type} [Group X]
    (U : Fin 8 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 8, edgeE 8 i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : (adjointGroup .E8 (GaloisField 2 1)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (adjointGroup .E8 (GaloisField 2 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E8 0 2 1 := by
  have hroot : ∃ c : Fin 8, edgeE 8 ⟨0, by norm_num⟩ c ∨ edgeE 8 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  obtain ⟨ρ, hρ, hψ⟩ :=
    exists_frame_of_tree_two hF (rootedTree_edgeE (r := 8) (by norm_num)) hroot hcomm hpair
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.weakCT_e8_of_frame 2 1
    ⟨Nat.prime_two, le_rfl, rfl⟩ (by rw [hF, pow_one]) U hgen hcomm hρ hψ

end CFSG.ClassicalInvolution.WeakCT
