module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaPSL

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts

theorem seitz_model_L {F : Type} [Field F] [Finite F] (hF3 : 3 ∣ Nat.card F - 1)
    {D H : Subgroup (MulAut (projectiveSL 3 F))} (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 9)
    (hH : innerAut (projectiveSL 3 F) ≤ H) (hne : localDeltaIn 3 H D ≠ ⊥) :
    D ≤ linearAutGroup 3 F ∧
      (∀ α ∈ linearAutGroup 3 F, (∀ d ∈ D, α * d = d * α) → α ∈ D) ∧
      ∃ A B : GL (Fin 3) F, conjAut 3 F A ∈ D ∧ conjAut 3 F B ∈ D ∧ A * B ≠ B * A := by
  have hDl : D ≤ linearAutGroup 3 F := by
    by_contra hDl
    exact hne (localDeltaIn_eq_bot_of_not_le_linearAutGroup_three hD hDl hH)
  have hab : ¬ ∀ A ∈ D.comap (conjAut 3 F), ∀ B ∈ D.comap (conjAut 3 F), A * B = B * A := by
    intro hab
    exact hne (localDeltaIn_eq_bot_of_abelian_plane hD hcard hDl hF3 hab hH)
  obtain ⟨-, -, hC, -⟩ :=
    ProjectivePlane.linear_projective_nonabelian_plane_coprime_centralizer_central (p := 3)
      Nat.prime_three (by norm_num) D hDl (fun x hx y hy => comm_of_elemAbelian hD hx hy) hD.2
      (by rw [hcard]; norm_num) hab
  refine ⟨hDl, fun α hα hcomm => ?_, ?_⟩
  · have hmem : α ∈ Subgroup.centralizer (D : Set (MulAut (projectiveSL 3 F))) ⊓
        linearAutGroup 3 F :=
      ⟨Subgroup.mem_centralizer_iff.2 fun d hd => (hcomm d hd).symm, hα⟩
    rw [hC] at hmem
    exact hmem
  · push Not at hab
    obtain ⟨A, hA, B, hB, hAB⟩ := hab
    exact ⟨A, B, hA, hB, hAB⟩

end CFSG.HardMathSupport.Solomon.Coordinator
