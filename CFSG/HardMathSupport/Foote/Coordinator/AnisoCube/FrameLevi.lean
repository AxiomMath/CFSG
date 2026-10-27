module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3
public import CFSG.RankThree.PartOne.D4RC.ParaConn

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

public noncomputable section

open CFSG.HardMathSupport.Malle.SeitzCube
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.E6 (e6Index)

open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (m := 2)) ∅

@[expose] def e6FrameLeviSet : Fin 2 → Set (Fin Tag.E6.rank)
  | 0 => {e6Index 0, e6Index 2}
  | 1 => {e6Index 4, e6Index 5}

theorem e6A2Frame_apply_eq_zero (i : Fin 2) (γ : Fin 2 → ℤ) {k : Fin Tag.E6.rank}
    (hk : k ∉ e6FrameLeviSet i) : e6A2Frame (Fin.castSucc i) γ k = 0 := by
  fin_cases i
  · simp only [e6FrameLeviSet, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hk
    simp [e6A2Frame, e6A2Simple₀, e6A2Simple₁, Ne.symm hk.1, Ne.symm hk.2]
  · simp only [e6FrameLeviSet, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hk
    simp [e6A2Frame, e6A2Simple₀, e6A2Simple₁, Ne.symm hk.1, Ne.symm hk.2]

theorem transvection_eq_x_of_RA2 (K : Type) [Field K] {a b : Fin 3} (hab : a ≠ b) :
    ∃ γ : Fin 2 → ℤ, γ ∈ RA2 ∧ ∀ c : K,
      CFSG.LieType.Steinberg.SL.x 2 K γ c = Matrix.SpecialLinearGroup.transvection hab c := by
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · refine ⟨![1, 0], ?_, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨0, 1, by decide, by decide⟩
  · refine ⟨![1, 1], ?_, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨0, 2, by decide, by decide⟩
  · refine ⟨![-1, 0], ?_, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨1, 0, by decide, by decide⟩
  · exact absurd rfl hab
  · refine ⟨![0, 1], ?_, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨1, 2, by decide, by decide⟩
  · refine ⟨![-1, -1], ?_, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨2, 0, by decide, by decide⟩
  · refine ⟨![0, -1], ?_, fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨2, 1, by decide, by decide⟩
  · exact absurd rfl hab

theorem sl3_le_of_transvections (K : Type) [Field K] (S : Subgroup (SL(3, K)))
    (h : ∀ a b : Fin 3, ∀ hab : a ≠ b, ∀ c : K,
      Matrix.SpecialLinearGroup.transvection hab c ∈ S) (A : SL(3, K)) : A ∈ S := by
  have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, b, hab, c, rfl⟩
    exact h a b hab c
  rw [CFSG.LinearGroups.special_linear_elementary_generation] at hle
  exact hle (Subgroup.mem_top A)

theorem range_le_parabolicLevi_E6 (K : Type) [Field K]
    (ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K)
    (hψ : ∀ i : Fin 3, ∀ γ : Fin 2 → ℤ, γ ∈ RA2 → ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      ((ψ i (CFSG.LieType.Steinberg.SL.x 2 K γ c) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        pinnedX Tag.E6 K (e6A2Frame i γ) (ε * c))
    (i : Fin 2) (A : SL(3, K)) :
    ((ψ (Fin.castSucc i) A : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
      parabolicLevi Tag.E6 K (e6FrameLeviSet i) := by
  let f : SL(3, K) →* ModGL Tag.E6 K :=
    (adjointGroup Tag.E6 K).subtype.comp (ψ (Fin.castSucc i))
  have key : A ∈ (parabolicLevi Tag.E6 K (e6FrameLeviSet i)).comap f := by
    refine sl3_le_of_transvections K _ ?_ A
    intro a b hab c
    obtain ⟨γ, hγ, hx⟩ := transvection_eq_x_of_RA2 K hab
    rw [Subgroup.mem_comap, ← hx c]
    obtain ⟨ε, -, hε⟩ := hψ (Fin.castSucc i) γ hγ
    have hf : f (CFSG.LieType.Steinberg.SL.x 2 K γ c) =
        pinnedX Tag.E6 K (e6A2Frame (Fin.castSucc i) γ) (ε * c) := hε c
    rw [hf]
    obtain ⟨a', b', hab', -, he⟩ := sl_x_frame K (Fin.castSucc i) hγ
    have hroot : IsRoot Tag.E6 (e6A2Frame (Fin.castSucc i) γ) := by
      rw [he]
      exact isRoot_e6A2Root _ hab'
    have hmem : pinnedX Tag.E6 K (e6A2Frame (Fin.castSucc i) γ) (ε * c) ∈
        CFSG.Blueprint.Chevalley.rootSubgroup Tag.E6 K (e6A2Frame (Fin.castSucc i) γ) :=
      mem_rootSubgroup.2 ⟨ε * c, rfl⟩
    exact CFSG.RankThree.PartOne.D4RC.rcp_rootSubgroup_le_parabolicLevi
      (τ := Tag.E6) (K := K) (J := e6FrameLeviSet i) (γ := e6A2Frame (Fin.castSucc i) γ)
      ⟨hroot, fun k hk => e6A2Frame_apply_eq_zero i γ hk⟩ hmem
  exact key

end

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
