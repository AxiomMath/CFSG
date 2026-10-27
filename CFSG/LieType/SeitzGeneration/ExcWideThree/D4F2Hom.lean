module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.A2Lemma
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Config
public import CFSG.LinearAlgebra.DesarguesianPlanes.SteinbergRecognition
public import CFSG.Timmesfeld.RankTwo.ModelG2Comm

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open scoped commutatorElement MatrixGroups

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

@[expose] def d4F2A2Pos (i j : Fin 3) : ℕ := ![![0, 2, 22], ![8, 0, 19], ![23, 21, 0]] i j

theorem d4F2_a2_root_pos : ∀ i j : Fin 3, i ≠ j →
    Tag.D4.rootCertificate.root (d4F2A2Pos i j) = d4F2A2Root i j := by
  decide +kernel

theorem d4F2_a2_repCheck : ∀ i j k l : Fin 3, i ≠ j → k ≠ l → ¬(k = j ∧ l = i) →
    ∃ C ∈ [(1 : ℤ), -1], RootOps.repCheck Tag.D4 (d4F2A2Pos i j) (d4F2A2Pos k l)
      (if j = k then [(1, 1, d4F2A2Pos i l, C)] else if i = l then [(1, 1, d4F2A2Pos k j, C)]
        else []) = true := by
  decide +kernel

theorem d4F2A2Root_01 : d4F2A2Root 0 1 = d4F2Delta1 := by decide +kernel

theorem d4F2A2Root_12 : d4F2A2Root 1 2 = d4F2Delta2 := by decide +kernel

theorem d4F2A2Root_02 : d4F2A2Root 0 2 = d4F2Theta := by decide +kernel

theorem d4F2A2Root_20 : d4F2A2Root 2 0 = -d4F2Theta := by decide +kernel


section Hom

theorem d4F2_a2_steinbergFamily {K : Type} [Field K] [CharP K 2] :
    CFSG.DesarguesianPlanes.IsSteinbergFamily
      (fun i j c => xPar (rootOperatorFamily Tag.D4) (d4F2A2Root i j) c :
        Fin 3 → Fin 3 → K → ↥(adjointGroup Tag.D4 K)) := by
  refine ⟨fun i j _ c d => (xPar_add _ c d).symm, fun i j k l hij hkl hex c d => ?_⟩
  obtain ⟨C, hC, h⟩ := d4F2_a2_repCheck i j k l hij hkl hex
  have hC1 : (C : K) = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · simp
    · simp [CharTwo.neg_eq]
  have e := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (K := K) h c d
  rw [d4F2_a2_root_pos i j hij, d4F2_a2_root_pos k l hkl] at e
  rw [e]
  split_ifs with hjk hil
  · subst hjk
    simp [d4F2_a2_root_pos i l fun h => hex ⟨rfl, h.symm⟩, hC1]
  · subst hil
    simp [d4F2_a2_root_pos k j fun h => hjk h.symm, hC1, CharTwo.neg_eq]
  · simp

theorem d4F2_exists_a2Hom {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ φ : SL(3, K) →* ↥(adjointGroup Tag.D4 K),
      (∀ c, φ (t12 c) = xPar (rootOperatorFamily Tag.D4) d4F2Delta1 c) ∧
      (∀ c, φ (t23 c) = xPar (rootOperatorFamily Tag.D4) d4F2Delta2 c) ∧
      (∀ c, φ (t13 c) = xPar (rootOperatorFamily Tag.D4) d4F2Theta c) ∧
      (∀ c, φ (t31 c) = xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) c) := by
  obtain ⟨φ, hφ⟩ := CFSG.DesarguesianPlanes.exists_hom_of_steinbergFamily
    (d4F2_a2_steinbergFamily (K := K))
  refine ⟨φ, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
  · rw [hφ 0 1 c (t12 c) (by decide) rfl, d4F2A2Root_01]
  · rw [hφ 1 2 c (t23 c) (by decide) rfl, d4F2A2Root_12]
  · rw [hφ 0 2 c (t13 c) (by decide) rfl, d4F2A2Root_02]
  · rw [hφ 2 0 c (t31 c) (by decide) rfl, d4F2A2Root_20]

end Hom

end CFSG.LieType.SeitzGeneration.ExcWideThree
