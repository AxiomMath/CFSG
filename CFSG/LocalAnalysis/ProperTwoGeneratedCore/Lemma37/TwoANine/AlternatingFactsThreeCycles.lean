module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Equiv.Perm CFSG.LocalAnalysis.ComponentInitial

@[expose] def finEightEquiv : Fin 8 ≃ {x : Fin 9 // x ≠ 8} where
  toFun i := ⟨i.castSucc, Fin.castSucc_ne_last i⟩
  invFun x := x.1.castLT (Fin.val_lt_last x.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem exists_extendDomain_eq {g : Perm (Fin 9)} (hg : g 8 = 8) :
    ∃ g' : Perm (Fin 8), g'.extendDomain finEightEquiv = g := by
  have hp : ∀ x, g x ≠ 8 ↔ x ≠ 8 := fun x =>
    not_congr ⟨fun h => g.injective (h.trans hg.symm), fun h => h ▸ hg⟩
  refine ⟨(finEightEquiv.trans (g.subtypePerm hp)).trans finEightEquiv.symm, ?_⟩
  refine Equiv.ext fun x => ?_
  by_cases hx : x ≠ 8
  · rw [Perm.extendDomain_apply_subtype _ finEightEquiv hx]
    simp
  · rw [Perm.extendDomain_apply_not_subtype _ finEightEquiv hx, not_not.mp hx, hg]

@[expose] def aNineThreeCycles : Set (alternatingGroup (Fin 9)) :=
  {g | ∃ k : Fin 9, k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 8 ∧ (g : Perm (Fin 9)) = swap 0 k * swap 0 1}

theorem aNineThreeCycles_subset_stabilizer :
    aNineThreeCycles ⊆ MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) := by
  rintro g ⟨k, -, -, hk8, hg⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def, hg,
    Perm.mul_apply, swap_apply_of_ne_of_ne (show (8 : Fin 9) ≠ 0 by decide)
      (show (8 : Fin 9) ≠ 1 by decide),
    swap_apply_of_ne_of_ne (show (8 : Fin 9) ≠ 0 by decide) (Ne.symm hk8)]

theorem closure_aNineThreeCycles :
    Subgroup.closure aNineThreeCycles =
      MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) := by
  refine le_antisymm ((Subgroup.closure_le _).mpr aNineThreeCycles_subset_stabilizer)
    fun g hg => ?_
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def] at hg
  obtain ⟨g', hg'⟩ := exists_extendDomain_eq hg
  have hsign : Perm.sign g' = 1 := by
    rw [← Perm.sign_extendDomain g' finEightEquiv, hg']
    exact Perm.mem_alternatingGroup.mp g.2
  have hmem : g' ∈ Subgroup.closure (Set.range (altThreeCyclePerm (n := 6))) := by
    rw [closure_altThreeCyclePerm]
    exact Perm.mem_alternatingGroup.mpr hsign
  have hgen : ∀ i : Fin 6, (altThreeCyclePerm i).extendDomain finEightEquiv =
      swap 0 (finEightEquiv (i.addNat 2)).1 * swap 0 1 := by
    decide +kernel
  have hk : ∀ i : Fin 6, (finEightEquiv (i.addNat 2)).1 ≠ 0 ∧
      (finEightEquiv (i.addNat 2)).1 ≠ 1 ∧ (finEightEquiv (i.addNat 2)).1 ≠ 8 := by
    decide
  have hle : (Subgroup.closure (Set.range (altThreeCyclePerm (n := 6)))).map
      (Perm.extendDomainHom finEightEquiv) ≤
      (Subgroup.closure aNineThreeCycles).map (alternatingGroup (Fin 9)).subtype := by
    rw [MonoidHom.map_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨h0, h1, h8⟩ := hk i
    exact Subgroup.subset_closure ⟨⟨swap 0 (finEightEquiv (i.addNat 2)).1 * swap 0 1,
      (isThreeCycle_swap_mul_swap_same (Ne.symm h0) (by decide) h1).mem_alternatingGroup⟩,
      ⟨_, h0, h1, h8, rfl⟩, (hgen i).symm⟩
  obtain ⟨h, hh, hhg⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map_of_mem _ hmem))
  rwa [show g = h from Subtype.ext (hg'.symm.trans hhg.symm)]

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
