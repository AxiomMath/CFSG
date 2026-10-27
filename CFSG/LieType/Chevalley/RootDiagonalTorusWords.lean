module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem cartanChar_prod_zpow_eq {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : B * τ.cartan = 1)
    (a : Fin τ.rank → Kˣ) : cartanChar (fun i => ∏ j, a j ^ B j i) = a := by
  funext l
  calc ∏ i, (∏ j, a j ^ B j i) ^ τ.cartan i l
      = ∏ i, ∏ j, a j ^ (B j i * τ.cartan i l) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm
    _ = ∏ j, ∏ i, a j ^ (B j i * τ.cartan i l) := Finset.prod_comm
    _ = ∏ j, a j ^ ((B * τ.cartan) j l) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Matrix.mul_apply, Finset.prod_zpow_eq_zpow_sum]
    _ = a l := by
        rw [hB]
        simp [Matrix.one_apply]

theorem rootDiagUnit_eq_list_prod_torusElt
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hB : B * τ.cartan = 1) (a : Fin τ.rank → Kˣ) :
    rootDiagUnit τ a =
      ((List.finRange τ.rank).map fun i => torusElt τ K i (∏ j, a j ^ B j i)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_prod_zpow_eq hB]

theorem G2_F4_root_character_diagonals_inner
    (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4) (K : Type)
    [Field K] :
    (∃ B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ, B * τ.cartan = 1 ∧ τ.cartan * B = 1) ∧
    ∀ B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ, B * τ.cartan = 1 → ∀ a : Fin τ.rank → Kˣ,
      rootDiagUnit τ a =
          ((List.finRange τ.rank).map fun i => torusElt τ K i (∏ j, a j ^ B j i)).prod ∧
        rootDiagUnit τ a ∈ torusGroup τ K ∧
        ∃ h : rootDiagUnit τ a ∈ adjointGroup τ K,
          rootDiagAut τ K a = MulAut.conj (⟨rootDiagUnit τ a, h⟩ : adjointGroup τ K) := by
  refine ⟨?_, fun B hB a => ?_⟩
  · rcases hτ with rfl | rfl
    · exact ⟨!![2, 1; 3, 2], by decide, by decide⟩
    · exact ⟨!![2, 3, 2, 1; 3, 6, 4, 2; 4, 8, 6, 3; 2, 4, 3, 2], by decide, by decide⟩
  have he := rootDiagUnit_eq_list_prod_torusElt (K := K) hB a
  have hH : rootDiagUnit τ a ∈ torusGroup τ K := by
    rw [he]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_torusGroup i _
  have hC : rootDiagUnit τ a ∈ adjointGroup τ K := by
    rw [he]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_adjointGroup i _
  exact ⟨he, hH, hC, MulEquiv.ext fun g => Subtype.ext rfl⟩

end CFSG.LieType.Chevalley
