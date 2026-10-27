module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8D8
public import CFSG.ClassicalInvolution.RouteD.MultiModelRoot

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE8

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false


@[expose] def e8Delta : Fin (Tag.rank .E8) → ℤ := ![1, 3, 3, 5, 4, 3, 2, 1]

theorem isRoot_e8Delta : IsRoot .E8 e8Delta := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  decide +kernel

@[expose] def e8DeltaWord : List (Fin (Tag.rank .E8)) :=
  ([2, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1] : List (Fin 8)).map e8Node

theorem wordReflect_e8DeltaWord :
    ComponentClassification.CatLeafProof.wordReflect .E8 e8DeltaWord e8Delta = Pi.single (e8Node 0) 1 := by
  decide

abbrev rootPairE8 (K : Type) [Field K] (γ : Fin (Tag.rank .E8) → ℤ) :
    Subgroup (adjointGroup .E8 K) :=
  (e8Datum K).rootGroup γ ⊔ (e8Datum K).rootGroup (-γ)

theorem e8DeltaWord_mem : ∀ i ∈ e8DeltaWord, ∃ k : Fin 8, k ≠ 0 ∧ e8D8Node k = i := by
  decide

theorem eq_top_of_d8Chain_le_of_delta_le {K : Type} [Field K] (M : Subgroup (adjointGroup .E8 K))
    (hX : ⨆ k, e8D8Chain K k ≤ M) (hδ : rootPairE8 K e8Delta ≤ M) : M = ⊤ := by
  have hb : ∀ k, e8D8Chain K k ≤ M := fun k => (le_iSup (e8D8Chain K) k).trans hX
  have hUk : ∀ k : Fin 8, k ≠ 0 → rankOne (e8Datum K).rootGroup (e8D8Node k) ≤ M := fun k hk => by
    have hU : e8D8Chain K k = rankOne (e8Datum K).rootGroup (e8D8Node k) := by
      unfold e8D8Chain
      rw [ite_eq_right_iff.2 (fun h => absurd h hk)]
    rw [← hU]
    exact hb k
  have hn : weylWordElt .E8 K e8DeltaWord ∈ M := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨k, hk, rfl⟩ := e8DeltaWord_mem i hi
    exact hUk k hk (Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .E8) _)
  have h0 : rankOne (e8Datum K).rootGroup (e8Node 0) ≤ M := by
    have hmap := map_conj_weylWordElt_rootPair (K := K) e8DeltaWord isRoot_e8Delta
    rw [wordReflect_e8DeltaWord] at hmap
    change (e8Datum K).rootGroup (Pi.single (e8Node 0) 1) ⊔
      (e8Datum K).rootGroup (-Pi.single (e8Node 0) 1) ≤ M
    rw [← hmap]
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem hn (hδ hy)) (M.inv_mem hn)
  have hall : ⨆ i, rankOne (e8Datum K).rootGroup i ≤ M := by
    refine iSup_le fun i => ?_
    fin_cases i
    · exact h0
    · exact hUk 7 (by decide)
    · exact hUk 6 (by decide)
    · exact hUk 5 (by decide)
    · exact hUk 4 (by decide)
    · exact hUk 3 (by decide)
    · exact hUk 2 (by decide)
    · exact hUk 1 (by decide)
  rw [CFSG.ClassicalInvolution.RouteD.iSup_rankOne_eq_top (e8_isCTGroupDatum K)] at hall
  exact eq_top_iff.2 hall

end CFSG.HardMathSupport.Lang.AnisoE8
