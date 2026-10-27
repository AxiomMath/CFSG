module

public import CFSG.Adapters.TauCetiExceptional.MinusculeMatch
public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti

@[expose] def e7Node : Fin 7 ≃ Fin (Tag.rank .E7) := finCongr rfl

theorem e7_cartan (i j : Fin 7) :
    E7Minuscule.weightTable.cartanMatrix i j = Tag.cartan .E7 (e7Node i) (e7Node j) := by
  have h : CartanMatrix.E 7 = Tag.cartanE 7 := by
    decide
  rw [E7Minuscule.weightTable_cartanMatrix, h]
  rfl

theorem e7Data_wt_zero (i : Fin 7) :
    e7Data.wt ((⟨0, by decide⟩ : Fin e7Data.d) : ℕ) (e7Node i) =
      E7Minuscule.weightTable.weight 0 i := by
  rw [E7Minuscule.weightTable_weight, DynkinType.e7MinusculeWeight_zero]
  revert i
  decide

@[expose] def e7Match :
    WeightMatch e7Data E7Minuscule.weightTable :=
  Classical.choice <| WeightMatch.nonempty e7Data_valid e7Node e7_cartan rfl e7Data_wt_zero
    fun a => by
      simpa only [E7Minuscule.weightTable_reflection] using
        DynkinType.exists_e7MinusculeReflections_eq a

theorem e7_raisingMatrix (i : Fin 7) :
    E7Minuscule.raisingMatrix i = E7Minuscule.weightTable.raisingMatrix i := by
  ext a b
  rw [E7Minuscule.raisingMatrix_apply, MinusculeWeightTable.raisingMatrix_apply,
    E7Minuscule.weightTable_weight, E7Minuscule.weightTable_reflection]

theorem e7_loweringMatrix (i : Fin 7) :
    E7Minuscule.loweringMatrix i = E7Minuscule.weightTable.loweringMatrix i := by
  ext a b
  rw [E7Minuscule.loweringMatrix_apply, MinusculeWeightTable.loweringMatrix_apply,
    E7Minuscule.weightTable_weight, E7Minuscule.weightTable_reflection]

theorem e7_rootSubgroupPoints_inl
    (A : Type*) [CommRing A] (i : Fin 7) (c : A) :
    (E7Minuscule.rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 56) A) =
      toMat e7Match.lab A (rootUnit e7Data_valid A (Pi.single (e7Match.node i) 1) c) := by
  refine Units.ext ?_
  rw [E7Minuscule.coe_rootSubgroupPoints_inl, toAdd_ofAdd, e7_raisingMatrix]
  exact (e7Match.toMat_rootUnit_single e7Data_valid A i c).symm

theorem e7_rootSubgroupPoints_inr
    (A : Type*) [CommRing A] (i : Fin 7) (c : A) :
    (E7Minuscule.rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 56) A) =
      toMat e7Match.lab A (rootUnit e7Data_valid A (-Pi.single (e7Match.node i) 1) c) := by
  refine Units.ext ?_
  rw [E7Minuscule.coe_rootSubgroupPoints_inr, toAdd_ofAdd, e7_loweringMatrix]
  exact (e7Match.toMat_rootUnit_neg_single e7Data_valid A i c).symm

theorem e7_weightTorusPoints
    (A : Type*) [CommRing A] (s : Fin 7 → Aˣ) :
    (E7Minuscule.weightTorusPoints A s : Matrix.GeneralLinearGroup (Fin 56) A) =
      toMat e7Match.lab A
        (diagUnit fun a => torusCharacter (s ∘ e7Match.node.symm) (e7Data.wt a)) := by
  refine Units.ext ?_
  rw [E7Minuscule.coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    diagGL_coe, e7Match.coe_toMat_diagUnit_torusCharacter A s, E7Minuscule.weightTable_weight]

theorem e7_weightTorusPoints_eq_torusElt
    (K : Type*) [Field K] (s : Fin 7 → Kˣ) :
    (E7Minuscule.weightTorusPoints K s : Matrix.GeneralLinearGroup (Fin 56) K) =
      toMat e7Match.lab K
        (torusElt e7Data_valid K (s ∘ e7Match.node.symm) : e7Data_valid.minGroup K) := by
  rw [e7_weightTorusPoints, coe_torusElt]

@[expose] def e7Elementary (A : Type*) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 56) A) :=
  Subgroup.closure {g | ∃ (k : Fin 7 ⊕ Fin 7) (u : Multiplicative A),
    g = (E7Minuscule.rootSubgroupPoints k A u : Matrix.GeneralLinearGroup (Fin 56) A)}

theorem e7Elementary_le_points (A : Type*) [CommRing A] :
    e7Elementary A ≤ E7Minuscule.points A := by
  rw [e7Elementary, Subgroup.closure_le]
  rintro _ ⟨k, u, rfl⟩
  exact (E7Minuscule.rootSubgroupPoints k A u).2

theorem map_toMat_e7_minGroup
    (K : Type*) [Field K] :
    (e7Data_valid.minGroup K).map (toMat e7Match.lab K).toMonoidHom = e7Elementary K := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine toMat_mem_of_simple e7Data_valid e7Match.lab K (fun i c => ?_) ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := e7Match.node.surjective i
    refine ⟨Subgroup.subset_closure ⟨.inl i, Multiplicative.ofAdd c, ?_⟩,
      Subgroup.subset_closure ⟨.inr i, Multiplicative.ofAdd c, ?_⟩⟩
    · exact (e7_rootSubgroupPoints_inl K i c).symm
    · exact (e7_rootSubgroupPoints_inr K i c).symm
  · rw [e7Elementary, Subgroup.closure_le]
    rintro _ ⟨i | i, u, rfl⟩
    · refine ⟨rootUnit e7Data_valid K (Pi.single (e7Match.node i) 1) (Multiplicative.toAdd u),
        e7Data_valid.xu_mem K _ _, ?_⟩
      change toMat e7Match.lab K _ = _
      rw [← e7_rootSubgroupPoints_inl, ofAdd_toAdd]
    · refine ⟨rootUnit e7Data_valid K (-Pi.single (e7Match.node i) 1) (Multiplicative.toAdd u),
        e7Data_valid.xu_mem K _ _, ?_⟩
      change toMat e7Match.lab K _ = _
      rw [← e7_rootSubgroupPoints_inr, ofAdd_toAdd]

theorem e7_toMat_mem_points
    (K : Type*) [Field K] (g : e7Data_valid.minGroup K) :
    toMat e7Match.lab K g ∈ E7Minuscule.points K :=
  e7Elementary_le_points K (by rw [← map_toMat_e7_minGroup]; exact ⟨g, g.2, rfl⟩)

end CFSG.TauCetiBridge.Minuscule
