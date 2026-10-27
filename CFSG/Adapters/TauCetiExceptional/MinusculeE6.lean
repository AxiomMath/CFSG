module

public import CFSG.Adapters.TauCetiExceptional.MinusculeMatch
public import TauCeti.Algebra.Lie.E6.Minuscule.Generation

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti

@[expose] def e6Node : Fin 6 ≃ Fin (Tag.rank .E6) := finCongr rfl

theorem e6_cartan (i j : Fin 6) :
    E6Minuscule.weightTable.cartanMatrix i j = Tag.cartan .E6 (e6Node i) (e6Node j) := by
  have h : (CartanMatrix.E 6).transpose = Tag.cartanE 6 := by
    decide
  rw [E6Minuscule.weightTable_cartanMatrix, h]
  rfl

theorem e6Data_wt_zero (i : Fin 6) :
    e6Data.wt ((⟨0, by decide⟩ : Fin e6Data.d) : ℕ) (e6Node i) =
      E6Minuscule.weightTable.weight 0 i := by
  rw [E6Minuscule.weightTable_weight, DynkinType.e6MinusculeWeight_zero]
  revert i
  decide

@[expose] def e6Match :
    WeightMatch e6Data E6Minuscule.weightTable :=
  Classical.choice <| WeightMatch.nonempty e6Data_valid e6Node e6_cartan rfl e6Data_wt_zero
    fun a => by
      simpa only [E6Minuscule.weightTable_reflection] using
        DynkinType.exists_e6MinusculeReflections_eq a

theorem e6_rootSubgroupPoints_inl
    (A : Type*) [CommRing A] (i : Fin 6) (c : A) :
    (E6Minuscule.rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 27) A) =
      toMat e6Match.lab A (rootUnit e6Data_valid A (Pi.single (e6Match.node i) 1) c) := by
  refine Units.ext ?_
  rw [E6Minuscule.coe_rootSubgroupPoints_inl, toAdd_ofAdd]
  exact (e6Match.toMat_rootUnit_single e6Data_valid A i c).symm

theorem e6_rootSubgroupPoints_inr
    (A : Type*) [CommRing A] (i : Fin 6) (c : A) :
    (E6Minuscule.rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 27) A) =
      toMat e6Match.lab A (rootUnit e6Data_valid A (-Pi.single (e6Match.node i) 1) c) := by
  refine Units.ext ?_
  rw [E6Minuscule.coe_rootSubgroupPoints_inr, toAdd_ofAdd]
  exact (e6Match.toMat_rootUnit_neg_single e6Data_valid A i c).symm

theorem e6_weightTorusPoints
    (A : Type*) [CommRing A] (s : Fin 6 → Aˣ) :
    (E6Minuscule.weightTorusPoints A s : Matrix.GeneralLinearGroup (Fin 27) A) =
      toMat e6Match.lab A
        (diagUnit fun a => torusCharacter (s ∘ e6Match.node.symm) (e6Data.wt a)) := by
  refine Units.ext ?_
  rw [E6Minuscule.coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    diagGL_coe, e6Match.coe_toMat_diagUnit_torusCharacter A s]

theorem e6_weightTorusPoints_eq_torusElt
    (K : Type*) [Field K] (s : Fin 6 → Kˣ) :
    (E6Minuscule.weightTorusPoints K s : Matrix.GeneralLinearGroup (Fin 27) K) =
      toMat e6Match.lab K
        (torusElt e6Data_valid K (s ∘ e6Match.node.symm) : e6Data_valid.minGroup K) := by
  rw [e6_weightTorusPoints, coe_torusElt]

theorem map_toMat_e6_minGroup
    (K : Type*) [Field K] :
    (e6Data_valid.minGroup K).map (toMat e6Match.lab K).toMonoidHom =
      (E6Minuscule.elementarySubgroup K).map (E6Minuscule.points K).subtype := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine toMat_mem_of_simple e6Data_valid e6Match.lab K (fun i c => ?_) ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := e6Match.node.surjective i
    refine ⟨⟨_, E6Minuscule.rootSubgroupPoints_mem_elementarySubgroup K (.inl i)
      (Multiplicative.ofAdd c), ?_⟩, ⟨_, E6Minuscule.rootSubgroupPoints_mem_elementarySubgroup K
      (.inr i) (Multiplicative.ofAdd c), ?_⟩⟩
    · exact e6_rootSubgroupPoints_inl K i c
    · exact e6_rootSubgroupPoints_inr K i c
  · rw [Subgroup.map_le_iff_le_comap, E6Minuscule.elementarySubgroup_le_iff]
    rintro (i | i) u
    · refine ⟨rootUnit e6Data_valid K (Pi.single (e6Match.node i) 1) (Multiplicative.toAdd u),
        e6Data_valid.xu_mem K _ _, ?_⟩
      change toMat e6Match.lab K _ = _
      rw [← e6_rootSubgroupPoints_inl, ofAdd_toAdd]
      rfl
    · refine ⟨rootUnit e6Data_valid K (-Pi.single (e6Match.node i) 1) (Multiplicative.toAdd u),
        e6Data_valid.xu_mem K _ _, ?_⟩
      change toMat e6Match.lab K _ = _
      rw [← e6_rootSubgroupPoints_inr, ofAdd_toAdd]
      rfl

theorem e6_toMat_mem_points
    (K : Type*) [Field K] (g : e6Data_valid.minGroup K) :
    toMat e6Match.lab K g ∈ E6Minuscule.points K := by
  have h : toMat e6Match.lab K g ∈
      (E6Minuscule.elementarySubgroup K).map (E6Minuscule.points K).subtype := by
    rw [← map_toMat_e6_minGroup]
    exact ⟨g, g.2, rfl⟩
  obtain ⟨x, -, hx⟩ := h
  rw [← hx]
  exact x.2

end CFSG.TauCetiBridge.Minuscule
