module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetNondeg
public import CFSG.LieType.Chevalley.WeylRoots
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetRootsAux
import CFSG.Mathlib.Decide.Bounded
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega.E7RootSet

open Certificates.OmegaSevenMax CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def redV (v : Fin Tag.E7.rank → ℤ) : V := fun i => ((v i : ℤ) : ZMod 3)

open CFSG.StandardType

private def e7RootsP1_certCodes : List ℕ :=
  e7RootsP1_certVecs.map fun v => encV (redV v)

open scoped CFSG.Decide.Bounded in
private theorem e7RootsP1_mem_all :
    ∀ c ∈ List.range 2187, c ∈ rootList ↔ c ∈ e7RootsP1_certCodes := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e7RootsP1_rootList_lt : ∀ c ∈ rootList, c < 2187 := by
  decide +kernel

private theorem e7RootsP1_certCodes_lt : ∀ c ∈ e7RootsP1_certCodes, c < 2187 := by
  intro c hc
  simp only [e7RootsP1_certCodes, List.mem_map, Function.comp_apply] at hc
  obtain ⟨v, -, rfl⟩ := hc
  exact encV_lt (redV v)

private theorem e7RootsP1_decSet_eq :
    decSet rootList = decSet e7RootsP1_certCodes := by
  apply decSet_eq_of_bitsOf
  rw [bitsOf_eq_iff]
  intro c
  constructor
  · intro hc
    exact (e7RootsP1_mem_all c (List.mem_range.2 (e7RootsP1_rootList_lt c hc))).1 hc
  · intro hc
    exact (e7RootsP1_mem_all c (List.mem_range.2 (e7RootsP1_certCodes_lt c hc))).2 hc

private theorem e7RootsP1_decSet_tables :
    decSet (tables ()).roots = decSet e7RootsP1_certCodes :=
  e7RootsP1_decSet_eq

private theorem e7RootsP1_set_eq :
    ({α : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 α} : Set _) = ↑e7RootsP1_certVecs.toFinset := by
  ext v
  rw [Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset]
  exact e7RootsP1_isRoot_iff v

private theorem e7RootsP1_certCodes_image :
    (decSet e7RootsP1_certCodes : Finset V) = e7RootsP1_certVecs.toFinset.image redV := by
  ext x
  rw [mem_decSet, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [e7RootsP1_certCodes, List.mem_map] at hc
    obtain ⟨v, hv, rfl⟩ := hc
    exact ⟨v, by simpa using hv, by rw [decV_encV]⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨encV (redV v), ?_, ?_⟩
    · rw [e7RootsP1_certCodes, List.mem_map]
      exact ⟨v, List.mem_toFinset.1 hv, rfl⟩
    · rw [decV_encV]

open scoped CFSG.Decide.Bounded in
private theorem e7RootsP1_inj :
    ∀ v ∈ e7RootsP1_certVecs, ∀ w ∈ e7RootsP1_certVecs, redV v = redV w → v = w := by
  decide +kernel

theorem rootSet_eq_image : (↑rootSet : Set V) = redV '' {α | IsRoot Tag.E7 α} := by
  have h1 : (↑rootSet : Set V) = ↑(decSet e7RootsP1_certCodes) := by
    show (↑(decSet (tables ()).roots) : Set V) = ↑(decSet e7RootsP1_certCodes)
    rw [e7RootsP1_decSet_tables]
  rw [h1, e7RootsP1_set_eq, e7RootsP1_certCodes_image, Finset.coe_image]

theorem redV_injOn_roots : Set.InjOn redV {α | IsRoot Tag.E7 α} := by
  rw [e7RootsP1_set_eq]
  intro v hv w hw h
  rw [Finset.mem_coe, List.mem_toFinset] at hv hw
  exact e7RootsP1_inj v hv w hw h

theorem card_rootSet : rootSet.card = 126 := by
  have h1 : rootSet = decSet e7RootsP1_certCodes := by
    show decSet (tables ()).roots = decSet e7RootsP1_certCodes
    rw [e7RootsP1_decSet_tables]
  rw [h1]
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega.E7RootSet

end
