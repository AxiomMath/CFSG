module

public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open Matrix TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ClassicalModels

theorem nonempty_equiv_catalog_psu (G : Type) [Group G] (m p f : ℕ)
    (h : StatedClassicalModel G .PSU (m + 1) p f) :
    ∃ (hp : p.Prime) (hf : 0 < f)
      (hv : (LieTypeIndex.twistedA m ⟨p, f, hp, hf⟩).Valid),
      Nonempty (G ≃* (CFSGIndex.lie ⟨_, hv⟩).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hv := unitaryCatalog_index_valid (m + 1) p f hadm
  let _ : Fact p.Prime := ⟨hp⟩
  have hf' : 0 < f := by omega
  let q : PrimePower := ⟨p, f, hp, hf'⟩
  let L := GaloisField p (2 * f)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin (m + 1)) φ) (glCongr_statedSU φ (m + 1) (p ^ f))
    (glCongr_statedScalars φ)
  have hv' : (LieTypeIndex.twistedA m q).Valid := by simpa using hv
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv'
  exact ⟨hp, hf', hv', ⟨(e.trans e1).trans eT.symm⟩⟩

theorem isChevSimple_two_derived_G2 {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 ↥(commutator ↥(adjointGroup .G2 k)) := by
  have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk
  rcases hLie with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨hp, hf, hv, ⟨e⟩⟩ := nonempty_equiv_catalog_psu _ 2 3 1 hM
    have hDM : (commutator ↥(adjointGroup .G2 k)).map (adjointGroup .G2 k).subtype =
        ⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    let eD : ↥(commutator ↥(adjointGroup .G2 k)) ≃* ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ :=
      ((commutator ↥(adjointGroup .G2 k)).equivMapOfInjective _
        (adjointGroup .G2 k).subtype_injective).trans (MulEquiv.subgroupCongr hDM)
    exact Or.inr ⟨CFSGIndex.lie ⟨_, hv⟩, by simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev],
      ⟨eD.trans e⟩⟩
  all_goals exact absurd h0 (by norm_num)

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
