module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.ClassicalBridge
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof TauCeti CFSG.Yardstones.Md0ec50421ce4
  CFSG.Adapters.RankTwoModelTransports

set_option linter.unusedSectionVars false

private theorem nonempty_ringEquiv_fixedField_genB {K : Type} [Field K] [Fintype K]
    (d : ValidLieTypeIndex)
    (hK : Fintype.card K = d.fieldOrder) : Nonempty (K ≃+* ↥d.fixedField) := by
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let _ : Fintype d.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card (α := d.fixedField), ValidLieTypeIndex.card_fixedField]
    exact hK
  exact ⟨FiniteField.ringEquivOfCardEq hcard⟩

theorem isChevSimple_statedProj_odd_gen {K : Type} [Field K] [Fintype K] (n : ℕ) (hn : 3 ≤ n)
    (h2 : ringChar K ≠ 2) :
    IsChevSimple (ringChar K) (StatedProj (StatedOmega (StatedQuadOdd n K))) := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (LieTypeIndex.B n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField_genB (K := K) ⟨.B n q, hv⟩ (by
    simp [ValidLieTypeIndex.fieldOrder, q, hcard])
  exact Or.inl ⟨.lie ⟨.B n q, hv⟩, LieTypeIndex.characteristic_B n q,
    ⟨(statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadOdd_comp φ)) (glCongr_statedScalars φ)).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q hv h2
        hn).symm⟩⟩


theorem lieModel_podd_chev {G : Type} [Group G] {n p f : ℕ}
    (h : LieModel G .POmegaOdd n p f) :
    IsChevSimple p G ∧ IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  have hadm := h.admissible
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hp2 : p ≠ 2 := hadm.2.2.2
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  refine ⟨?_, isEmpty_alt6_of_lieModel_gen h ?_⟩
  · rcases h with ⟨-, hmod⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
      haveI : Fintype K := Fintype.ofFinite K
      have hring : ringChar K = p := ringChar_eq_of_natCard_eq_pow hp hK hf
      have := isChevSimple_congr e.symm
        (isChevSimple_statedProj_odd_gen (K := K) n hn3 (by rw [hring]; exact hp2))
      rwa [hring] at this
    all_goals simp [chevalleyExceptionalTags, reeTitsTags] at ht
  · simp only [lieSylowExponent]
    have h9 : 9 ≤ n ^ 2 := by nlinarith
    nlinarith

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
