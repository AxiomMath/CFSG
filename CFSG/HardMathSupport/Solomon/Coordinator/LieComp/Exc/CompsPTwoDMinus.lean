module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.ClassicalBridge
import CFSG.Blueprint.SourceClassicalTransportOrthogonal
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof TauCeti CFSG.Yardstones.Md0ec50421ce4
  CFSG.Adapters.RankTwoModelTransports

set_option linter.unusedSectionVars false

private theorem nonempty_ringEquiv_fixedField_genM {K : Type} [Field K] [Fintype K]
    (d : ValidLieTypeIndex)
    (hK : Fintype.card K = d.fieldOrder) : Nonempty (K ≃+* ↥d.fixedField) := by
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let _ : Fintype d.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card (α := d.fixedField), ValidLieTypeIndex.card_fixedField]
    exact hK
  exact ⟨FiniteField.ringEquivOfCardEq hcard⟩

theorem isChevSimple_statedProj_minus_gen {K : Type} [Field K] [Fintype K] (n : ℕ) (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsChevSimple (ringChar K) (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (LieTypeIndex.twistedD n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      n q hv
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField_genM (K := K) ⟨.twistedD n q, hv⟩ (by
    simp [ValidLieTypeIndex.fieldOrder, q, hcard])
  haveI : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD n q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n) (by omega)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
  let e1 := statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := n) (b := b) (c := c) φ rfl
        rfl))
    (glCongr_statedScalars φ)
  exact Or.inl ⟨.lie ⟨.twistedD n q, hv⟩, LieTypeIndex.characteristic_twistedD n q,
    ⟨(e1.trans e2).trans eT.symm⟩⟩


theorem lieModel_pominus_chev {G : Type} [Group G] {n p f : ℕ}
    (h : LieModel G .POmegaMinus n p f) :
    IsChevSimple p G ∧ IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  have hadm := h.admissible
  have hn4 : 4 ≤ n := hadm.2.2
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  refine ⟨?_, isEmpty_alt6_of_lieModel_gen h ?_⟩
  · rcases h with ⟨-, hmod⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩
    · obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hmod
      haveI : Fintype K := Fintype.ofFinite K
      have hring : ringChar K = p := ringChar_eq_of_natCard_eq_pow hp hK hf
      have := isChevSimple_congr e.symm (isChevSimple_statedProj_minus_gen (K := K) n hn4 hirr)
      rwa [hring] at this
    all_goals simp [chevalleyExceptionalTags, reeTitsTags] at ht
  · simp only [lieSylowExponent]
    have h12 : 12 ≤ n * (n - 1) := by
      calc 12 = 4 * 3 := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 (by omega)
    nlinarith

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
