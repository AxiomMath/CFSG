module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.NotA6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof TauCeti CFSG.Yardstones.Md0ec50421ce4
  CFSG.Adapters.RankTwoModelTransports

set_option linter.unusedSectionVars false

theorem ringChar_eq_of_natCard_eq_pow {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) : ringChar K = p := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hq, hcard⟩ := FiniteField.card K (ringChar K)
  have hd : ringChar K ∣ p ^ f := by
    rw [← hK, Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self _ n.pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hd)


theorem isEmpty_alt6_of_lieModel_gen {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (hlarge : 4 ≤ lieSylowExponent t n * f) :
    IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨-, -, hfac⟩ := lieOrderFormulasInput G t n p f h.admissible h
  have hp : p.Prime := h.admissible.1
  have hcard : Nat.card G = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  rw [hcard] at hfac
  have hdvd : p ^ ((360 : ℕ).factorization p) ∣ 360 := Nat.ordProj_dvd 360 p
  rw [hfac] at hdvd
  exact not_pow_four_dvd_360 hp ((pow_dvd_pow p hlarge).trans hdvd)

private theorem nonempty_ringEquiv_fixedField_gen {K : Type} [Field K] [Fintype K]
    (d : ValidLieTypeIndex)
    (hK : Fintype.card K = d.fieldOrder) : Nonempty (K ≃+* ↥d.fixedField) := by
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let _ : Fintype d.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card (α := d.fixedField), ValidLieTypeIndex.card_fixedField]
    exact hK
  exact ⟨FiniteField.ringEquivOfCardEq hcard⟩

theorem isChevSimple_statedProj_plus_gen {K : Type} [Field K] [Fintype K] (n : ℕ)
    (hn : 4 ≤ n) :
    IsChevSimple (ringChar K) (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (LieTypeIndex.D n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField_gen (K := K) ⟨.D n q, hv⟩ (by
    simp [ValidLieTypeIndex.fieldOrder, q, hcard])
  exact Or.inl ⟨.lie ⟨.D n q, hv⟩, LieTypeIndex.characteristic_D n q,
    ⟨(statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)) (glCongr_statedScalars φ)).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q hv).symm⟩⟩

theorem lieModel_plus_chev {G : Type} [Group G] {n p f : ℕ}
    (h : LieModel G .POmegaPlus n p f) :
    IsChevSimple p G ∧ IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  have hadm := h.admissible
  have hn4 : 4 ≤ n := hadm.2.2
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  refine ⟨?_, isEmpty_alt6_of_lieModel_gen h ?_⟩
  · rcases h with ⟨-, hmod⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩ | ⟨hn0, ht, -⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
      haveI : Fintype K := Fintype.ofFinite K
      have hring : ringChar K = p := ringChar_eq_of_natCard_eq_pow hp hK hf
      have := isChevSimple_congr e.symm (isChevSimple_statedProj_plus_gen (K := K) n hn4)
      rwa [hring] at this
    all_goals simp [chevalleyExceptionalTags, reeTitsTags] at ht
  · simp only [lieSylowExponent]
    have h12 : 12 ≤ n * (n - 1) := by
      calc 12 = 4 * 3 := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 (by omega)
    nlinarith

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
