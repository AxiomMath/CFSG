module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusBlocks
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.LeviGeneric
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSixB
public import CFSG.RankThree.PartOne.K159.Klein
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section P141
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbedding.LeviBlock CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding TauCeti


theorem isClassicalTwoOrG2_of_statedPOmegaPlus {G : Type} [Group G] {k f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus k 2 f) : IsClassicalTwoOrG2 G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn⟩ := hadm
  let q : PrimePower := ⟨2, f, hp, by omega⟩
  have hv : (LieTypeIndex.D k q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  exact isClassicalTwoOrG2_of_fixedField_model (fun K _ => StatedOmega (StatedQuadPlus k K))
    (fun φ => CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)) ⟨.D k q, hv⟩ rfl
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid k q hv) (by
      simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ

theorem isChevComponent_spinPlus {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hk : 4 ≤ k) :
    CFSG.IsQuasisimple (spinGroup (quadPlus k F)) ∧
      IsClassicalTwoOrG2 (spinGroup (quadPlus k F) ⧸ Subgroup.center (spinGroup (quadPlus k F))) := by
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  refine ⟨isQuasisimple_spinGroup_quadPlus (by omega), ?_⟩
  exact isClassicalTwoOrG2_of_statedPOmegaPlus
    (statedClassicalModel_spin_quadPlus ⟨Nat.prime_two, hf1, hk⟩ hfcard)



section ABlockDecomp

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n) {ι : Type} [Fintype ι]
  [DecidableEq ι] (ch : DBlk n ι)

theorem ablock_decomp {Y : Type} [Group Y]
    (π : spinGroup (quadPlus n F) →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center (spinGroup (quadPlus n F)))
    (A : Subgroup (spinGroup (quadPlus n F)))
    (hA : A ≤ Subgroup.normalizer ((leviM (plusDatum n F hn) ch.nodes : Subgroup _) : Set _))
    (hcard : 2 ≤ Fintype.card ι) :
    ∃ E C : Subgroup (spinGroup (quadPlus n F)),
      E ≤ leviM (plusDatum n F hn) ch.nodes ∧ C ≤ leviM (plusDatum n F hn) ch.nodes ∧
      leviM (plusDatum n F hn) ch.nodes ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧
      E ≤ Subgroup.normalizer (C : Set (spinGroup (quadPlus n F))) ∧
      A ≤ Subgroup.normalizer (E : Set (spinGroup (quadPlus n F))) ∧
      A ≤ Subgroup.normalizer (C : Set (spinGroup (quadPlus n F))) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) := by
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  let e1 : Matrix.SpecialLinearGroup (Fin (Fintype.card ι)) F ≃*
      ↥(leviM (plusDatum n F hn) ch.nodes) :=
    (slReindexEquiv (Fintype.equivFin ι)).symm.trans (chEquiv hn ch)
  by_cases h3 : 3 ≤ Fintype.card ι
  · exact decomp_of_chev π hker A _ hA e1 (isChevComponent_sl (Or.inl h3))
  · have h2 : Fintype.card ι = 2 := by omega
    by_cases hf : f = 1
    ·
      subst hf
      have : Fintype F := Fintype.ofFinite F
      have hF2 : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hfcard]; norm_num
      have hsolv : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin (Fintype.card ι)) F) := by
        rw [h2]; exact CFSG.Quasithin.R3c21.S0.isSolvable_sl2_of_card_two hF2
      haveI := hsolv
      exact decomp_so π A _ hA (Group.isSolvable_of_isSolvable_injective
        (f := e1.symm.toMonoidHom) e1.symm.injective)
    · have h4 : 4 ≤ Nat.card F := by
        rw [hfcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact decomp_of_chev π hker A _ hA e1 (isChevComponent_sl (Or.inr ⟨h2, h4⟩))

end ABlockDecomp


end P141

section P144
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding TauCeti


section D3

open CFSG.ComponentClassification.CatLeafProof.KleinSix

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem spinMatrix_injective {n : ℕ} : Function.Injective (spinMatrix (quadPlus n F)) := by
  intro x y h
  have hk := ker_spinMatrix_quadPlus_eq_bot (n := n) (K := F) CharTwo.two_eq_zero
  have : x⁻¹ * y ∈ (spinMatrix (quadPlus n F)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [hk, Subgroup.mem_bot] at this
  exact inv_mul_eq_one.mp this

theorem rhoGL_injective' : Function.Injective (rhoGL (K := F)) := by
  obtain ⟨hs, -⟩ := CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := F)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (rhoGL (K := F)).ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    have hg : transv (0 : Fin 4) 2 (by decide) (1 : F) ∈ (rhoGL (K := F)).ker := by
      rw [h]; exact Subgroup.mem_top _
    have h1 : rhoGL (transv (0 : Fin 4) 2 (by decide) (1 : F)) = 1 := hg
    have h2 := congrArg (fun f => f (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → F) (Sum.inl 2)) h1
    rw [rhoGL_apply] at h2
    simp [CFSG.ComponentClassification.CatLeafProof.KleinSix.coordsOf, skewOf, CFSG.LocalAnalysis.antiMat, transv, Matrix.transvection,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply] at h2


theorem rhoGL_range_eq : (rhoGL (K := F)).range = CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadPlus 3 F) := by
  refine le_antisymm ?_ elementaryGroup_le_range
  obtain ⟨-, hperf⟩ := CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := F)
  have hperf' : commutator (Matrix.SpecialLinearGroup (Fin 4) F) = ⊤ := Group.isPerfect_def.mp hperf
  calc (rhoGL (K := F)).range = (commutator (Matrix.SpecialLinearGroup (Fin 4) F)).map rhoGL := by
        rw [hperf', ← MonoidHom.range_eq_map]
    _ = ⁅(rhoGL (K := F)).range, (rhoGL (K := F)).range⁆ := map_commutator_eq (f := rhoGL)
    _ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 F),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 F)⁆ :=
        Subgroup.commutator_mono range_le_orthogonalGroup range_le_orthogonalGroup
    _ = CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadPlus 3 F) :=
        CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (by norm_num)

theorem spinAction_injective : Function.Injective (spinAction (quadPlus 3 F)) := by
  intro x y h
  apply spinMatrix_injective
  rw [spinMatrix_eq_comp, MonoidHom.comp_apply, MonoidHom.comp_apply, h]

@[expose] noncomputable def spinPlusThreeEquiv : spinGroup (quadPlus 3 F) ≃* Matrix.SpecialLinearGroup (Fin 4) F :=
  (MonoidHom.ofInjective (spinAction_injective (F := F))).trans
    ((MulEquiv.subgroupCongr ((range_spinAction_quadPlus (le_refl 3)).trans
      rhoGL_range_eq.symm)).trans (MonoidHom.ofInjective (rhoGL_injective' (F := F))).symm)


theorem chev_spinPlus_three :
    CFSG.IsQuasisimple (spinGroup (quadPlus 3 F)) ∧
      IsClassicalTwoOrG2 (spinGroup (quadPlus 3 F) ⧸ Subgroup.center (spinGroup (quadPlus 3 F))) := by
  obtain ⟨h1, h2⟩ := isChevComponent_sl (F := F) (k := 4) (Or.inl (by norm_num))
  let e : Matrix.SpecialLinearGroup (Fin 4) F ≃* spinGroup (quadPlus 3 F) := (spinPlusThreeEquiv (F := F)).symm
  exact ⟨isQuasisimple_of_mulEquiv e h1,
    isClassicalTwoOrG2_of_mulEquiv (CFSG.Quasithin.SmithC27.quotCenterCongr e) h2⟩

end D3


end P144

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
