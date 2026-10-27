module

import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.Adapters.RankTwoModelTransports
import CFSG.Blueprint.SourceClassicalTransportOrthogonal
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public noncomputable section

namespace CFSG.ClassicalModels

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports

theorem nonempty_ringEquiv_validIndex_fixedField (d : ValidLieTypeIndex) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = d.fieldOrder) : Nonempty (K ≃+* ↥d.fixedField) := by
  have _ : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  exact ⟨CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard
    (hK.trans (ValidLieTypeIndex.card_fixedField d).symm)⟩

theorem inCatalog_of_fixedField_model {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : (K : Type) → [Field K] → Subgroup (GL ι K))
    (hH : ∀ {K L : Type} [Field K] [Field L] (φ : K ≃+* L),
      (H K).map (glCongr φ).toMonoidHom = H L)
    (d : ValidLieTypeIndex) (eT : d.Group ≃* StatedProj (H ↥d.fixedField))
    {G : Type} [Group G] {K : Type} [Field K] [Finite K] (hK : Nat.card K = d.fieldOrder)
    (θ : G ≃* StatedProj (H K)) : CFSG.Assembly.InCatalog G := by
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField d K hK
  exact ⟨.lie d, ⟨(θ.trans (statedProjCongr (glCongr φ) (hH φ) (glCongr_statedScalars φ))).trans
    eT.symm⟩⟩

theorem statedClassicalModel_PSp_even_inCatalog (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .PSp n p f) (hn : 3 ≤ n) (hp2 : p = 2) :
    CFSG.Assembly.InCatalog G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  let q : PrimePower := ⟨p, f, hadm.1, by have := hadm.2.1; omega⟩
  have hv : (LieTypeIndex.B n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  exact inCatalog_of_fixedField_model (fun K _ => StatedSp n K)
    (fun φ => CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ n) ⟨.B n q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj n q hv hp2 hn) (by
      simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ

theorem statedClassicalModel_PSU_four_two_of_PSp_two_three {G : Type} [Group G]
    (h : StatedClassicalModel G .PSp 2 3 1) : StatedClassicalModel G .PSU 4 2 1 := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have _ : Finite (ZMod 3) := inferInstance
  let φ : K ≃+* ZMod 3 := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (by simp [hK])
  let e1 := statedProjCongr (glCongr (ι := Fin 2 ⊕ Fin 2) φ)
    (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 2) (glCongr_statedScalars φ)
  exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, CFSG.Blueprint.Fischer.K, inferInstance,
    inferInstance, CFSG.Fischer.Classification.Unitary.card_K,
    ⟨((θ.trans e1).trans CFSG.GH74.Exceptional.psp43EquivU2).trans
      CFSG.GH74.Exceptional.u2FourEquiv⟩⟩

theorem statedClassicalModel_PSp_two_three_inCatalog (G : Type) [Group G]
    (h : StatedClassicalModel G .PSp 2 3 1) : CFSG.Assembly.InCatalog G :=
  statedClassicalModel_PSU_inCatalog G 4 2 1 (statedClassicalModel_PSU_four_two_of_PSp_two_three h)

theorem statedClassicalModel_POmegaOdd_inCatalog (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .POmegaOdd n p f) : CFSG.Assembly.InCatalog G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn, hp2⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.B n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  exact inCatalog_of_fixedField_model (fun K _ => StatedOmega (StatedQuadOdd n K))
    (fun φ => CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadOdd_comp φ)) ⟨.B n q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q hv hp2 hn) (by
      simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ

theorem statedClassicalModel_POmegaPlus_inCatalog (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .POmegaPlus n p f) : CFSG.Assembly.InCatalog G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.D n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  exact inCatalog_of_fixedField_model (fun K _ => StatedOmega (StatedQuadPlus n K))
    (fun φ => CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)) ⟨.D n q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q hv) (by
      simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ

theorem statedClassicalModel_POmegaMinus_inCatalog (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .POmegaMinus n p f) : CFSG.Assembly.InCatalog G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.twistedD n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      n q hv
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField ⟨.twistedD n q, hv⟩ K (by
    simp [ValidLieTypeIndex.fieldOrder, q, hK])
  have _ : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD n q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n) (by omega)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
  let e1 := statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := n) (b := b) (c := c) φ rfl
        rfl))
    (glCongr_statedScalars φ)
  exact ⟨.lie ⟨.twistedD n q, hv⟩, ⟨((θ.trans e1).trans e2).trans eT.symm⟩⟩

theorem eq_three_one_of_pow_eq_three {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : p ^ f = 3) :
    p = 3 ∧ f = 1 := by
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := h ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h.trans (pow_one 3).symm)⟩

theorem inCatalog_of_statedClassicalModel (G : Type) [Group G]
    (t : StatedLieTag) (n p f : ℕ) (h : StatedClassicalModel G t n p f) :
    CFSG.Assembly.InCatalog G := by
  cases t
  case PSL => exact statedClassicalModel_PSL_inCatalog_all G n p f h
  case PSU => exact statedClassicalModel_PSU_inCatalog G n p f h
  case PSp =>
    obtain ⟨hp, hf, hn, -⟩ := h.1
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_one_of_pow_eq_three hp hf h3
        exact statedClassicalModel_PSp_two_three_inCatalog G h
      · exact statedClassicalModel_PSp_inCatalog G 2 p f h (Or.inr ⟨rfl, h3⟩)
    · by_cases hp2 : p = 2
      · exact statedClassicalModel_PSp_even_inCatalog G n p f h hn3 hp2
      · exact statedClassicalModel_PSp_inCatalog G n p f h (Or.inl ⟨hn3, hp2⟩)
  case POmegaOdd => exact statedClassicalModel_POmegaOdd_inCatalog G n p f h
  case POmegaPlus => exact statedClassicalModel_POmegaPlus_inCatalog G n p f h
  case POmegaMinus => exact statedClassicalModel_POmegaMinus_inCatalog G n p f h
  all_goals exact h.2.elim

end CFSG.ClassicalModels
