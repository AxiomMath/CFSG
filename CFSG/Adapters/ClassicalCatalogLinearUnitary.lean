module

public import CFSG.Adapters.LinearCatalog
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedReverse
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

noncomputable section

namespace CFSG.ClassicalModels

open Matrix TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

theorem unitaryCatalog_index_valid (n p f : ℕ) (h : StatedLieAdmissible .PSU n p f) :
    (LieTypeIndex.twistedA (n - 1) ⟨p, f, h.1, by have hf := h.2.1; omega⟩).Valid := by
  obtain ⟨hp, hf, hn, h32⟩ := h
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [PrimePower.card_def, not_false_eq_true, and_true]
  refine ⟨by omega, fun hr => ?_⟩
  have hn3 : n = 3 := by omega
  have hq2 : p ^ f ≠ 2 := fun hq => h32 (by rw [hn3, hq])
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  omega

theorem statedClassicalModel_PSU_inCatalog (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .PSU n p f) : CFSG.Assembly.InCatalog G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hv := unitaryCatalog_index_valid n p f hadm
  let _ : Fact p.Prime := ⟨hp⟩
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  let L := GaloisField p (2 * f)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin n) φ) (glCongr_statedSU φ n (p ^ f))
    (glCongr_statedScalars φ)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hv' : (LieTypeIndex.twistedA m q).Valid := by simpa using hv
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv'
  exact ⟨.lie ⟨_, hv'⟩, ⟨(e.trans e1).trans eT.symm⟩⟩

theorem statedClassicalModel_PSL_two_inCatalog
    (G : Type) [Group G] (p f : ℕ)
    (h : StatedClassicalModel G .PSL 2 p f) : CFSG.Assembly.InCatalog G := by
  by_cases h45 : p ^ f = 4 ∨ p ^ f = 5
  · exact statedClassicalModel_PSL_inCatalog_of_card_four_or_five G p f h h45
  by_cases h9 : p ^ f = 9
  · obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
    let _ := hfield
    let _ := hfinite
    let _ : Fintype K := Fintype.ofFinite K
    have hK9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK, h9]
    obtain ⟨e6⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism K hK9
    exact ⟨.alternating 6 (Nat.le_succ 5),
      ⟨(e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans e6⟩⟩
  refine statedClassicalModel_PSL_inCatalog_of_not_duplicate G 2 p f h ?_
  rw [LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [PrimePower.card_def]
  omega

theorem statedClassicalModel_PSL_inCatalog (G : Type) [Group G] (n p f : ℕ) (hn : 3 ≤ n)
    (h : StatedClassicalModel G .PSL n p f) (h32 : (n, p ^ f) ≠ (3, 2))
    (h42 : (n, p ^ f) ≠ (4, 2)) : CFSG.Assembly.InCatalog G := by
  refine statedClassicalModel_PSL_inCatalog_of_not_duplicate G n p f h ?_
  rw [LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [PrimePower.card_def]
  intro hdup
  rcases hdup with ⟨hr, -⟩ | ⟨hr, hq⟩ | ⟨hr, hq⟩
  · omega
  · exact h32 (by rw [show n = 3 by omega, hq])
  · exact h42 (by rw [show n = 4 by omega, hq])

theorem eq_two_one_of_pow_eq_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : p ^ f = 2) :
    p = 2 ∧ f = 1 := by
  have hp2 : p = 2 := by
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have := hp.two_le
    omega
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective le_rfl (h.trans (pow_one 2).symm)⟩

theorem statedClassicalModel_PSL_inCatalog_all
    (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .PSL n p f) : CFSG.Assembly.InCatalog G := by
  have hp : p.Prime := h.1.1
  have hf : 1 ≤ f := h.1.2.1
  have hn : 2 ≤ n := h.1.2.2.1
  have hmem : (StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · exact statedClassicalModel_PSL_two_inCatalog G p f h
  by_cases h32 : (n, p ^ f) = (3, 2)
  · obtain ⟨rfl, hq⟩ := Prod.mk.inj h32
    obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp hf hq
    rcases CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism G
        (Or.inl ⟨hmem, h⟩) with ⟨-, h7⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact statedClassicalModel_PSL_two_inCatalog G 7 1 h7
    all_goals exact absurd h0 (by norm_num)
  by_cases h42 : (n, p ^ f) = (4, 2)
  · obtain ⟨rfl, hq⟩ := Prod.mk.inj h42
    obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp hf hq
    obtain ⟨e⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
      (Or.inl ⟨hmem, h⟩)
    have h8 : 5 ≤ 8 := by norm_num
    exact ⟨.alternating 8 h8, ⟨e⟩⟩
  exact statedClassicalModel_PSL_inCatalog G n p f hn3 h h32 h42

theorem statedClassicalModel_PSL_or_PSU_inCatalog
    (G : Type) [Group G] (t : StatedLieTag)
    (n p f : ℕ) (ht : t = .PSL ∨ t = .PSU) (h : StatedClassicalModel G t n p f) :
    CFSG.Assembly.InCatalog G := by
  rcases ht with rfl | rfl
  · exact statedClassicalModel_PSL_inCatalog_all G n p f h
  · exact statedClassicalModel_PSU_inCatalog G n p f h

theorem statedClassicalModel_PSp_inCatalog (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .PSp n p f)
    (hcases : (3 ≤ n ∧ p ≠ 2) ∨ (n = 2 ∧ p ^ f ≠ 3)) : CFSG.Assembly.InCatalog G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  let _ : Fintype K := Fintype.ofFinite K
  rcases hcases with ⟨hn3, hp2⟩ | ⟨rfl, hq3⟩
  · have hv : (LieTypeIndex.C n q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨⟨hn3, hp2⟩, not_false⟩
    let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.C n q, hv⟩)
    have _ : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    let _ : Fintype Fd := Fintype.ofFinite Fd
    have hcard : Fintype.card K = Fintype.card Fd := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
        ValidLieTypeIndex.card_fixedField]
      simp [ValidLieTypeIndex.fieldOrder, q]
    let φ : K ≃+* Fd := FiniteField.ringEquivOfCardEq hcard
    let e1 := CFSG.ComponentClassification.ClassicalModelStatedBridge.statedProjCongr
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv (Fin n ⊕ Fin n) φ)
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedSp n φ)
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedScalars φ)
    let eT := CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj n q hv
    exact ⟨.lie ⟨_, hv⟩, ⟨(θ.trans e1).trans eT.symm⟩⟩
  · have hq2 : p ^ f ≠ 2 := fun h2 => hadm.2.2.2 (by rw [h2])
    have hv : (LieTypeIndex.B 2 q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [PrimePower.card_def, true_and, le_refl]
      exact ⟨hq2, hq3⟩
    let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)
    have _ : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    let _ : Fintype Fd := Fintype.ofFinite Fd
    have hcard : Fintype.card K = Fintype.card Fd := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
        ValidLieTypeIndex.card_fixedField]
      simp [ValidLieTypeIndex.fieldOrder, q]
    let φ : K ≃+* Fd := FiniteField.ringEquivOfCardEq hcard
    let e1 := CFSG.ComponentClassification.ClassicalModelStatedBridge.statedProjCongr
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) φ)
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedSp 2 φ)
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedScalars φ)
    let eT := CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv
    exact ⟨.lie ⟨_, hv⟩, ⟨(θ.trans e1).trans eT.symm⟩⟩

end CFSG.ClassicalModels
