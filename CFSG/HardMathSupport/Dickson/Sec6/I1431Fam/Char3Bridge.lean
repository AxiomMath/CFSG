module

public import CFSG.Adapters.TauCetiExceptional.Interface
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.Blueprint.SourceClassicalTransportOrthogonal
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank TauCeti

@[expose] def TauCetiDuplicate (t : StatedLieTag) (n p f : ℕ) : Prop :=
  (t = .PSL ∧ ((n = 2 ∧ (p ^ f = 4 ∨ p ^ f = 5 ∨ p ^ f = 9)) ∨ (n = 3 ∧ p ^ f = 2) ∨
    (n = 4 ∧ p ^ f = 2))) ∨ (t = .PSp ∧ n = 2 ∧ p ^ f = 3)

theorem not_tauCetiDuplicate_three_iff {t : StatedLieTag} {n f : ℕ} :
    ¬ TauCetiDuplicate t n 3 f ↔
      ¬ (t = .PSL ∧ n = 2 ∧ f = 2) ∧ ¬ (t = .PSp ∧ n = 2 ∧ f = 1) := by
  have h3 : ∀ g : ℕ, (3 ^ g = 4 ∨ 3 ^ g = 5 ∨ 3 ^ g = 2) → False := by
    intro g hg
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · simp at hg
    · have hdvd : 3 ∣ 3 ^ g := dvd_pow_self 3 (by omega)
      omega
  have h9 : ∀ g : ℕ, 3 ^ g = 9 ↔ g = 2 := fun g =>
    ⟨fun h => Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      (h.trans (by norm_num : (9 : ℕ) = 3 ^ 2)), fun h => by rw [h]; norm_num⟩
  have h31 : ∀ g : ℕ, 3 ^ g = 3 ↔ g = 1 := fun g =>
    ⟨fun h => Nat.pow_right_injective (by norm_num) (h.trans (pow_one 3).symm),
      fun h => by rw [h]; norm_num⟩
  unfold TauCetiDuplicate
  constructor
  · intro h
    refine ⟨fun ⟨ht, hn, hf⟩ => h (Or.inl ⟨ht, Or.inl ⟨hn, Or.inr (Or.inr ((h9 f).2 hf))⟩⟩),
      fun ⟨ht, hn, hf⟩ => h (Or.inr ⟨ht, hn, (h31 f).2 hf⟩)⟩
  · rintro ⟨h1, h2⟩ (⟨ht, ⟨hn, h | h | h⟩ | ⟨hn, h⟩ | ⟨hn, h⟩⟩ | ⟨ht, hn, h⟩)
    · exact h3 f (Or.inl h)
    · exact h3 f (Or.inr (Or.inl h))
    · exact h1 ⟨ht, hn, (h9 f).1 h⟩
    · exact h3 f (Or.inr (Or.inr h))
    · exact h3 f (Or.inr (Or.inr h))
    · exact h2 ⟨ht, hn, (h31 f).1 h⟩

section Classical

open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr
  glCongr_statedSp glCongr_statedSU)
open CFSG.ClassicalInvolution.Upgrade (fieldIsoOfCard map_statedOmega statedQuadOdd_comp
  statedQuadPlus_comp statedQuadMinus_comp irreducible_map)

private theorem t6char3_equiv_of_fixedField_model {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : (K : Type) → [Field K] → Subgroup (GL ι K))
    (hH : ∀ {K L : Type} [Field K] [Field L] (φ : K ≃+* L),
      (H K).map (glCongr φ).toMonoidHom = H L)
    (d : ValidLieTypeIndex) (eT : d.Group ≃* StatedProj (H ↥d.fixedField))
    {G : Type} [Group G] {K : Type} [Field K] [Finite K] (hK : Nat.card K = d.fieldOrder)
    (θ : G ≃* StatedProj (H K)) : Nonempty (G ≃* d.Group) := by
  have _ : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let φ : K ≃+* ↥d.fixedField :=
    fieldIsoOfCard (hK.trans (ValidLieTypeIndex.card_fixedField d).symm)
  exact ⟨(θ.trans (statedProjCongr (glCongr φ) (hH φ) (glCongr_statedScalars φ))).trans eT.symm⟩

theorem t6char3_index_psl {P : Type} [Group P] {n p f : ℕ} (h : StatedClassicalModel P .PSL n p f)
    (hdup : ¬ ((n = 2 ∧ (p ^ f = 4 ∨ p ^ f = 5 ∨ p ^ f = 9)) ∨ (n = 3 ∧ p ^ f = 2) ∨
      (n = 4 ∧ p ^ f = 2))) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (P ≃* (CFSGIndex.lie d).Group) := by
  have hp : p.Prime := h.1.1
  have hf : 1 ≤ f := h.1.2.1
  have hn : 2 ≤ n := h.1.2.2.1
  let q : PrimePower := ⟨p, f, hp, hf⟩
  let _ : Fact p.Prime := ⟨hp⟩
  have hdup' : ¬ (LieTypeIndex.A (n - 1) q).IsDuplicateRepresentative := by
    rw [LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [PrimePower.card_def, q]
    intro hd
    apply hdup
    omega
  have hv := CFSG.ClassicalModels.linearCatalog_index_valid n p f h.1 hdup'
  obtain ⟨K, hfield, hfinite, hKcard, e⟩ := h.2
  let _ := hfield
  let _ := hfinite
  obtain ⟨e⟩ := e
  let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K n p f (by omega) hKcard
  have hdim : n - 1 + 1 = n := by omega
  have eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL (n - 1) q hv
  have eC' : (ValidLieTypeIndex.Group ⟨LieTypeIndex.A (n - 1) q, hv⟩) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f) := by
    rw [hdim] at eC
    exact eC
  exact ⟨⟨LieTypeIndex.A (n - 1) q, hv⟩, LieTypeIndex.characteristic_A (n - 1) q,
    ⟨(e.trans eK).trans eC'.symm⟩⟩

private theorem t6char3_unitary_index_valid (n p f : ℕ) (h : StatedLieAdmissible .PSU n p f) :
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

theorem t6char3_index_psu {P : Type} [Group P] {n p f : ℕ} (h : StatedClassicalModel P .PSU n p f) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (P ≃* (CFSGIndex.lie d).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hv := t6char3_unitary_index_valid n p f hadm
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
  exact ⟨⟨_, hv'⟩, LieTypeIndex.characteristic_twistedA m q, ⟨(e.trans e1).trans eT.symm⟩⟩

theorem t6char3_index_psp {P : Type} [Group P] {n p f : ℕ} (h : StatedClassicalModel P .PSp n p f)
    (hdup : ¬ (n = 2 ∧ p ^ f = 3)) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (P ≃* (CFSGIndex.lie d).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · have hq2 : p ^ f ≠ 2 := fun h2 => hadm.2.2.2 (by rw [h2])
    have hq3 : p ^ f ≠ 3 := fun h3 => hdup ⟨rfl, h3⟩
    have hv : (LieTypeIndex.B 2 q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [PrimePower.card_def, true_and, le_refl]
      exact ⟨hq2, hq3⟩
    obtain ⟨e⟩ := t6char3_equiv_of_fixedField_model (fun K _ => StatedSp 2 K)
      (fun φ => glCongr_statedSp φ 2) ⟨.B 2 q, hv⟩
      (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
    exact ⟨⟨.B 2 q, hv⟩, LieTypeIndex.characteristic_B 2 q, ⟨e⟩⟩
  · by_cases hp2 : p = 2
    · have hv : (LieTypeIndex.B n q).Valid := by
        rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
          LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
      obtain ⟨e⟩ := t6char3_equiv_of_fixedField_model (fun K _ => StatedSp n K)
        (fun φ => glCongr_statedSp φ n) ⟨.B n q, hv⟩
        (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj n q hv hp2 hn3)
        (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
      exact ⟨⟨.B n q, hv⟩, LieTypeIndex.characteristic_B n q, ⟨e⟩⟩
    · have hv : (LieTypeIndex.C n q).Valid := by
        rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
          LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨⟨hn3, hp2⟩, not_false⟩
      obtain ⟨e⟩ := t6char3_equiv_of_fixedField_model (fun K _ => StatedSp n K)
        (fun φ => glCongr_statedSp φ n) ⟨.C n q, hv⟩
        (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj n q hv)
        (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
      exact ⟨⟨.C n q, hv⟩, LieTypeIndex.characteristic_C n q, ⟨e⟩⟩

theorem t6char3_index_pomegaOdd {P : Type} [Group P] {n p f : ℕ}
    (h : StatedClassicalModel P .POmegaOdd n p f) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (P ≃* (CFSGIndex.lie d).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn, hp2⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.B n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  obtain ⟨e⟩ := t6char3_equiv_of_fixedField_model (fun K _ => StatedOmega (StatedQuadOdd n K))
    (fun φ => map_statedOmega φ (statedQuadOdd_comp φ)) ⟨.B n q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q hv hp2 hn)
    (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
  exact ⟨⟨.B n q, hv⟩, LieTypeIndex.characteristic_B n q, ⟨e⟩⟩

theorem t6char3_index_pomegaPlus {P : Type} [Group P] {n p f : ℕ}
    (h : StatedClassicalModel P .POmegaPlus n p f) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (P ≃* (CFSGIndex.lie d).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.D n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨e⟩ := t6char3_equiv_of_fixedField_model (fun K _ => StatedOmega (StatedQuadPlus n K))
    (fun φ => map_statedOmega φ (statedQuadPlus_comp φ)) ⟨.D n q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q hv)
    (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
  exact ⟨⟨.D n q, hv⟩, LieTypeIndex.characteristic_D n q, ⟨e⟩⟩

theorem t6char3_index_pomegaMinus {P : Type} [Group P] {n p f : ℕ}
    (h : StatedClassicalModel P .POmegaMinus n p f) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (P ≃* (CFSGIndex.lie d).Group) := by
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
  obtain ⟨φ⟩ : Nonempty (K ≃+* ↥(ValidLieTypeIndex.fixedField ⟨.twistedD n q, hv⟩)) := by
    have _ : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD n q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    exact ⟨fieldIsoOfCard (by
      rw [ValidLieTypeIndex.card_fixedField]
      simp [ValidLieTypeIndex.fieldOrder, q, hK])⟩
  have _ : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD n q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n) (by omega)
    (irreducible_map φ hirr) hirr₀
  let e1 := statedProjCongr (glCongr φ)
    (map_statedOmega φ (statedQuadMinus_comp (n := n) (b := b) (c := c) φ rfl rfl))
    (glCongr_statedScalars φ)
  exact ⟨⟨.twistedD n q, hv⟩, LieTypeIndex.characteristic_twistedD n q,
    ⟨((θ.trans e1).trans e2).trans eT.symm⟩⟩

theorem exists_tauCeti_index_of_statedClassicalModel {P : Type} [Group P] {t : StatedLieTag}
    {n p f : ℕ} (hm : StatedClassicalModel P t n p f) (hdup : ¬ TauCetiDuplicate t n p f) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (P ≃* (CFSGIndex.lie d).Group) := by
  cases t
  case PSL =>
    exact t6char3_index_psl hm fun h => hdup (Or.inl ⟨rfl, h⟩)
  case PSU => exact t6char3_index_psu hm
  case PSp => exact t6char3_index_psp hm fun h => hdup (Or.inr ⟨rfl, h⟩)
  case POmegaOdd => exact t6char3_index_pomegaOdd hm
  case POmegaPlus => exact t6char3_index_pomegaPlus hm
  case POmegaMinus => exact t6char3_index_pomegaMinus hm
  all_goals exact hm.2.elim

end Classical

theorem t6char3_characteristic_of_namesTag {d : LieTypeIndex} {t : StatedLieTag} {p f : ℕ}
    (h : CFSG.Models.NamesTag d t p f) : d.characteristic = p := by
  cases d <;> cases t <;> first
    | exact absurd h id
    | exact h.1
    | (obtain ⟨rfl, -⟩ := h; rfl)

theorem exists_tauCeti_index_of_blueprint_lieModel_odd (hB : CFSG.TauCetiBridge.TypewiseBridges)
    {P : Type} [Group P] {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Blueprint.LieModel P t n p f)
    (hp2 : p ≠ 2) (hdup : ¬ TauCetiDuplicate t n p f) :
    ∃ d : ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (P ≃* (CFSGIndex.lie d).Group) := by
  have hp : p.Prime := hm.admissible.1
  rcases hm with ⟨-, h⟩ | ⟨rfl, ht, h⟩ | ⟨rfl, ht, h⟩ | ⟨-, -, h⟩
  · exact exists_tauCeti_index_of_statedClassicalModel h hdup
  · obtain ⟨d, hd, he⟩ := CFSG.TauCetiBridge.exists_index_of_exceptional hB hp hp2 (.inl ⟨ht, h⟩)
    exact ⟨d, t6char3_characteristic_of_namesTag hd, he⟩
  · obtain ⟨d, hd, he⟩ := CFSG.TauCetiBridge.exists_index_of_exceptional hB hp hp2 (.inr ⟨ht, h⟩)
    exact ⟨d, t6char3_characteristic_of_namesTag hd, he⟩
  · exact absurd h.1 hp2

end CFSG.HardMathSupport.Dickson.Sec6.I1431
