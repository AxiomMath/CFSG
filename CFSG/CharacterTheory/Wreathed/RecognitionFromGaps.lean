module

public import CFSG.CharacterTheory.Wreathed.SameFieldLinearRecognition
public import CFSG.CharacterTheory.Wreathed.ComponentCoverConfinement
public import CFSG.CharacterTheory.Wreathed.FourPointUnitaryRecognition
public import CFSG.CharacterTheory.Semidihedral.RecognitionFromGaps

public section

namespace CFSG.Wreathed.RecognitionFromGaps

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.OriginalStationarityCoverageCriterion
  CFSG.Wreathed.SmallerRecognitionOriginalField

@[expose] def RecognitionAt (G : Type) [Group G] : Prop :=
  ∀ (a : ℕ), 2 ≤ a → ∀ (T : Sylow 2 G), Nonempty (T ≃* Wreath (2 ^ a)) →
    ∃ r b : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ b ∧
      ((r ^ b % 4 = 1 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 r b) ∨
        (r ^ b % 4 = 3 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 r b))

@[expose] def SemidihedralRecognitionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    (∃ (S : Sylow 2 G) (n : ℕ), 4 ≤ n ∧
      Nonempty ((S : Subgroup G) ≃* CFSG.Open.SemidihedralGroup n)) →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
        CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
        CFSG.Open.StatedClassicalModel G .PSU 3 p f) ∨
    Nonempty (G ≃* CFSG.Open.StatedM11)

theorem smallerSimpleRecognition_of_semidihedral (hSD : SemidihedralRecognitionStatement)
    (X : Type) : CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition X := by
  intro A _ _ _ hAnonab _ k hk S ⟨e⟩
  rcases hSD A hAnonab ⟨S, k, hk, ⟨e.symm⟩⟩ with
    ⟨p, f, hp, hp2, hf, hq, hm⟩ | ⟨p, f, hp, hp2, hf, hq, hm⟩ | hM
  · exact Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hq, hm⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hq, hm⟩)
  · exact Or.inr (Or.inr hM)

@[expose] def StationaryCoverageStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    SmallerWreathedRecognition G →
    CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G →
    ∀ (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)),
      ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 ≤ p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f →
      OriginalAllPrimeStationarity n S e ∧ OriginalAllPrimeCoverage n S e

@[expose] def UnitaryBranchStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    SmallerWreathedRecognition G →
    ∀ (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)),
      ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 ≤ p ^ f → p ^ f % 4 = 3 →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f →
      OriginalAllPrimeStationarity n S e → OriginalAllPrimeCoverage n S e →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f

theorem five_le_of_admissible {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (h : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f) : 5 ≤ p ^ f := by
  obtain ⟨-, -, -, -, h3⟩ := h
  have hodd : Odd (p ^ f) := hpodd.pow
  have hp3 : 3 ≤ p ^ f := by
    have h1 : p ≤ p ^ f := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    have : p ≠ 2 := fun h2 => by rw [h2] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
    have := hp.two_le
    omega
  have hne : p ^ f ≠ 3 := fun h' => h3 (by rw [h'])
  obtain ⟨k, hk⟩ := hodd
  omega

theorem recognitionAt_of_local_theorems
    (hSC : StationaryCoverageStatement)
    (hU : UnitaryBranchStatement) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (hsd : CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G) :
    RecognitionAt G := by
  intro n hn S ⟨e⟩
  by_cases hfour : Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
  · obtain ⟨α⟩ := hfour
    have : Fintype G := Fintype.ofFinite G
    have : Fintype (centralizerOddCoreQuotient n S e) := Fintype.ofFinite _
    exact ⟨3, 1, Nat.prime_three, by norm_num, le_refl _, Or.inr ⟨by norm_num,
      (FourPointUnitaryRecognition.four_point_actual_simple_group_is_unitary_three_over_nine
        hnonab n hn S e α).2⟩⟩
  · obtain ⟨p, f, hp, hp2, hpodd, hf, hmodel⟩ :=
      actual_full_center_quotient_layer_odd_projective_model hnonab n hn S e hfour
    have hmodel' : CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (centralizerSimpleLayer n hn S e) .PSL 2 p f := hmodel
    have hq5 : 5 ≤ p ^ f := five_le_of_admissible hp hpodd hf hmodel'.1
    obtain ⟨hst, hcov⟩ := hSC G hnonab hrec hsd n hn S e hfour p f hp hpodd hf hq5 hmodel'
    have hodd : Odd (p ^ f) := hpodd.pow
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with hq1 | hq3
    · have hconf :=
        ComponentCoverConfinement.stationarity_and_original_coverage_confine_all_odd_core_elements
          hnonab n hn S e hfour p f hp hpodd hf hq5 hmodel' hrec hst hcov
      exact ⟨p, f, hp, hp2, hf, Or.inl ⟨hq1,
        SameFieldLinearRecognition.wreathed_linear_branch_of_original_primewise hnonab n hn S e
          hfour p f hp hp2 hf hmodel hcov (fun r hr hr1 => (hconf r hr hr1).1) hq1⟩⟩
    · exact ⟨p, f, hp, hp2, hf, Or.inr ⟨hq3,
        hU G hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel' hst hcov⟩⟩

theorem recognitionAt_all
    (hSD : SemidihedralRecognitionStatement)
    (hSC : StationaryCoverageStatement) (hU : UnitaryBranchStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    RecognitionAt G := by
  suffices h : ∀ (k : ℕ) (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → Nat.card G = k → RecognitionAt G from h _ G hnonab rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro G _ _ _ hnonab hk
    refine recognitionAt_of_local_theorems hSC hU G hnonab ?_
      (smallerSimpleRecognition_of_semidihedral hSD G)
    intro J _ _ _ hJnonab hJ a ha T hT
    exact ih (Nat.card J) (hk ▸ hJ) J hJnonab rfl a ha T hT

theorem wreathed_recognition_of_local_theorems
    (hSD : SemidihedralRecognitionStatement)
    (hSC : StationaryCoverageStatement) (hU : UnitaryBranchStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hwr : ∃ (S : Sylow 2 G) (n : ℕ), 2 ≤ n ∧
      Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
        CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
        CFSG.Open.StatedClassicalModel G .PSU 3 p f) := by
  obtain ⟨S, n, hn, he⟩ := hwr
  obtain ⟨r, b, hr, hr2, hb, ⟨hq, hm⟩ | ⟨hq, hm⟩⟩ := recognitionAt_all hSD hSC hU G hnonab n hn S he
  · exact Or.inl ⟨r, b, hr, hr2, hb, hq,
      CFSG.Semidihedral.RecognitionFromGaps.stated_model_psl_of_lowTwoRank hm⟩
  · exact Or.inr ⟨r, b, hr, hr2, hb, hq,
      CFSG.Semidihedral.RecognitionFromGaps.stated_model_psu_of_lowTwoRank hm⟩

theorem wreathed_catalogue_of_local_theorems
    (hSD : SemidihedralRecognitionStatement)
    (hSC : StationaryCoverageStatement) (hU : UnitaryBranchStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (hwr : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((P : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) :
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* CFSG.Open.PSU3 p k)) := by
  obtain ⟨n, hn, he⟩ := hwr
  exact CFSG.Adapters.RankTwoModelTransports.wreathed_catalogue_of_stated G
    (wreathed_recognition_of_local_theorems hSD hSC hU G hnonab ⟨P, n, hn, he⟩)

end CFSG.Wreathed.RecognitionFromGaps
