module

public import CFSG.Adapters.LinearCatalog
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix CFSG.Assembly.LowTwoRank TauCeti CFSG.ClassicalModels CFSG.AGLEmbedding

theorem isClassicalTwoOrG2_of_psl_nondup {G : Type} [Group G] {n f : ℕ}
    (h : StatedClassicalModel G .PSL n 2 f)
    (hdup : ¬ (LieTypeIndex.A (n - 1)
      ⟨2, f, h.1.1, by have hf := h.1.2.1; omega⟩).IsDuplicateRepresentative) :
    IsClassicalTwoOrG2 G := by
  let q : PrimePower := ⟨2, f, h.1.1, by have hf := h.1.2.1; omega⟩
  let _ : Fact (2 : ℕ).Prime := ⟨h.1.1⟩
  have hv : (LieTypeIndex.A (n - 1) q).Valid := linearCatalog_index_valid n 2 f h.1 hdup
  obtain ⟨K, hfield, hfinite, hKcard, e⟩ := h.2
  let _ := hfield
  let _ := hfinite
  obtain ⟨e⟩ := e
  let eK := statedLinearModelEquivGaloisPSL K n 2 f (by have hf := h.1.2.1; omega) hKcard
  have hdim : n - 1 + 1 = n := by have hn := h.1.2.2.1; omega
  have eC := linearCatalogCandidateEquivPSL (n - 1) q hv
  have eC' : (ValidLieTypeIndex.Group ⟨LieTypeIndex.A (n - 1) q, hv⟩) ≃*
      ProjectiveSpecialLinearGroup (Fin n) (GaloisField 2 f) := by
    rw [hdim] at eC
    exact eC
  exact Or.inl ⟨⟨LieTypeIndex.A (n - 1) q, hv⟩, rfl, ⟨(e.trans eK).trans eC'.symm⟩⟩

theorem isClassicalTwoOrG2_of_statedPSL {G : Type} [Group G]
    {n f : ℕ} (h : StatedClassicalModel G .PSL n 2 f) : IsClassicalTwoOrG2 G := by
  have hp : (2 : ℕ).Prime := h.1.1
  have hf : 1 ≤ f := h.1.2.1
  have hn : 2 ≤ n := h.1.2.2.1
  have hmem : (StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  by_cases hdup : (LieTypeIndex.A (n - 1)
      ⟨2, f, h.1.1, by omega⟩).IsDuplicateRepresentative
  · rw [LieTypeIndex.isDuplicateRepresentative_iff] at hdup
    simp only [PrimePower.card_def] at hdup
    rcases hdup with ⟨hr, h459⟩ | ⟨hr, hq⟩ | ⟨hr, hq⟩
    ·
      have hn2 : n = 2 := by omega
      subst hn2
      have h4 : 2 ^ f = 4 := by
        rcases h459 with h4 | h5 | h9
        · exact h4
        · exfalso
          have : (2 : ℕ) ^ f % 2 = 0 := by
            rw [Nat.pow_mod]; simp [Nat.zero_pow (by omega : 0 < f)]
          omega
        · exfalso
          have : (2 : ℕ) ^ f % 2 = 0 := by
            rw [Nat.pow_mod]; simp [Nat.zero_pow (by omega : 0 < f)]
          omega
      obtain ⟨-, K, hfield, hfinite, hKcard, ⟨e⟩⟩ := h
      let _ := hfield
      let _ := hfinite
      obtain ⟨e5⟩ := nonempty_statedLinearModel_equiv_alternating_five K (Or.inl (hKcard ▸ h4))
      exact Or.inr (Or.inl ⟨5, Or.inl rfl, ⟨e.trans e5⟩⟩)
    ·
      have hn3 : n = 3 := by omega
      subst hn3
      have hf1 : f = 1 := by
        have : (2 : ℕ) ^ f = 2 ^ 1 := by simpa using hq
        exact Nat.pow_right_injective le_rfl this
      subst hf1
      rcases CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism G
          (Or.inl ⟨hmem, h⟩) with ⟨-, h7⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · have hp7 : (7 : ℕ).Prime := h7.1.1
        let q7 : PrimePower := ⟨7, 1, hp7, by omega⟩
        let _ : Fact (7 : ℕ).Prime := ⟨hp7⟩
        have hv7 : (LieTypeIndex.A 1 q7).Valid := by
          have := linearCatalog_index_valid 2 7 1 h7.1 (by
            rw [LieTypeIndex.isDuplicateRepresentative_iff]
            simp only [PrimePower.card_def]
            omega)
          exact this
        obtain ⟨K, hfield, hfinite, hKcard, ⟨e⟩⟩ := h7.2
        let _ := hfield
        let _ := hfinite
        let eK := statedLinearModelEquivGaloisPSL K 2 7 1 (by omega) hKcard
        have eC := linearCatalogCandidateEquivPSL 1 q7 hv7
        exact Or.inr (Or.inr ⟨⟨LieTypeIndex.A 1 q7, hv7⟩, Or.inl ⟨q7, by simp [PrimePower.card_def, q7], rfl⟩,
          ⟨(e.trans eK).trans eC.symm⟩⟩)
      all_goals exact absurd h0 (by norm_num)
    ·
      have hn4 : n = 4 := by omega
      subst hn4
      have hf1 : f = 1 := by
        have : (2 : ℕ) ^ f = 2 ^ 1 := by simpa using hq
        exact Nat.pow_right_injective le_rfl this
      subst hf1
      obtain ⟨e⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
        (Or.inl ⟨hmem, h⟩)
      exact Or.inr (Or.inl ⟨8, Or.inr (Or.inr rfl), ⟨e⟩⟩)
  · exact isClassicalTwoOrG2_of_psl_nondup h hdup

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
