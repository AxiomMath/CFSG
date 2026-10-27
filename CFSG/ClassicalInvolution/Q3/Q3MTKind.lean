module

public import CFSG.ClassicalInvolution.Q3.Q3MTAbel
public import CFSG.ClassicalInvolution.Q3.Q3MTBig
public import CFSG.ClassicalInvolution.Q3.Q3MTWyl
public import CFSG.ClassicalInvolution.Q3.Q3MTRows
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open CFSG.Assembly CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.MuTab
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3T6

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem muVal_of_shape (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) (hne : Ω.Nonempty)
    (κ : MuKind) (h : KindShape Ω κ) : MuVal Ω W κ := by
  cases κ with
  | z2 => exact Mu.muIsoZ2_of_shape hP hW hne h
  | s3 => exact Mu.muIsoS3_of_shape hP hW h.1 h.2
  | e4 => exact muIsoE4_of_shape hP hW h.1 h.2.1 h.2.2
  | s4 => exact muIsoS4_of_shape hP hW h.1 h.2.1 h.2.2
  | wyl =>
    obtain ⟨hle, ⟨K, hK, hinj, hcomm⟩, hcomp⟩ := h
    exact muIsoWylD4_of_shape hP hW hle K hK hinj hcomm hcomp
  | big10 =>
    obtain ⟨K, U, Q, hinj, hQ, h⟩ := h
    exact not_small_of_big10 hP hW K U hinj (fun i => (h i).1) (fun i => (h i).2.1)
      (fun i => (h i).2.2.1) Q hQ (fun i => (h i).2.2.2)
  | large =>
    obtain ⟨K, hK, hinj, hcomm⟩ := h
    exact not_small_of_triple hP hW K hK hinj hcomm

theorem muKind_cases3 (π : Bool) (t : LowTwoRank.StatedLieTag) (k : ℕ) :
    (t = .PSL ∧ k = 3) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSL ∧ k = 5) ∨ (t = .PSU ∧ k = 3) ∨
      (t = .PSU ∧ k = 4) ∨ (t = .PSU ∧ k = 5) ∨ (t = .PSp ∧ k = 2) ∨ (t = .POmegaOdd ∧ k = 3) ∨
      (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4) ∨ (t = .G2 ∧ k = 0) ∨
      (t = .trialityD4 ∧ k = 0) ∨ muKind π t k = .large := by
  by_cases h1 : t = .PSL ∧ k = 3
  · exact Or.inl h1
  by_cases h2 : t = .PSL ∧ k = 4
  · exact Or.inr (Or.inl h2)
  by_cases h3 : t = .PSL ∧ k = 5
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : t = .PSU ∧ k = 3
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  by_cases h5 : t = .PSU ∧ k = 4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  by_cases h6 : t = .PSU ∧ k = 5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  by_cases h7 : t = .PSp ∧ k = 2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
  by_cases h8 : t = .POmegaOdd ∧ k = 3
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))))
  by_cases h9 : t = .POmegaPlus ∧ k = 4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9))))))))
  by_cases h10 : t = .POmegaMinus ∧ k = 4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h10)))))))))
  by_cases h11 : t = .G2 ∧ k = 0
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h11))))))))))
  by_cases h12 : t = .trialityD4 ∧ k = 0
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h12)))))))))))
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr ?_)))))))))))
  simp only [muKind, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ↓reduceIte]

theorem piSign_three_one : piSign 3 1 = false := by decide

section Table


@[expose] def SmallShape3 (t : LowTwoRank.StatedLieTag) (k : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
      (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → HasLieTypeU 3 1 Ω t k →
        KindShape Ω (muKind false t k)

structure MuSmallShapes3 : Prop where
  psl3 : SmallShape3 .PSL 3
  psl4 : SmallShape3 .PSL 4
  psl5 : SmallShape3 .PSL 5
  psu3 : SmallShape3 .PSU 3
  psu4 : SmallShape3 .PSU 4
  psu5 : SmallShape3 .PSU 5
  psp2 : SmallShape3 .PSp 2
  pOmegaOdd3 : SmallShape3 .POmegaOdd 3
  pOmegaPlus4 : SmallShape3 .POmegaPlus 4
  pOmegaMinus4 : SmallShape3 .POmegaMinus 4
  g2 : SmallShape3 .G2 0
  trialityD4 : SmallShape3 .trialityD4 0
  large : ∀ (t : LowTwoRank.StatedLieTag) (k : ℕ), muKind false t k = .large → SmallShape3 t k
  m11 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
      (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → HasM11TypeU 3 1 Ω → ShapeZ2 Ω

theorem MuSmallShapes3.shape (hsh : MuSmallShapes3) (t : LowTwoRank.StatedLieTag) (k : ℕ) :
    SmallShape3 t k := by
  rcases muKind_cases3 false t k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | hlarge
  · exact hsh.psl3
  · exact hsh.psl4
  · exact hsh.psl5
  · exact hsh.psu3
  · exact hsh.psu4
  · exact hsh.psu5
  · exact hsh.psp2
  · exact hsh.pOmegaOdd3
  · exact hsh.pOmegaPlus4
  · exact hsh.pOmegaMinus4
  · exact hsh.g2
  · exact hsh.trialityD4
  · exact hsh.large t k hlarge

theorem muValuesU_of_shapes (hsh : MuSmallShapes3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hA : ∀ J ∈ Ω, AEmpty Ω J) (hne : Ω.Nonempty)
    (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) {W : Subgroup G} (hW : W ∈ WSet Ω) :
    MuValuesU 3 1 false Ω W :=
  have hP := Q3CL.partIHypG_of_modU hΩ hA
  ⟨fun t k hL => muVal_of_shape hP hW hne _ (hsh.shape t k G Ω hΩ hA hne htrans hL),
    fun hM => muVal_of_shape hP hW hne .z2 (hsh.m11 G Ω hΩ hA hne htrans hM)⟩

theorem muTableBelowU_three_of_shapes {n : ℕ} (hn : CITBelowT (.sl2 3 1) n)
    (hsh : MuSmallShapes3) (h6 : Thm6TypedBelowU 3 1 n) (h8 : Thm8TypedBelowU 3 1 n) :
    MuTableBelowU 3 1 n := by
  intro hp2 hq G _ _ _ hlt Ω hΩ hA hne htrans W hW
  have hex := hasTypeU_three_of_citBelowT hn hlt hΩ hne
  have hv : MuValuesU 3 1 (piSign 3 1) Ω W := by
    rw [piSign_three_one]
    exact muValuesU_of_shapes hsh hΩ hA hne htrans hW
  exact muRowsU_of_values hex hv (fun hE => h6 hp2 hq G hlt Ω hΩ hA hne htrans hE)
    (fun hE hC => h8 hp2 hq G hlt Ω hΩ hA hne htrans hE hC)

end Table

end CFSG.ClassicalInvolution.Q3.Q3MT
