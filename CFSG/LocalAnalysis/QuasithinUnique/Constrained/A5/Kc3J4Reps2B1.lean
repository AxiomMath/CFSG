module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B336Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Words
public import CFSG.Sporadic.J4.QT2AMod
public import CFSG.Sporadic.J4.QT2LocFiveProofBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] noncomputable def xiGens (t : ↥J) : List ↥J :=
  [t, fiveElt * t * fiveElt⁻¹, fiveElt ^ 2 * t * (fiveElt ^ 2)⁻¹,
    fiveElt ^ 3 * t * (fiveElt ^ 3)⁻¹]

@[expose] noncomputable def xiSpan (t : ↥J) : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ xiGens t}

@[expose] def b56Masks : List ℕ := [25, 136, 833, 1312]

@[expose] noncomputable def B56 : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ b56Masks.map (eta uJ 11)}

@[expose] noncomputable def B7 : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ CFSG.QuasithinUnique.A5.B7.b7ExplicitWords.map QT2A.el5}

@[expose] def b336Word : List ℤ :=
  QT2A.w5 "cAAccAccABCccBBCccBBCccBBCccBBCccBccAccAAbcBAbcBAbcBAbcBAbcBAbcBAbcBaaC"

@[expose] noncomputable def b336Gen (e : ℕ) : ↥J := eta uJ 11 e * QT2A.el5 b336Word

@[expose] noncomputable def B336a : Subgroup ↥J := xiSpan (b336Gen 37)

@[expose] noncomputable def B336b : Subgroup ↥J := xiSpan (b336Gen 97)

@[expose] noncomputable def B336c : Subgroup ↥J := xiSpan (b336Gen 236)

@[expose] noncomputable def B336d : Subgroup ↥J := xiSpan (b336Gen 491)

@[expose] noncomputable def B336x : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ Dec2.wsB336.map QT2A.el5}

@[expose] noncomputable def reps2B1 : List (Subgroup ↥J) :=
  [B56, B7, B336a, B336b, B336c, B336d, B336x]

theorem B56_mem_reps2B1 : B56 ∈ reps2B1 := by simp [reps2B1]

theorem B7_mem_reps2B1 : B7 ∈ reps2B1 := by simp [reps2B1]

theorem B336a_mem_reps2B1 : B336a ∈ reps2B1 := by simp [reps2B1]

theorem B336b_mem_reps2B1 : B336b ∈ reps2B1 := by simp [reps2B1]

theorem B336c_mem_reps2B1 : B336c ∈ reps2B1 := by simp [reps2B1]

theorem B336d_mem_reps2B1 : B336d ∈ reps2B1 := by simp [reps2B1]

theorem B336x_mem_reps2B1 : B336x ∈ reps2B1 := by simp [reps2B1]

end CFSG.QuasithinUnique.A5
