module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three7
public import CFSG.RankThree.PartOne.KE.E8ClassLists

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)

open scoped Matrix MatrixGroups

private theorem wordProd_append_smul {c c' : List (Fin Tag.E8.rank)} {l l' l'' : List ℤ}
    (hc' : (coxeterSystem Tag.E8).wordProd c' • toVec Tag.E8.rank l = toVec Tag.E8.rank l')
    (hc : (coxeterSystem Tag.E8).wordProd c • toVec Tag.E8.rank l' = toVec Tag.E8.rank l'') :
    (coxeterSystem Tag.E8).wordProd (c ++ c') • toVec Tag.E8.rank l = toVec Tag.E8.rank l'' := by
  rw [CoxeterSystem.wordProd_append, mul_smul, hc', hc]

private def e8T3W1a : List (Fin Tag.E8.rank) := [3, 4, 2, 3, 0, 2, 1, 3]

private def e8T3W1b : List (Fin Tag.E8.rank) := [4, 5, 6, 7, 2, 3, 0, 2]

private def e8T3W1c : List (Fin Tag.E8.rank) := [1, 3, 4, 5, 6, 3, 2, 1]

private def e8T3W1d : List (Fin Tag.E8.rank) := [3, 4, 5, 0, 2, 3, 4, 1]

private def e8T3W1e : List (Fin Tag.E8.rank) := [3]

private def e8T3W2a : List (Fin Tag.E8.rank) := [5, 6, 7, 4, 5, 6, 2, 3]

private def e8T3W2b : List (Fin Tag.E8.rank) := [4, 5, 1, 3, 4, 2, 1, 3]

def e8T3W1 : List (Fin Tag.E8.rank) := e8T3W1a ++ (e8T3W1b ++ (e8T3W1c ++ (e8T3W1d ++ e8T3W1e)))

def e8T3W2 : List (Fin Tag.E8.rank) := e8T3W2a ++ e8T3W2b

section Certs

theorem mem_twistedFixedPoints_of_mem_twistedTorusOf {τ : Tag} {L : Type} [Field L]
    {n : ModGL τ L} {Φ : ModGL τ L →* ModGL τ L} {x : ModGL τ L}
    (h : x ∈ twistedTorusOf n Φ) : x ∈ twistedFixedPoints n Φ :=
  mem_twistedFixedPoints.2 (mem_twistedTorusOf.1 h).2

private theorem e8a2Weight_zero :
    e8a2Weight (0 : Fin 3) = toVec Tag.E8.rank [1, 0, 1, 1, 0, 0, 0, 0] := by
  rw [e8a2Weight_eq]
  rfl

private theorem e8a2Weight_one :
    e8a2Weight (1 : Fin 3) = toVec Tag.E8.rank [0, 0, 1, 1, 0, 0, 0, 0] := by
  rw [e8a2Weight_eq]
  rfl

private theorem e8a2Weight_two :
    e8a2Weight (2 : Fin 3) = toVec Tag.E8.rank [0, 0, 0, 1, 0, 0, 0, 0] := by
  rw [e8a2Weight_eq]
  rfl

private theorem wb_chain_e8T3W1 {l0 l1 l2 l3 l4 l5 : List ℤ}
    (h5 : (coxeterSystem Tag.E8).wordProd e8T3W1e • toVec Tag.E8.rank l0 = toVec Tag.E8.rank l1)
    (h4 : (coxeterSystem Tag.E8).wordProd e8T3W1d • toVec Tag.E8.rank l1 = toVec Tag.E8.rank l2)
    (h3 : (coxeterSystem Tag.E8).wordProd e8T3W1c • toVec Tag.E8.rank l2 = toVec Tag.E8.rank l3)
    (h2 : (coxeterSystem Tag.E8).wordProd e8T3W1b • toVec Tag.E8.rank l3 = toVec Tag.E8.rank l4)
    (h1 : (coxeterSystem Tag.E8).wordProd e8T3W1a • toVec Tag.E8.rank l4 = toVec Tag.E8.rank l5) :
    (coxeterSystem Tag.E8).wordProd e8T3W1 • toVec Tag.E8.rank l0 = toVec Tag.E8.rank l5 := by
  have hA := wordProd_append_smul (c := e8T3W1d) (c' := e8T3W1e) h5 h4
  have hB := wordProd_append_smul (c := e8T3W1c) (c' := e8T3W1d ++ e8T3W1e) hA h3
  have hC := wordProd_append_smul (c := e8T3W1b) (c' := e8T3W1c ++ (e8T3W1d ++ e8T3W1e)) hB h2
  have hD := wordProd_append_smul (c := e8T3W1a)
    (c' := e8T3W1b ++ (e8T3W1c ++ (e8T3W1d ++ e8T3W1e))) hC h1
  rw [e8T3W1]
  exact hD

private theorem wb_chain_e8T3W2 {l0 l1 l2 : List ℤ}
    (h2 : (coxeterSystem Tag.E8).wordProd e8T3W2b • toVec Tag.E8.rank l0 = toVec Tag.E8.rank l1)
    (h1 : (coxeterSystem Tag.E8).wordProd e8T3W2a • toVec Tag.E8.rank l1 = toVec Tag.E8.rank l2) :
    (coxeterSystem Tag.E8).wordProd e8T3W2 • toVec Tag.E8.rank l0 = toVec Tag.E8.rank l2 := by
  have hA := wordProd_append_smul (c := e8T3W2a) (c' := e8T3W2b) h2 h1
  rw [e8T3W2]
  exact hA

private theorem wb_e8T3W1_zero :
    wbE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) 0 =
      toVec Tag.E8.rank [0, 1, 1, 2, 2, 1, 1, 0] := by
  rw [wbE8, e8a2Weight_zero]
  refine wb_chain_e8T3W1 (l0 := [1, 0, 1, 1, 0, 0, 0, 0]) (l1 := [1, 0, 1, 0, 0, 0, 0, 0])
    (l2 := [0, 0, 1, 1, 1, 0, 0, 0]) (l3 := [0, 0, 0, 1, 1, 1, 0, 0])
    (l4 := [1, 0, 1, 1, 1, 1, 1, 0]) (l5 := [0, 1, 1, 2, 2, 1, 1, 0])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

private theorem wb_e8T3W1_one :
    wbE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) 1 =
      toVec Tag.E8.rank [0, 1, 1, 2, 1, 1, 1, 0] := by
  rw [wbE8, e8a2Weight_one]
  refine wb_chain_e8T3W1 (l0 := [0, 0, 1, 1, 0, 0, 0, 0]) (l1 := [0, 0, 1, 0, 0, 0, 0, 0])
    (l2 := [0, 0, 0, 0, 1, 0, 0, 0]) (l3 := [0, 0, 0, 0, 1, 1, 0, 0])
    (l4 := [0, 0, 1, 1, 1, 1, 1, 0]) (l5 := [0, 1, 1, 2, 1, 1, 1, 0])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

private theorem wb_e8T3W1_two :
    wbE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) 2 =
      toVec Tag.E8.rank [-2, -2, -3, -4, -3, -2, -1, -1] := by
  rw [wbE8, e8a2Weight_two]
  refine wb_chain_e8T3W1 (l0 := [0, 0, 0, 1, 0, 0, 0, 0]) (l1 := [0, 0, 0, -1, 0, 0, 0, 0])
    (l2 := [-1, -1, -1, -2, -1, -1, 0, 0]) (l3 := [-1, -2, -2, -3, -2, -1, -1, 0])
    (l4 := [-1, -2, -2, -3, -3, -2, -1, -1]) (l5 := [-2, -2, -3, -4, -3, -2, -1, -1])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

private theorem wb_e8T3W2_zero :
    wbE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) 0 =
      toVec Tag.E8.rank [1, 0, 1, 0, 0, 0, 0, 0] := by
  rw [wbE8, e8a2Weight_zero]
  refine wb_chain_e8T3W2 (l0 := [1, 0, 1, 1, 0, 0, 0, 0]) (l1 := [1, 0, 0, 0, 0, 0, 0, 0])
    (l2 := [1, 0, 1, 0, 0, 0, 0, 0]) (by decide +kernel) (by decide +kernel)

private theorem wb_e8T3W2_one :
    wbE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) 1 =
      toVec Tag.E8.rank [0, -1, -1, -2, -2, -2, -1, 0] := by
  rw [wbE8, e8a2Weight_one]
  refine wb_chain_e8T3W2 (l0 := [0, 0, 1, 1, 0, 0, 0, 0]) (l1 := [0, -1, -1, -1, -1, 0, 0, 0])
    (l2 := [0, -1, -1, -2, -2, -2, -1, 0]) (by decide +kernel) (by decide +kernel)

private theorem wb_e8T3W2_two :
    wbE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) 2 =
      toVec Tag.E8.rank [0, -1, -1, -2, -2, -2, -2, -1] := by
  rw [wbE8, e8a2Weight_two]
  refine wb_chain_e8T3W2 (l0 := [0, 0, 0, 1, 0, 0, 0, 0]) (l1 := [0, -1, -1, -2, -2, -1, 0, 0])
    (l2 := [0, -1, -1, -2, -2, -2, -2, -1]) (by decide +kernel) (by decide +kernel)

private theorem toVec_sub_toVec (u v : List ℤ) :
    toVec Tag.E8.rank u - toVec Tag.E8.rank v =
      fun k : Fin Tag.E8.rank => u.getD k 0 - v.getD k 0 := by
  funext k
  rfl

private theorem sigmaRoot_e8T3W1_zero_one :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) 0 1 = -e8T3BetaOne := by
  rw [sigmaRootE8, wb_e8T3W1_zero, wb_e8T3W1_one, e8T3BetaOne, toVec_sub_toVec]
  funext k
  fin_cases k <;> decide

private theorem sigmaRoot_e8T3W1_zero_two :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) 0 2 = -e8T3BetaTwo := by
  rw [sigmaRootE8, wb_e8T3W1_zero, wb_e8T3W1_two, e8T3BetaTwo, toVec_sub_toVec]
  funext k
  fin_cases k <;> decide

private theorem sigmaRoot_e8T3W1_one_two :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) 1 2 =
      e8T3BetaOne - e8T3BetaTwo := by
  rw [sigmaRootE8, wb_e8T3W1_one, wb_e8T3W1_two, e8T3BetaOne, e8T3BetaTwo, toVec_sub_toVec]
  funext k
  fin_cases k <;> decide

private theorem sigmaRoot_e8T3W1_one_zero :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) 1 0 = e8T3BetaOne := by
  rw [← sigmaRootE8_neg, sigmaRoot_e8T3W1_zero_one, neg_neg]

private theorem sigmaRoot_e8T3W1_two_zero :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) 2 0 = e8T3BetaTwo := by
  rw [← sigmaRootE8_neg, sigmaRoot_e8T3W1_zero_two, neg_neg]

private theorem sigmaRoot_e8T3W1_two_one :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) 2 1 =
      e8T3BetaTwo - e8T3BetaOne := by
  rw [← sigmaRootE8_neg, sigmaRoot_e8T3W1_one_two, neg_sub]

private theorem sigmaRoot_e8T3W2_zero_one :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) 0 1 =
      e8T3GammaOne - e8T3GammaTwo := by
  rw [sigmaRootE8, wb_e8T3W2_zero, wb_e8T3W2_one, e8T3GammaOne, e8T3GammaTwo, toVec_sub_toVec]
  funext k
  fin_cases k <;> decide

private theorem sigmaRoot_e8T3W2_zero_two :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) 0 2 = e8T3GammaOne := by
  rw [sigmaRootE8, wb_e8T3W2_zero, wb_e8T3W2_two, e8T3GammaOne, toVec_sub_toVec]
  funext k
  fin_cases k <;> decide

private theorem sigmaRoot_e8T3W2_one_two :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) 1 2 = e8T3GammaTwo := by
  rw [sigmaRootE8, wb_e8T3W2_one, wb_e8T3W2_two, e8T3GammaTwo, toVec_sub_toVec]
  funext k
  fin_cases k <;> decide

private theorem sigmaRoot_e8T3W2_one_zero :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) 1 0 =
      e8T3GammaTwo - e8T3GammaOne := by
  rw [← sigmaRootE8_neg, sigmaRoot_e8T3W2_zero_one, neg_sub]

private theorem sigmaRoot_e8T3W2_two_zero :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) 2 0 = -e8T3GammaOne := by
  rw [← sigmaRootE8_neg, sigmaRoot_e8T3W2_zero_two]

private theorem sigmaRoot_e8T3W2_two_one :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) 2 1 = -e8T3GammaTwo := by
  rw [← sigmaRootE8_neg, sigmaRoot_e8T3W2_one_two]

@[expose] def e8T3A2One : Set (Fin Tag.E8.rank → ℤ) :=
  {e8T3BetaOne, e8T3BetaTwo, e8T3BetaOne - e8T3BetaTwo, -e8T3BetaOne, -e8T3BetaTwo,
    e8T3BetaTwo - e8T3BetaOne}

@[expose] def e8T3A2Two : Set (Fin Tag.E8.rank → ℤ) :=
  {e8T3GammaOne, e8T3GammaTwo, e8T3GammaOne - e8T3GammaTwo, -e8T3GammaOne, -e8T3GammaTwo,
    e8T3GammaTwo - e8T3GammaOne}

theorem sigmaSetE8_e8T3W1 :
    sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) = e8T3A2One := by
  ext α
  rw [sigmaSetE8_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [e8T3A2One, sigmaRoot_e8T3W1_zero_one, sigmaRoot_e8T3W1_zero_two,
            sigmaRoot_e8T3W1_one_two, sigmaRoot_e8T3W1_one_zero, sigmaRoot_e8T3W1_two_zero,
            sigmaRoot_e8T3W1_two_one]
  · intro h
    simp only [e8T3A2One, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h | h
    · exact ⟨1, 0, by decide, by rw [h, sigmaRoot_e8T3W1_one_zero]⟩
    · exact ⟨2, 0, by decide, by rw [h, sigmaRoot_e8T3W1_two_zero]⟩
    · exact ⟨1, 2, by decide, by rw [h, sigmaRoot_e8T3W1_one_two]⟩
    · exact ⟨0, 1, by decide, by rw [h, sigmaRoot_e8T3W1_zero_one]⟩
    · exact ⟨0, 2, by decide, by rw [h, sigmaRoot_e8T3W1_zero_two]⟩
    · exact ⟨2, 1, by decide, by rw [h, sigmaRoot_e8T3W1_two_one]⟩

theorem sigmaSetE8_e8T3W2 :
    sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) = e8T3A2Two := by
  ext α
  rw [sigmaSetE8_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [e8T3A2Two, sigmaRoot_e8T3W2_zero_one, sigmaRoot_e8T3W2_zero_two,
            sigmaRoot_e8T3W2_one_two, sigmaRoot_e8T3W2_one_zero, sigmaRoot_e8T3W2_two_zero,
            sigmaRoot_e8T3W2_two_one]
  · intro h
    simp only [e8T3A2Two, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h | h
    · exact ⟨0, 2, by decide, by rw [h, sigmaRoot_e8T3W2_zero_two]⟩
    · exact ⟨1, 2, by decide, by rw [h, sigmaRoot_e8T3W2_one_two]⟩
    · exact ⟨0, 1, by decide, by rw [h, sigmaRoot_e8T3W2_zero_one]⟩
    · exact ⟨2, 0, by decide, by rw [h, sigmaRoot_e8T3W2_two_zero]⟩
    · exact ⟨2, 1, by decide, by rw [h, sigmaRoot_e8T3W2_two_one]⟩
    · exact ⟨1, 0, by decide, by rw [h, sigmaRoot_e8T3W2_one_zero]⟩

theorem neg_mem_e8T3A2One {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8T3A2One) :
    -α ∈ e8T3A2One := by
  simp only [e8T3A2One, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · rw [neg_sub]; simp
  · simp
  · simp
  · rw [neg_sub]; simp

theorem neg_mem_e8T3A2Two {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8T3A2Two) :
    -α ∈ e8T3A2Two := by
  simp only [e8T3A2Two, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · rw [neg_sub]; simp
  · simp
  · simp
  · rw [neg_sub]; simp

private theorem e8T3W_smul_e8T3BetaOne :
    e8T3W • e8T3BetaOne = e8T3BetaTwo - e8T3BetaOne := by
  rw [← weylMatrix_mulVec, weylMatrix_e8T3W]
  decide +kernel

private theorem e8T3W_smul_e8T3BetaTwo : e8T3W • e8T3BetaTwo = -e8T3BetaOne := by
  rw [← weylMatrix_mulVec, weylMatrix_e8T3W]
  decide +kernel

private theorem e8T3W_smul_e8T3BetaSub :
    e8T3W • (e8T3BetaOne - e8T3BetaTwo) = e8T3BetaTwo := by
  rw [← weylMatrix_mulVec, weylMatrix_e8T3W]
  decide +kernel

private theorem e8T3W_smul_e8T3GammaOne :
    e8T3W • e8T3GammaOne = e8T3GammaTwo - e8T3GammaOne := by
  rw [← weylMatrix_mulVec, weylMatrix_e8T3W]
  decide +kernel

private theorem e8T3W_smul_e8T3GammaTwo : e8T3W • e8T3GammaTwo = -e8T3GammaOne := by
  rw [← weylMatrix_mulVec, weylMatrix_e8T3W]
  decide +kernel

private theorem e8T3W_smul_e8T3GammaSub :
    e8T3W • (e8T3GammaOne - e8T3GammaTwo) = e8T3GammaTwo := by
  rw [← weylMatrix_mulVec, weylMatrix_e8T3W]
  decide +kernel

private theorem e8T6W_smul_eq_neg (α : Fin Tag.E8.rank → ℤ) :
    e8T6W • α = -(e8T3W • α) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, weylMatrix_e8T6W, weylMatrix_e8T3W,
    ← Matrix.neg_mulVec]

private theorem e8T3W_smul_mem_e8T3A2One {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8T3A2One) :
    e8T3W • α ∈ e8T3A2One := by
  simp only [e8T3A2One, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e8T3W_smul_e8T3BetaOne]; simp
  · rw [e8T3W_smul_e8T3BetaTwo]; simp
  · rw [e8T3W_smul_e8T3BetaSub]; simp
  · rw [smul_neg, e8T3W_smul_e8T3BetaOne, neg_sub]; simp
  · rw [smul_neg, e8T3W_smul_e8T3BetaTwo, neg_neg]; simp
  · rw [smul_sub, e8T3W_smul_e8T3BetaTwo, e8T3W_smul_e8T3BetaOne]
    have h : -e8T3BetaOne - (e8T3BetaTwo - e8T3BetaOne) = -e8T3BetaTwo := by abel
    rw [h]; simp

private theorem e8T3W_smul_mem_e8T3A2Two {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8T3A2Two) :
    e8T3W • α ∈ e8T3A2Two := by
  simp only [e8T3A2Two, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e8T3W_smul_e8T3GammaOne]; simp
  · rw [e8T3W_smul_e8T3GammaTwo]; simp
  · rw [e8T3W_smul_e8T3GammaSub]; simp
  · rw [smul_neg, e8T3W_smul_e8T3GammaOne, neg_sub]; simp
  · rw [smul_neg, e8T3W_smul_e8T3GammaTwo, neg_neg]; simp
  · rw [smul_sub, e8T3W_smul_e8T3GammaTwo, e8T3W_smul_e8T3GammaOne]
    have h : -e8T3GammaOne - (e8T3GammaTwo - e8T3GammaOne) = -e8T3GammaTwo := by abel
    rw [h]; simp

theorem e8T3We_smul_mem_e8T3A2One {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∀ α ∈ e8T3A2One, e8T3We ε • α ∈ e8T3A2One := by
  rcases hε with rfl | rfl
  · intro α hα
    simpa only [e8T3We_one] using e8T3W_smul_mem_e8T3A2One hα
  · intro α hα
    rw [e8T3We_neg_one, e8T6W_smul_eq_neg]
    exact neg_mem_e8T3A2One (e8T3W_smul_mem_e8T3A2One hα)

theorem e8T3We_smul_mem_e8T3A2Two {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∀ α ∈ e8T3A2Two, e8T3We ε • α ∈ e8T3A2Two := by
  rcases hε with rfl | rfl
  · intro α hα
    simpa only [e8T3We_one] using e8T3W_smul_mem_e8T3A2Two hα
  · intro α hα
    rw [e8T3We_neg_one, e8T6W_smul_eq_neg]
    exact neg_mem_e8T3A2Two (e8T3W_smul_mem_e8T3A2Two hα)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
