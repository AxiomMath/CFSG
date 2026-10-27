module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks
public import CFSG.HardMathSupport.Timmesfeld.Torality.SL3Monomial
public import CFSG.RankThree.PartOne.KE.E8A2Sigma
public import CFSG.RankThree.Lattice.SteinbergBIRoots

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

@[expose] def e8Word (l : List ℕ) : List (Fin Tag.E8.rank) :=
  l.map fun n => (⟨n % 8, Nat.mod_lt n (by decide)⟩ : Fin 8)

@[expose] def e8RootWords : Fin 8 → List ℕ :=
  ![[], [3, 2, 1, 3, 0, 2], [0, 2], [2, 3, 0, 2], [3, 4, 2, 3, 0, 2], [4, 5, 3, 4, 2, 3, 0, 2],
    [5, 6, 4, 5, 3, 4, 2, 3, 0, 2], [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2]]

set_option maxHeartbeats 2000000 in
@[expose] def e8A2PairWords : List (List ℤ × List ℕ) :=
  [
    ([-2, -3, -3, -5, -4, -3, -2, -1], [
      1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0,
      2]),
    ([-2, -2, -3, -5, -4, -3, -2, -1], [
      3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-2, -2, -3, -4, -4, -3, -2, -1], [
      4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-2, -2, -3, -4, -3, -3, -2, -1], [
      5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-2, -2, -3, -4, -3, -2, -2, -1], [
      6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-2, -2, -3, -4, -3, -2, -1, -1], [
      7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-2, -2, -3, -4, -3, -2, -1, 0], [
      2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -2, -2, -2, -1], [6, 7, 5, 6, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -2, -2, -1, -1], [7, 5, 6, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -2, -2, -1, 0], [5, 6, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -2, -1, -1, -1], [7, 6, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -2, -1, -1, 0], [6, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -2, -1, 0, 0], [4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -1, -1, -1, -1], [7, 6, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -1, -1, -1, 0], [6, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -1, -1, 0, 0], [5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -1, 0, 0, 0], [2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -1, -1, -1, -1, -1], [7, 6, 5, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -1, -1, -1, -1, 0], [6, 5, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -1, -1, -1, 0, 0], [5, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -1, -1, 0, 0, 0], [2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -1, 0, 0, 0, 0], [4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, -1, -1, -1, -1, -1], [7, 6, 5, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, -1, -1, -1, -1, 0], [6, 5, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, -1, -1, -1, 0, 0], [5, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, -1, -1, 0, 0, 0], [2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, -1, 0, 0, 0, 0], [4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, 0, 0, 0, 0, 0], [3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([0, 0, 1, 0, 0, 0, 0, 0], []),
    ([0, 0, 1, 1, 0, 0, 0, 0], [3]),
    ([0, 0, 1, 1, 1, 0, 0, 0], [4, 3]),
    ([0, 0, 1, 1, 1, 1, 0, 0], [5, 4, 3]),
    ([0, 0, 1, 1, 1, 1, 1, 0], [6, 5, 4, 3]),
    ([0, 0, 1, 1, 1, 1, 1, 1], [7, 6, 5, 4, 3]),
    ([0, 1, 1, 1, 0, 0, 0, 0], [1, 3]),
    ([0, 1, 1, 1, 1, 0, 0, 0], [4, 1, 3]),
    ([0, 1, 1, 1, 1, 1, 0, 0], [5, 4, 1, 3]),
    ([0, 1, 1, 1, 1, 1, 1, 0], [6, 5, 4, 1, 3]),
    ([0, 1, 1, 1, 1, 1, 1, 1], [7, 6, 5, 4, 1, 3]),
    ([0, 1, 1, 2, 1, 0, 0, 0], [3, 4, 1, 3]),
    ([0, 1, 1, 2, 1, 1, 0, 0], [5, 3, 4, 1, 3]),
    ([0, 1, 1, 2, 1, 1, 1, 0], [6, 5, 3, 4, 1, 3]),
    ([0, 1, 1, 2, 1, 1, 1, 1], [7, 6, 5, 3, 4, 1, 3]),
    ([0, 1, 1, 2, 2, 1, 0, 0], [4, 5, 3, 4, 1, 3]),
    ([0, 1, 1, 2, 2, 1, 1, 0], [6, 4, 5, 3, 4, 1, 3]),
    ([0, 1, 1, 2, 2, 1, 1, 1], [7, 6, 4, 5, 3, 4, 1, 3]),
    ([0, 1, 1, 2, 2, 2, 1, 0], [5, 6, 4, 5, 3, 4, 1, 3]),
    ([0, 1, 1, 2, 2, 2, 1, 1], [7, 5, 6, 4, 5, 3, 4, 1, 3]),
    ([0, 1, 1, 2, 2, 2, 2, 1], [6, 7, 5, 6, 4, 5, 3, 4, 1, 3]),
    ([1, 2, 3, 4, 3, 2, 1, 0], [2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]),
    ([1, 2, 3, 4, 3, 2, 1, 1], [7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]),
    ([1, 2, 3, 4, 3, 2, 2, 1], [
      6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]),
    ([1, 2, 3, 4, 3, 3, 2, 1], [
      5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]),
    ([1, 2, 3, 4, 4, 3, 2, 1], [
      4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]),
    ([1, 2, 3, 5, 4, 3, 2, 1], [
      3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]),
    ([1, 3, 3, 5, 4, 3, 2, 1], [
      1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3])
  ]

set_option maxRecDepth 100000 in
theorem e8RootWords_spec : ∀ j : Fin 8,
    (e8Word (e8RootWords j)).foldr (reflect Tag.E8) (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) =
      (Pi.single (j : Fin Tag.E8.rank) 1 : Fin Tag.E8.rank → ℤ) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8A2PairWords_spec : ∀ ent ∈ e8A2PairWords,
    (e8Word ent.2).foldr (reflect Tag.E8) (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) =
        (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) ∧
      (e8Word ent.2).foldr (reflect Tag.E8) (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) =
        toVec Tag.E8.rank ent.1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8A2PairWords_complete :
    ∀ l ∈ Tag.E8.artifactRoots,
      iform (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) (toVec Tag.E8.rank l) = -1 →
        l ∈ e8A2PairWords.map Prod.fst := by
  decide +kernel

theorem wordProd_smul_E8 (l : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem Tag.E8).wordProd l • v = l.foldr (reflect Tag.E8) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

section


theorem iform_self_E8 {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) : iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  have h1 : Tag.E8.symmetrizer j j = 1 := by
    change (1 : Matrix (Fin 8) (Fin 8) ℤ) j j = 1
    exact Matrix.one_apply_eq j
  rw [hj, h1, mul_one]

theorem exists_weyl_a2Pair_E8 {α β : Fin Tag.E8.rank → ℤ} (h : IsA2Pair α β) :
    ∃ v : WeylGroup Tag.E8, v • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = α ∧
      v • (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) = β := by
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 h.isRoot_fst
  set t := (coxeterSystem Tag.E8).wordProd (e8Word (e8RootWords j)) with ht
  have htj : t • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = Pi.single j 1 := by
    rw [ht, wordProd_smul_E8]
    exact e8RootWords_spec j
  set u := w * t with hu
  have hu0 : u • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = α := by rw [hu, mul_smul, htj, hw]
  set β' := u⁻¹ • β with hβ'
  have hβ'r : IsRoot Tag.E8 β' := IsRoot.smul h.isRoot_snd u⁻¹
  have hform : iform (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) β' = -1 := by
    have e : iform (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) β' = iform α β := by
      rw [← iform_smul u, hu0, hβ', smul_inv_smul]
    have h2 := h.two_iform
    rw [iform_self_E8 h.isRoot_fst] at h2
    rw [e]
    omega
  obtain ⟨l, hl, hβ'l⟩ := isRoot_iff_exists_mem.1 hβ'r
  obtain ⟨ent, hent, hentl⟩ := List.mem_map.1 (e8A2PairWords_complete l hl (hβ'l ▸ hform))
  obtain ⟨h0, h2⟩ := e8A2PairWords_spec ent hent
  refine ⟨u * (coxeterSystem Tag.E8).wordProd (e8Word ent.2), ?_, ?_⟩
  · rw [mul_smul, wordProd_smul_E8, h0, hu0]
  · rw [mul_smul, wordProd_smul_E8, h2, hentl, ← hβ'l, hβ', smul_inv_smul]

end

private theorem det_monoM₁ {K : Type*} [Field K] (a b c : K) : (monoM₁ a b c).det = a * b * c := by
  simp [monoM₁, Matrix.det_fin_three]
  ring

private theorem three_ne_zero_of_ringChar {L : Type} [Field L] (hL : ringChar L ≠ 3) :
    (3 : L) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
  rw [ringChar.spec] at h'
  rcases (Nat.dvd_prime Nat.prime_three).1 h' with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hL h1

private theorem exists_cube_root_unity (L : Type) [Field L] [IsAlgClosed L] :
    ∃ ω : L, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L)
    (by
      rw [Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_add_eq_left_of_degree_lt]
      · simp
      · simp
      · rw [Polynomial.degree_add_eq_left_of_degree_lt] <;> simp)
  exact ⟨ω, by simpa using hω⟩

section


theorem weylElt_eq_xUnit_yUnit (L : Type) [Field L] (i : Fin Tag.E8.rank) :
    weylElt Tag.E8 L i 1 = xUnit Tag.E8 L i 1 * yUnit Tag.E8 L i (-1) * xUnit Tag.E8 L i 1 := by
  refine Units.ext ?_
  simp [weylElt, xUnit, yUnit]

theorem xUnit_mem_subsystemGroup13 (L : Type) [Field L] {i : Fin Tag.E8.rank}
    (hi : i ∈ e8support13) (c : L) : xUnit Tag.E8 L i c ∈ subsystemGroup Tag.E8 L e8support13 :=
  Subgroup.subset_closure ⟨i, hi, c, Or.inl rfl⟩

theorem yUnit_mem_subsystemGroup13 (L : Type) [Field L] {i : Fin Tag.E8.rank}
    (hi : i ∈ e8support13) (c : L) : yUnit Tag.E8 L i c ∈ subsystemGroup Tag.E8 L e8support13 :=
  Subgroup.subset_closure ⟨i, hi, c, Or.inr rfl⟩

theorem weylElt_mem_subsystemGroup13 (L : Type) [Field L] {i : Fin Tag.E8.rank}
    (hi : i ∈ e8support13) : weylElt Tag.E8 L i 1 ∈ subsystemGroup Tag.E8 L e8support13 := by
  rw [weylElt_eq_xUnit_yUnit]
  exact mul_mem (mul_mem (xUnit_mem_subsystemGroup13 L hi 1) (yUnit_mem_subsystemGroup13 L hi _))
    (xUnit_mem_subsystemGroup13 L hi 1)

theorem e8a2Mat_weylElt_mul (L : Type) [Field L] :
    e8a2Mat (weylElt Tag.E8 L (e8Index 0) 1 * weylElt Tag.E8 L (e8Index 2) 1) =
      !![0, 0, 1; -1, 0, 0; 0, -1, 0] := by
  have h0 := mem_e8support13_0
  have h2 := mem_e8support13_2
  rw [e8a2Mat_mul (weylElt_mem_subsystemGroup13 L h0) (weylElt_mem_subsystemGroup13 L h2),
    weylElt_eq_xUnit_yUnit, weylElt_eq_xUnit_yUnit,
    e8a2Mat_mul (mul_mem (xUnit_mem_subsystemGroup13 L h0 1) (yUnit_mem_subsystemGroup13 L h0 _))
      (xUnit_mem_subsystemGroup13 L h0 1),
    e8a2Mat_mul (xUnit_mem_subsystemGroup13 L h0 1) (yUnit_mem_subsystemGroup13 L h0 _),
    e8a2Mat_mul (mul_mem (xUnit_mem_subsystemGroup13 L h2 1) (yUnit_mem_subsystemGroup13 L h2 _))
      (xUnit_mem_subsystemGroup13 L h2 1),
    e8a2Mat_mul (xUnit_mem_subsystemGroup13 L h2 1) (yUnit_mem_subsystemGroup13 L h2 _),
    e8a2Mat_x1, e8a2Mat_y1, e8a2Mat_x3, e8a2Mat_y3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem sigmaSetE8_eq_a2Roots (v : WeylGroup Tag.E8) :
    sigmaSetE8 v = a2Roots (v • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ))
      (v • (Pi.single 2 1 : Fin Tag.E8.rank → ℤ)) := by
  have hb01 : e8a2Weight 0 - e8a2Weight 1 = (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) := by
    decide +kernel
  have hb12 : e8a2Weight 1 - e8a2Weight 2 = (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) := by
    decide +kernel
  have hσ : ∀ i j, sigmaRootE8 v i j = v • (e8a2Weight i - e8a2Weight j) := fun i j => by
    rw [sigmaRootE8, wbE8, wbE8, smul_sub]
  have h01 : sigmaRootE8 v 0 1 = v • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) := by rw [hσ, hb01]
  have h12 : sigmaRootE8 v 1 2 = v • (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) := by rw [hσ, hb12]
  have h02 : sigmaRootE8 v 0 2 = v • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) +
      v • (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) := by
    rw [← sigmaRootE8_add v 0 1 2, h01, h12]
  have h10 : sigmaRootE8 v 1 0 = -(v • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ)) := by
    rw [← sigmaRootE8_neg, h01]
  have h21 : sigmaRootE8 v 2 1 = -(v • (Pi.single 2 1 : Fin Tag.E8.rank → ℤ)) := by
    rw [← sigmaRootE8_neg, h12]
  have h20 : sigmaRootE8 v 2 0 = -(v • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) +
      v • (Pi.single 2 1 : Fin Tag.E8.rank → ℤ)) := by
    rw [← sigmaRootE8_neg, h02]
  rw [sigmaSetE8_eq]
  ext r
  simp only [a2Roots, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Or.inl h01
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h02))))
    · exact Or.inr (Or.inl h10)
    · exact absurd rfl hij
    · exact Or.inr (Or.inr (Or.inl h12))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h20))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h21)))
    · exact absurd rfl hij
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, h01.symm⟩
    · exact ⟨1, 0, by decide, h10.symm⟩
    · exact ⟨1, 2, by decide, h12.symm⟩
    · exact ⟨2, 1, by decide, h21.symm⟩
    · exact ⟨0, 2, by decide, h02.symm⟩
    · exact ⟨2, 0, by decide, h20.symm⟩

theorem a2BlockToral_E8 : A2BlockToral Tag.E8 := by
  intro L _ _ hL α β hA2
  obtain ⟨v, hv0, hv2⟩ := exists_weyl_a2Pair_E8 hA2
  have hset : sigmaSetE8 v = a2Roots α β := by rw [sigmaSetE8_eq_a2Roots, hv0, hv2]
  have hrange : ∀ X : SL(3, L), rhoSigmaE8 L v X ∈ rootSpan Tag.E8 L (a2Roots α β) := fun X => by
    rw [← hset, ← rhoSigmaE8_range]
    exact ⟨X, rfl⟩
  set V := canonicalRep (coxeterSystem Tag.E8) L v with hV
  set n₀ := weylElt Tag.E8 L (e8Index 0) 1 with hn₀
  set n₂ := weylElt Tag.E8 L (e8Index 2) 1 with hn₂
  have hnQ : n₀ * n₂ ∈ subsystemGroup Tag.E8 L e8support13 :=
    mul_mem (weylElt_mem_subsystemGroup13 L mem_e8support13_0)
      (weylElt_mem_subsystemGroup13 L mem_e8support13_2)
  set M₀ : SL(3, L) := e8a2Rep L ⟨n₀ * n₂, hnQ⟩ with hM₀
  have hM₀mat : (M₀ : Matrix (Fin 3) (Fin 3) L) = !![0, 0, 1; -1, 0, 0; 0, -1, 0] := by
    rw [hM₀, coe_e8a2Rep]
    exact e8a2Mat_weylElt_mul L
  have hρM₀ : rhoSigmaE8 L v M₀ = V * (n₀ * n₂) * V⁻¹ := by
    rw [rhoSigmaE8_apply, hM₀, e8rhoJ_e8a2Rep hnQ]
  have hVN : V ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L v
  have hn₀N : n₀ ∈ monomialSubgroup Tag.E8 L := weylElt_mem_monomialSubgroup _
  have hn₂N : n₂ ∈ monomialSubgroup Tag.E8 L := weylElt_mem_monomialSubgroup _
  have hmN : rhoSigmaE8 L v M₀ ∈ monomialSubgroup Tag.E8 L := by
    rw [hρM₀]
    exact mul_mem (mul_mem hVN (mul_mem hn₀N hn₂N)) (inv_mem hVN)
  refine ⟨rhoSigmaE8 L v M₀, hrange M₀, hmN, ?_, ?_⟩
  ·
    have e : (⟨rhoSigmaE8 L v M₀, hmN⟩ : monomialSubgroup Tag.E8 L) =
        ⟨V, hVN⟩ * (⟨n₀, hn₀N⟩ * ⟨n₂, hn₂N⟩) * (⟨V, hVN⟩)⁻¹ := Subtype.ext hρM₀
    have hπV : weylQuotientHom Tag.E8 L ⟨V, hVN⟩ = v :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep v)
    have hπ0 : weylQuotientHom Tag.E8 L ⟨n₀, hn₀N⟩ = simple Tag.E8 0 :=
      weylQuotientHom_eq (mapsRootLines_weylElt _)
    have hπ2 : weylQuotientHom Tag.E8 L ⟨n₂, hn₂N⟩ = simple Tag.E8 2 :=
      weylQuotientHom_eq (mapsRootLines_weylElt _)
    have h0 : rootReflection α = v * simple Tag.E8 0 * v⁻¹ := rootReflection_eq_conj hv0
    have h2 : rootReflection β = v * simple Tag.E8 2 * v⁻¹ := rootReflection_eq_conj hv2
    rw [e, map_mul, map_mul, map_inv, map_mul, hπV, hπ0, hπ2, h0, h2]
    group
  ·
    intro t ht
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    have htor := rhoSigmaE8_torus (L := L) v b
    set d : Fin 3 → Lˣ := fun i => rootChar b (wbE8 v i) with hd
    obtain ⟨ω, hω⟩ := exists_cube_root_unity L
    have h3 := three_ne_zero_of_ringChar hL
    set a₀ : L := -((d 0 : Lˣ) : L) with ha₀
    set b₀ : L := -((d 1 : Lˣ) : L) with hb₀
    set c₀ : L := ((d 2 : Lˣ) : L) with hc₀
    have habc0 : a₀ * b₀ * c₀ ≠ 0 := by
      simp only [ha₀, hb₀, hc₀, neg_mul, mul_neg, neg_neg, ne_eq, mul_eq_zero, Units.ne_zero,
        or_self, not_false_eq_true]
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (a₀ * b₀ * c₀) (by norm_num : 0 < 3)
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hμ
      exact habc0 hμ.symm
    have hprod : a₀ / μ * (b₀ / μ) * (c₀ / μ) = 1 := by
      rw [div_mul_div_comm, div_mul_div_comm, ← hμ]
      field_simp
    have hdet : (monoM₁ (a₀ / μ) (b₀ / μ) (c₀ / μ)).det = 1 := by rw [det_monoM₁, hprod]
    set m' : SL(3, L) := ⟨monoM₁ (a₀ / μ) (b₀ / μ) (c₀ / μ), hdet⟩ with hm'
    obtain ⟨g, hg⟩ := exists_sl3_conj_M₁ hω h3 hprod m' rfl
    refine ⟨rhoSigmaE8 L v g⁻¹, hrange _, ?_⟩
    have e1 : rhoSigmaE8 L v g⁻¹ * (rhoSigmaE8 L v M₀ * rootDiagUnit Tag.E8 b) *
        (rhoSigmaE8 L v g⁻¹)⁻¹ =
        rhoSigmaE8 L v (g⁻¹ * M₀ * conjDiag3 d g) * rootDiagUnit Tag.E8 b := by
      rw [map_mul, map_mul, ← htor g, map_inv, inv_inv]
      group
    rw [e1]
    refine mul_mem (rhoSigmaE8_diagonal v _ ?_) ht
    have hMD : (M₀ : Matrix (Fin 3) (Fin 3) L) * (diagGL3 d : Matrix (Fin 3) (Fin 3) L) =
        μ • (m' : Matrix (Fin 3) (Fin 3) L) := by
      rw [hM₀mat]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hm', monoM₁, diagGL3, Matrix.mul_apply, Fin.sum_univ_three, ha₀, hb₀, hc₀] <;>
        field_simp
    have hg' : (g⁻¹ : SL(3, L)).val * m'.val * g.val = Matrix.diagonal ![1, ω, ω ^ 2] := by
      simpa [Matrix.SpecialLinearGroup.coe_mul] using hg
    have key : ((g⁻¹ * M₀ * conjDiag3 d g : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        μ • Matrix.diagonal ![1, ω, ω ^ 2] *
          Matrix.diagonal (fun k => (((d k)⁻¹ : Lˣ) : L)) := by
      calc ((g⁻¹ * M₀ * conjDiag3 d g : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
            (g⁻¹ : SL(3, L)).val * M₀.val *
              ((diagGL3 d : Matrix (Fin 3) (Fin 3) L) * g.val *
                ((diagGL3 d)⁻¹ : GL (Fin 3) L)) := by
            simp only [Matrix.SpecialLinearGroup.coe_mul, coe_conjDiag3]
        _ = (g⁻¹ : SL(3, L)).val * (M₀.val * (diagGL3 d : Matrix (Fin 3) (Fin 3) L)) * g.val *
              ((diagGL3 d)⁻¹ : GL (Fin 3) L) := by simp only [Matrix.mul_assoc]
        _ = μ • ((g⁻¹ : SL(3, L)).val * m'.val * g.val) * ((diagGL3 d)⁻¹ : GL (Fin 3) L) := by
            rw [hMD]
            simp only [Matrix.mul_smul, Matrix.smul_mul]
        _ = _ := by
            rw [hg']
            rfl
    intro i j hij
    rw [key, Matrix.smul_mul, Matrix.diagonal_mul_diagonal, Matrix.smul_apply,
      Matrix.diagonal_apply_ne _ hij, smul_zero]

end

end CFSG.HardMathSupport.Timmesfeld.CrossChar
