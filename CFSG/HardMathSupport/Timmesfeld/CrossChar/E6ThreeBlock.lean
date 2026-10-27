module

public import CFSG.HardMathSupport.Timmesfeld.Torality.A2Block
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.RankThree.PartOne.TCX.E.E6A2Sigma

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KF4
open CFSG.RankThree.E6 (chain13 chainRoot)

open CFSG.RankThree.PartOne.TCX.E (a2Std₁ chainRoot_eq_weight_sub)


@[expose] def e6BlockWord (l : List ℕ) : List (Fin Tag.E6.rank) :=
  l.map fun n => (⟨n % 6, Nat.mod_lt n (by decide)⟩ : Fin 6)

@[expose] def e6BlockRootWords : Fin 6 → List ℕ :=
  ![[], [3, 2, 1, 3, 0, 2], [0, 2], [2, 3, 0, 2], [3, 4, 2, 3, 0, 2], [4, 5, 3, 4, 2, 3, 0, 2]]

set_option maxRecDepth 100000 in
theorem e6BlockRootWords_spec : ∀ j : Fin 6,
    (e6BlockWord (e6BlockRootWords j)).foldr (reflect Tag.E6)
      (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) =
        (Pi.single (j : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

@[expose] def e6BlockPairWords : List (List ℤ × List ℕ) :=
  [([-1, -1, -1, -2, -2, -1], [4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -1, -1], [5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -2, -1, 0], [2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -1, -1, -1], [5, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -1, -1, 0], [2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, -1, -1, -1, 0, 0], [4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, -1, -1, -1], [5, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, -1, -1, 0], [2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, -1, 0, 0], [4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([-1, 0, -1, 0, 0, 0], [3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2]),
    ([0, 0, 1, 0, 0, 0], []),
    ([0, 0, 1, 1, 0, 0], [3]),
    ([0, 0, 1, 1, 1, 0], [4, 3]),
    ([0, 0, 1, 1, 1, 1], [5, 4, 3]),
    ([0, 1, 1, 1, 0, 0], [1, 3]),
    ([0, 1, 1, 1, 1, 0], [4, 1, 3]),
    ([0, 1, 1, 1, 1, 1], [5, 4, 1, 3]),
    ([0, 1, 1, 2, 1, 0], [3, 4, 1, 3]),
    ([0, 1, 1, 2, 1, 1], [5, 3, 4, 1, 3]),
    ([0, 1, 1, 2, 2, 1], [4, 5, 3, 4, 1, 3])]

set_option maxRecDepth 100000 in
theorem e6BlockPairWords_spec : ∀ ent ∈ e6BlockPairWords,
    (e6BlockWord ent.2).foldr (reflect Tag.E6) (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) =
        (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∧
      (e6BlockWord ent.2).foldr (reflect Tag.E6) (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) =
        toVec Tag.E6.rank ent.1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e6BlockPairWords_complete :
    ∀ l ∈ Tag.E6.artifactRoots,
      iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (toVec Tag.E6.rank l) = -1 →
        l ∈ e6BlockPairWords.map Prod.fst := by
  decide +kernel

theorem wordProd_smul_E6' (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    (coxeterSystem Tag.E6).wordProd l • v = l.foldr (reflect Tag.E6) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

section


theorem iform_self_E6 {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) : iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  have h1 : Tag.E6.symmetrizer j j = 1 := by
    change (1 : Matrix (Fin 6) (Fin 6) ℤ) j j = 1
    exact Matrix.one_apply_eq j
  rw [hj, h1, mul_one]

theorem exists_weyl_a2Pair_E6 {α β : Fin Tag.E6.rank → ℤ} (h : IsA2Pair α β) :
    ∃ v : WeylGroup Tag.E6, v • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = α ∧
      v • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = β := by
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 h.isRoot_fst
  set t := (coxeterSystem Tag.E6).wordProd (e6BlockWord (e6BlockRootWords j)) with ht
  have htj : t • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := by
    rw [ht, wordProd_smul_E6']
    exact e6BlockRootWords_spec j
  set u := w * t with hu
  have hu0 : u • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = α := by rw [hu, mul_smul, htj, hw]
  set β' := u⁻¹ • β with hβ'
  have hβ'r : IsRoot Tag.E6 β' := IsRoot.smul h.isRoot_snd u⁻¹
  have hform : iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) β' = -1 := by
    have e : iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) β' = iform α β := by
      rw [← iform_smul u, hu0, hβ', smul_inv_smul]
    have h2 := h.two_iform
    rw [iform_self_E6 h.isRoot_fst] at h2
    rw [e]
    omega
  obtain ⟨l, hl, hβ'l⟩ := isRoot_iff_exists_mem.1 hβ'r
  obtain ⟨ent, hent, hentl⟩ := List.mem_map.1 (e6BlockPairWords_complete l hl (hβ'l ▸ hform))
  obtain ⟨h0, h2⟩ := e6BlockPairWords_spec ent hent
  refine ⟨u * (coxeterSystem Tag.E6).wordProd (e6BlockWord ent.2), ?_, ?_⟩
  · rw [mul_smul, wordProd_smul_E6', h0, hu0]
  · rw [mul_smul, wordProd_smul_E6', h2, hentl, ← hβ'l, hβ', smul_inv_smul]

end

theorem chainRoot13_zero_one :
    chainRoot chain13 0 1 = (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

theorem chainRoot13_one_two :
    chainRoot chain13 1 2 = (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

section


theorem e6Std_frame (L : Type) [Field L] :
    IsA2Frame (a2Std₁.ρ L) (fun i j => chainRoot chain13 i j) where
  injective := a2Std₁.inj L
  isRoot i j hij := ((a2Std₁.roots _).2 ⟨i, j, hij, rfl⟩).1
  neg i j := by rw [chainRoot_eq_weight_sub, chainRoot_eq_weight_sub, neg_sub]
  add i j k := by
    rw [chainRoot_eq_weight_sub, chainRoot_eq_weight_sub, chainRoot_eq_weight_sub]
    abel
  transv i j hij := a2Std₁.gen L i j hij
  range := by
    rw [a2Std₁.range, subsystemGroup_eq_rootSpan]
    congr 1
    ext r
    exact a2Std₁.roots r
  diag A hA := a2Std₁.diag L A hA

theorem a2BlockToral_E6 : A2BlockToral Tag.E6 := by
  intro L _ _ hL α β hpair
  obtain ⟨v, h1, h2⟩ := exists_weyl_a2Pair_E6 hpair
  have hfr := (e6Std_frame L).transport v
  have key := a2BlockAt_of_frame hL hfr
  have e1 : v • chainRoot chain13 0 1 = α := by rw [chainRoot13_zero_one]; exact h1
  have e2 : v • chainRoot chain13 1 2 = β := by rw [chainRoot13_one_two]; exact h2
  simp only [e1, e2] at key
  exact key

theorem monomialToralAt_E6_three : MonomialToralAt Tag.E6 3 :=
  monomialToralAt_three_of_block a2BlockToral_E6

end

end CFSG.HardMathSupport.Timmesfeld.CrossChar
