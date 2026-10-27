module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.A2Words

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph


variable {K : Type} [Field K] [Finite K]

theorem wordG_flatten_mem {M : Subgroup ↥(adjointGroup Tag.D4 K)} (ws : List (List ℕ))
    (h : ∀ v ∈ ws, wordG K v ∈ M) : wordG K ws.flatten ∈ M := by
  induction ws with
  | nil => exact M.one_mem
  | cons v ws ih =>
    rw [List.flatten_cons, wordG_append]
    exact M.mul_mem (h v (by simp)) (ih fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem wordG_conj_back (hK : Nat.card K = 2) (c w : List ℕ) :
    wordG K w = wordG K c * wordG K (c.reverse ++ w ++ c) * (wordG K c)⁻¹ := by
  have h2 := two_eq_zero_of_card_two' hK
  rw [wordG_append, wordG_append, ← wordG_inv h2]
  group

theorem eq_top_of_chains (hK : Nat.card K = 2) {x cs cd : List ℕ} (hx : Letters x)
    (hcs : Letters cs) (hcd : Letters cd) {M : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hCM : ∀ g ∈ Subgroup.centralizer ({wordG K x} : Set ↥(adjointGroup Tag.D4 K)), g ∈ M)
    (hcsM : wordG K cs ∈ M) (hcdM : wordG K cd ∈ M)
    (h0 : CentB x (cs.reverse ++ [0, 4] ++ cs)) (h1 : CentB x (cs.reverse ++ [1, 6] ++ cs))
    (h3 : CentB x (cs.reverse ++ [3, 10] ++ cs)) (hx2 : CentB x (cd.reverse ++ [2] ++ cd))
    (hy2 : CentB x (cd.reverse ++ [8] ++ cd)) : M = ⊤ := by
  have key : ∀ (c w : List ℕ), Letters c → Letters w → wordG K c ∈ M →
      CentB x (c.reverse ++ w ++ c) → wordG K w ∈ M := by
    intro c w hc hw hcM hcen
    rw [wordG_conj_back hK c w]
    refine M.mul_mem (M.mul_mem hcM (hCM _ ?_)) (M.inv_mem hcM)
    exact mem_centralizer_of_wordN hK hx
      (letters_append (letters_append (letters_reverse hc) hw) hc) hcen
  exact eq_top_of_psi hK (key cs _ hcs (by decide) hcsM h0) (key cs _ hcs (by decide) hcsM h1)
    (key cs _ hcs (by decide) hcsM h3) (key cd _ hcd (by decide) hcdM hx2)
    (key cd _ hcd (by decide) hcdM hy2)

theorem quadSet_mems {x : ↥(adjointGroup Tag.D4 K)} {β : MulAut ↥(adjointGroup Tag.D4 K)} :
    (∀ g ∈ Subgroup.centralizer ({x} : Set ↥(adjointGroup Tag.D4 K)),
      g ∈ Subgroup.closure (quadSet x β)) ∧
    (∀ g ∈ fixedSubgroup β, g ∈ Subgroup.closure (quadSet x β)) ∧
    (∀ g ∈ fixedSubgroup (MulAut.conj x * β), g ∈ Subgroup.closure (quadSet x β)) ∧
    (∀ g ∈ fixedSubgroup ((MulAut.conj x)⁻¹ * β), g ∈ Subgroup.closure (quadSet x β)) :=
  ⟨fun _ hg => Subgroup.subset_closure (Or.inl (Or.inl (Or.inl hg))),
    fun _ hg => Subgroup.subset_closure (Or.inl (Or.inl (Or.inr hg))),
    fun _ hg => Subgroup.subset_closure (Or.inl (Or.inr hg)),
    fun _ hg => Subgroup.subset_closure (Or.inr hg)⟩

theorem closure_quadSet_y₀ :
    Subgroup.closure (quadSet (wordG K y0W) (gammaP K (uSL 1 * vSL 1))) = ⊤ := by
  have hγ : (MulAut.conj (wordG K y0W))⁻¹ * gammaP K (uSL 1 * vSL 1) = d4Graph K 1 := by
    rw [gammaP, y₀_eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [eq_top_iff, ← closure_eq_top_long (K := K) (uSL 1 * vSL 1), Subgroup.closure_le]
  rintro g (hg | hg)
  · rw [← y₀_eq] at hg
    exact quadSet_mems.1 g hg
  · rw [← hγ] at hg
    exact quadSet_mems.2.2.2 g hg

theorem closure_quadSet_d (hK : Nat.card K = 2) :
    Subgroup.closure (quadSet (wordG K dW) (gammaP K (uSL 1 * vSL 1))) = ⊤ := by
  obtain ⟨hC, hF, hX, -⟩ := quadSet_mems (x := wordG K dW) (β := gammaP K (uSL 1 * vSL 1))
  have n1 : wordG K [0, 19, 21, 3, 13, 4] ∈ Subgroup.closure (quadSet (wordG K dW)
      (gammaP K (uSL 1 * vSL 1))) :=
    hX _ (mem_fix_conj_of_wordN hK (by decide) (by decide) (by decide +kernel))
  have n2 : wordG K [8, 20, 15] ∈ Subgroup.closure (quadSet (wordG K dW)
      (gammaP K (uSL 1 * vSL 1))) :=
    hC _ (mem_centralizer_of_wordN hK (by decide) (by decide) (by decide +kernel))
  have n3 : wordG K [5, 3, 12, 9, 1] ∈ Subgroup.closure (quadSet (wordG K dW)
      (gammaP K (uSL 1 * vSL 1))) :=
    hF _ (mem_fix_of_wordN hK (by decide) (by decide +kernel))
  have n4 : wordG K [2] ∈ Subgroup.closure (quadSet (wordG K dW) (gammaP K (uSL 1 * vSL 1))) :=
    hC _ (mem_centralizer_of_wordN hK (by decide) (by decide) (by decide +kernel))
  have n5 : wordG K [15, 20] ∈ Subgroup.closure (quadSet (wordG K dW)
      (gammaP K (uSL 1 * vSL 1))) :=
    hC _ (mem_centralizer_of_wordN hK (by decide) (by decide) (by decide +kernel))
  refine eq_top_of_chains hK (x := dW)
    (cs := [[0, 19, 21, 3, 13, 4], [8, 20, 15], [5, 3, 12, 9, 1], [2], [5, 3, 12, 9, 1],
      [15, 20], [5, 3, 12, 9, 1]].flatten) (cd := []) (by decide) (by decide) (by decide) hC
    (wordG_flatten_mem _ (by
      simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
      exact ⟨n1, n2, n3, n4, n3, n5, n3, fun _ h => absurd h List.not_mem_nil⟩))
    (by rw [wordG_nil]; exact Subgroup.one_mem _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem closure_quadSet_ry₀ (hK : Nat.card K = 2) :
    Subgroup.closure (quadSet (wordG K (rW ++ y0W)) (gammaP K (uSL 1 * vSL 1))) = ⊤ := by
  obtain ⟨hC, hF, -, hY⟩ := quadSet_mems (x := wordG K (rW ++ y0W))
    (β := gammaP K (uSL 1 * vSL 1))
  have n1 : wordG K [19, 6, 15, 2, 8, 11] ∈ Subgroup.closure (quadSet (wordG K (rW ++ y0W))
      (gammaP K (uSL 1 * vSL 1))) :=
    hY _ (mem_fix_conj_inv_of_wordN hK (by decide) (by decide) (by decide +kernel))
  have n2 : wordG K [14, 20, 9, 2, 7, 16] ∈ Subgroup.closure (quadSet (wordG K (rW ++ y0W))
      (gammaP K (uSL 1 * vSL 1))) :=
    hC _ (mem_centralizer_of_wordN hK (by decide) (by decide) (by decide +kernel))
  have n3 : wordG K [5, 3, 12, 9, 1] ∈ Subgroup.closure (quadSet (wordG K (rW ++ y0W))
      (gammaP K (uSL 1 * vSL 1))) :=
    hF _ (mem_fix_of_wordN hK (by decide) (by decide +kernel))
  have n4 : wordG K [23, 5, 18, 2, 1, 8] ∈ Subgroup.closure (quadSet (wordG K (rW ++ y0W))
      (gammaP K (uSL 1 * vSL 1))) :=
    hC _ (mem_centralizer_of_wordN hK (by decide) (by decide) (by decide +kernel))
  have n5 : wordG K [2, 8] ∈ Subgroup.closure (quadSet (wordG K (rW ++ y0W))
      (gammaP K (uSL 1 * vSL 1))) :=
    hF _ (mem_fix_of_wordN hK (by decide) (by decide +kernel))
  refine eq_top_of_chains hK (x := rW ++ y0W)
    (cs := [[19, 6, 15, 2, 8, 11], [14, 20, 9, 2, 7, 16], [5, 3, 12, 9, 1]].flatten)
    (cd := [[23, 5, 18, 2, 1, 8], [2, 8]].flatten) (by decide) (by decide) (by decide) hC
    (wordG_flatten_mem _ (by
      simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
      exact ⟨n1, n2, n3, fun _ h => absurd h List.not_mem_nil⟩))
    (wordG_flatten_mem _ (by
      simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
      exact ⟨n4, n5, fun _ h => absurd h List.not_mem_nil⟩))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem closure_quadSet_ry₀sq (hK : Nat.card K = 2) :
    Subgroup.closure (quadSet (wordG K (rW ++ y0W ++ y0W)) (gammaP K (uSL 1 * vSL 1))) = ⊤ := by
  obtain ⟨hC, hF, -, -⟩ := quadSet_mems (x := wordG K (rW ++ y0W ++ y0W))
    (β := gammaP K (uSL 1 * vSL 1))
  have n1 : wordG K [4, 16, 17, 10, 14] ∈ Subgroup.closure (quadSet (wordG K (rW ++ y0W ++ y0W))
      (gammaP K (uSL 1 * vSL 1))) :=
    hF _ (mem_fix_of_wordN hK (by decide) (by decide +kernel))
  have n2 : wordG K [13, 4, 6, 2, 12, 18] ∈ Subgroup.closure
      (quadSet (wordG K (rW ++ y0W ++ y0W)) (gammaP K (uSL 1 * vSL 1))) :=
    hC _ (mem_centralizer_of_wordN hK (by decide) (by decide) (by decide +kernel))
  have n3 : wordG K [5, 3, 12, 9, 1] ∈ Subgroup.closure (quadSet (wordG K (rW ++ y0W ++ y0W))
      (gammaP K (uSL 1 * vSL 1))) :=
    hF _ (mem_fix_of_wordN hK (by decide) (by decide +kernel))
  have n4 : wordG K [2, 22, 14, 12, 8, 10] ∈ Subgroup.closure
      (quadSet (wordG K (rW ++ y0W ++ y0W)) (gammaP K (uSL 1 * vSL 1))) :=
    hC _ (mem_centralizer_of_wordN hK (by decide) (by decide) (by decide +kernel))
  have n5 : wordG K [2, 8] ∈ Subgroup.closure (quadSet (wordG K (rW ++ y0W ++ y0W))
      (gammaP K (uSL 1 * vSL 1))) :=
    hF _ (mem_fix_of_wordN hK (by decide) (by decide +kernel))
  refine eq_top_of_chains hK (x := rW ++ y0W ++ y0W)
    (cs := [[4, 16, 17, 10, 14], [13, 4, 6, 2, 12, 18], [5, 3, 12, 9, 1]].flatten)
    (cd := [[2, 22, 14, 12, 8, 10], [2, 8]].flatten) (by decide) (by decide) (by decide) hC
    (wordG_flatten_mem _ (by
      simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
      exact ⟨n1, n2, n3, fun _ h => absurd h List.not_mem_nil⟩))
    (wordG_flatten_mem _ (by
      simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
      exact ⟨n4, n5, fun _ h => absurd h List.not_mem_nil⟩))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
