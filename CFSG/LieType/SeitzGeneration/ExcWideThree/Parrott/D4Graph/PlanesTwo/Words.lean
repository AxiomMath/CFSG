module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.Bits
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.G2Pair
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Lang.D4Three
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree


variable {K : Type} [Field K]

theorem xPar_mul_self (h2 : (2 : K) = 0) (α : Fin Tag.D4.rank → ℤ) :
    xPar (rootOperatorFamily Tag.D4) α (1 : K) * xPar (rootOperatorFamily Tag.D4) α 1 = 1 := by
  rw [← xPar_add, one_add_one_eq_two, h2, xPar_zero]

theorem wordG_inv (h2 : (2 : K) = 0) (w : List ℕ) : (wordG K w)⁻¹ = wordG K w.reverse := by
  induction w with
  | nil => simp [wordG_nil]
  | cons a w ih =>
    rw [wordG_cons, mul_inv_rev, ih, List.reverse_cons, wordG_append, wordG_cons, wordG_nil,
      mul_one, inv_eq_of_mul_eq_one_right (xPar_mul_self h2 (rt a))]

theorem conj_wordG (h2 : (2 : K) = 0) (v w : List ℕ) :
    wordG K v * wordG K w * (wordG K v)⁻¹ = wordG K (v ++ w ++ v.reverse) := by
  rw [wordG_inv h2, wordG_append, wordG_append]

@[expose] def rhoIdx (a : ℕ) : ℕ :=
  [1, 3, 2, 0, 6, 7, 10, 9, 8, 5, 4, 14, 15, 12, 16, 13, 11, 20, 17, 19, 18, 21, 22, 23].getD a 0

theorem rhoIdx_spec' : ∀ a < 24, permLattice (τ := Tag.D4) TwistTag.D4.perm (rt a) = rt (rhoIdx a) ∧
    rhoIdx a < 24 := by
  decide +kernel

theorem rhoIdx_spec {a : ℕ} (ha : a < 24) :
    permLattice (τ := TwistTag.D4.tag) TwistTag.D4.perm (rt a) = rt (rhoIdx a) ∧ rhoIdx a < 24 :=
  rhoIdx_spec' a ha

theorem d4Graph_one_xPar_rt (h2 : (2 : K) = 0) {a : ℕ} (ha : a < 24) :
    d4Graph K 1 (xPar (rootOperatorFamily Tag.D4) (rt a) (1 : K)) =
      xPar (rootOperatorFamily Tag.D4) (rt (rhoIdx a)) 1 := by
  have hroot : IsRoot Tag.D4 (rt a) := RootWalk.isRoot_rootCertificate_root ha
  have hroot' : IsRoot Tag.D4 (rt (rhoIdx a)) :=
    RootWalk.isRoot_rootCertificate_root (rhoIdx_spec ha).2
  have e := CFSG.LieType.Chevalley.twistHom_id_pinnedX (t := TwistTag.D4) (K := K) h2 hroot 1
  rw [CFSG.LieType.Chevalley.twistHom_id_eq, (rhoIdx_spec ha).1] at e
  apply Subtype.ext
  rw [coe_d4Graph, pow_one, CFSG.StandardType.RootCentExc.coe_xPar_eq_pinnedX h2 _ hroot,
    CFSG.StandardType.RootCentExc.coe_xPar_eq_pinnedX h2 _ hroot', d4P]
  exact e

theorem d4Graph_one_wordG (h2 : (2 : K) = 0) {w : List ℕ} (hw : ∀ a ∈ w, a < 24) :
    d4Graph K 1 (wordG K w) = wordG K (w.map rhoIdx) := by
  induction w with
  | nil => simp [wordG_nil]
  | cons a w ih =>
    rw [wordG_cons, map_mul, d4Graph_one_xPar_rt h2 (hw a (by simp)),
      ih fun b hb => hw b (List.mem_cons_of_mem _ hb), List.map_cons, wordG_cons]

theorem rhoIdx_lt {w : List ℕ} (hw : ∀ a ∈ w, a < 24) : ∀ a ∈ w.map rhoIdx, a < 24 := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
  exact (rhoIdx_spec (hw a ha)).2

theorem rt_single : rt 0 = Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1 ∧
    rt 1 = Pi.single (⟨1, by decide⟩ : Fin Tag.D4.rank) 1 ∧
    rt 2 = Pi.single (⟨2, by decide⟩ : Fin Tag.D4.rank) 1 ∧
    rt 3 = Pi.single (⟨3, by decide⟩ : Fin Tag.D4.rank) 1 ∧
    rt 4 = -Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1 ∧
    rt 6 = -Pi.single (⟨1, by decide⟩ : Fin Tag.D4.rank) 1 ∧
    rt 8 = -Pi.single (⟨2, by decide⟩ : Fin Tag.D4.rank) 1 ∧
    rt 10 = -Pi.single (⟨3, by decide⟩ : Fin Tag.D4.rank) 1 := by
  decide +kernel

theorem sl2At_uv (i : Fin Tag.D4.rank) :
    sl2At K i (uSL 1 * vSL 1) =
      xPar (rootOperatorFamily Tag.D4) (Pi.single i 1) 1 *
        xPar (rootOperatorFamily Tag.D4) (-Pi.single i 1) 1 := by
  rw [map_mul, xPar_single_eq_sl2At, xPar_neg_single_eq_sl2At]

theorem sl2At_uv_eq_wordG :
    sl2At K ⟨0, by decide⟩ (uSL 1 * vSL 1) = wordG K [0, 4] ∧
      sl2At K ⟨1, by decide⟩ (uSL 1 * vSL 1) = wordG K [1, 6] ∧
      sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1) = wordG K [2, 8] ∧
      sl2At K ⟨3, by decide⟩ (uSL 1 * vSL 1) = wordG K [3, 10] := by
  obtain ⟨h0, h1, h2, h3, h4, h6, h8, h10⟩ := rt_single
  simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, sl2At_uv,
    h0, h1, h2, h3, h4, h6, h8, h10, and_self]

theorem gammaP_uv_wordG (h2 : (2 : K) = 0) {w : List ℕ} (hw : ∀ a ∈ w, a < 24) :
    gammaP K (uSL 1 * vSL 1) (wordG K w) = wordG K ([2, 8] ++ w.map rhoIdx ++ [8, 2]) := by
  rw [gammaP, MulAut.mul_apply, MulAut.conj_apply, sl2At_uv_eq_wordG.2.2.1,
    d4Graph_one_wordG h2 hw, conj_wordG h2]
  rfl

theorem rt_lt_of_mem {w : List ℕ} (hw : w.all (· < 24) = true) : ∀ a ∈ w, a < 24 := by
  intro a ha
  have := List.all_eq_true.1 hw a ha
  simpa using this

theorem wordG_eq (h2 : (2 : K) = 0) {v w : List ℕ} (hv : v.all (· < 24) = true)
    (hw : w.all (· < 24) = true) (h : wordN v = wordN w) : wordG K v = wordG K w :=
  wordG_eq_of_wordN_eq h2 (rt_lt_of_mem hv) (rt_lt_of_mem hw) h

theorem two_eq_zero_of_card_two' [Finite K] (hK : Nat.card K = 2) : (2 : K) = 0 :=
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.two_eq_zero_of_card_eq_two hK

theorem eq_top_of_psi [Finite K] (hK : Nat.card K = 2) {M : Subgroup ↥(adjointGroup Tag.D4 K)}
    (h0 : wordG K [0, 4] ∈ M) (h1 : wordG K [1, 6] ∈ M) (h3 : wordG K [3, 10] ∈ M)
    (hx : wordG K [2] ∈ M) (hy : wordG K [8] ∈ M) : M = ⊤ := by
  have h2 := two_eq_zero_of_card_two' hK
  have hmem : ∀ v : List ℕ, v.all (· < 24) = true → wordG K v ∈ M → wordG K v.reverse ∈ M :=
    fun v _ hv => by rw [← wordG_inv h2]; exact M.inv_mem hv
  have h0' := hmem [0, 4] rfl h0
  have h1' := hmem [1, 6] rfl h1
  have h3' := hmem [3, 10] rfl h3
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h0' h1' h3'
  have hprod : ∀ ws : List (List ℕ), (∀ v ∈ ws, wordG K v ∈ M) → wordG K ws.flatten ∈ M := by
    intro ws hws
    induction ws with
    | nil => exact M.one_mem
    | cons v ws ih =>
      rw [List.flatten_cons, wordG_append]
      exact M.mul_mem (hws v (by simp)) (ih fun u hu => hws u (List.mem_cons_of_mem _ hu))
  have hx0 : wordG K [0] ∈ M := by
    rw [← wordG_eq h2 (v := [[2], [8], [4, 0], [2], [0, 4], [8], [2]].flatten) rfl rfl
      (by decide +kernel)]
    exact hprod _ (by simp [hx, hy, h0, h0'])
  have hx1 : wordG K [1] ∈ M := by
    rw [← wordG_eq h2 (v := [[2], [8], [6, 1], [2], [1, 6], [8], [2]].flatten) rfl rfl
      (by decide +kernel)]
    exact hprod _ (by simp [hx, hy, h1, h1'])
  have hx3 : wordG K [3] ∈ M := by
    rw [← wordG_eq h2 (v := [[2], [8], [10, 3], [2], [3, 10], [8], [2]].flatten) rfl rfl
      (by decide +kernel)]
    exact hprod _ (by simp [hx, hy, h3, h3'])
  have hy0 : wordG K [4] ∈ M := by
    rw [← wordG_eq h2 (v := [[8], [2], [0, 4], [8], [4, 0], [2], [8]].flatten) rfl rfl
      (by decide +kernel)]
    exact hprod _ (by simp [hx, hy, h0, h0'])
  have hy1 : wordG K [6] ∈ M := by
    rw [← wordG_eq h2 (v := [[8], [2], [1, 6], [8], [6, 1], [2], [8]].flatten) rfl rfl
      (by decide +kernel)]
    exact hprod _ (by simp [hx, hy, h1, h1'])
  have hy3 : wordG K [10] ∈ M := by
    rw [← wordG_eq h2 (v := [[8], [2], [3, 10], [8], [10, 3], [2], [8]].flatten) rfl rfl
      (by decide +kernel)]
    exact hprod _ (by simp [hx, hy, h3, h3'])
  have hsingle : ∀ a, wordG K [a] = xPar (rootOperatorFamily Tag.D4) (rt a) (1 : K) := by
    intro a
    simp [wordG]
  obtain ⟨r0, r1, r2, r3, r4, r6, r8, r10⟩ := rt_single
  have hc : ∀ c : K, c = 0 ∨ c = 1 := fun c => by
    classical
    have : Fintype K := Fintype.ofFinite K
    by_contra hc
    push Not at hc
    have h3' : ({0, 1, c} : Finset K).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hc.1.symm]), Finset.card_pair hc.2.symm]
    have hle := Finset.card_le_univ ({0, 1, c} : Finset K)
    rw [h3', ← Nat.card_eq_fintype_card, hK] at hle
    omega
  refine eq_top_of_simple_mem fun i c => ?_
  rcases hc c with rfl | rfl
  · rw [xPar_zero, xPar_zero]
    exact ⟨M.one_mem, M.one_mem⟩
  · fin_cases i
    · refine ⟨?_, ?_⟩
      · have := hx0; rwa [hsingle, r0] at this
      · have := hy0; rwa [hsingle, r4] at this
    · refine ⟨?_, ?_⟩
      · have := hx1; rwa [hsingle, r1] at this
      · have := hy1; rwa [hsingle, r6] at this
    · refine ⟨?_, ?_⟩
      · have := hx; rwa [hsingle, r2] at this
      · have := hy; rwa [hsingle, r8] at this
    · refine ⟨?_, ?_⟩
      · have := hx3; rwa [hsingle, r3] at this
      · have := hy3; rwa [hsingle, r10] at this

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
