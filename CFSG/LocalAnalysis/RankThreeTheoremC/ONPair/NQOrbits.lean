module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.NQOvergroups
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.NQFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.NQRelab
import Mathlib.Tactic.FinCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.HardMathSupport.Dickson.I271
  CFSG.RankThree.Native CFSG.Sporadic.ONOddCore CFSG.Sporadic.ON.Native
open CFSG.Sporadic.HNSchreier (gStrong gStrong_of_lt)

theorem mapsTo_of_mem_closure' {G α : Type*} [Group G] {ρ : G →* Equiv.Perm α} {s : Set G}
    {P : Set α} (hP : P.Finite) (hs : ∀ g ∈ s, Set.MapsTo (ρ g) P P) {g : G}
    (hg : g ∈ Subgroup.closure s) : Set.MapsTo (ρ g) P P := by
  have : Finite P := hP
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => intro x hx; simpa using hx
  | mul x y _ _ hx hy =>
    intro z hz
    rw [map_mul, Equiv.Perm.mul_apply]
    exact hx (hy hz)
  | inv x _ hx =>
    simpa using Equiv.Perm.perm_symm_mapsTo_of_mapsTo (ρ x) hx

section Elements


@[expose] noncomputable def nqG (g : ℕ → List ℤ) (a : ℕ) : Pv :=
  nqEv2 ⟨a0, a0_mem⟩ ⟨a1, a1_mem⟩ (g a)

@[expose] noncomputable def nqN (n : ℕ → List ℤ) (k : ℕ) : Pv := ⟨hval (n k), hval_mem _⟩

@[expose] noncomputable def nqM (m : ℕ → List ℤ) (i : ℕ) : Pv := ⟨hval (m i), hval_mem _⟩

@[expose] noncomputable def nqGamma (g m : ℕ → List ℤ) (a i : ℕ) : Pv := nqG g (a + 1) * nqM m i

@[expose] noncomputable def nqU (g n m : ℕ → List ℤ) (u : ℕ → ℕ → List (Fin 5 × Bool)) (a i : ℕ) :
    Pv :=
  Quiver.SchreierGraph.evalWord
    (fun h : Fin 5 => if (h : ℕ) < 4 then nqN n h else nqGamma g m a i) (u a i)

end Elements

section Lines


theorem lineAct_nqG (g : ℕ → List ℤ) (a : ℕ) : lineAct (nqG g a) = nqRho (g a) := by
  unfold nqG
  rw [map_nqEv2, lineAct_a0, lineAct_a1]
  rfl


theorem lineActA_nqG (g : ℕ → List ℤ) (a : ℕ) : lineActA (nqG g a) = nqRhoA (g a) := by
  unfold nqG
  rw [map_nqEv2, lineActA_a0, lineActA_a1, lineAct_alphaWordA]
  rfl

end Lines

section Facts

variable
  {g n m : ℕ → List ℤ} {u : ℕ → ℕ → List (Fin 5 × Bool)}

theorem nqN_mem_M1 (n : ℕ → List ℤ) (k : ℕ) : nqN n k ∈ M1 :=
  hP_mem_M1 _

theorem nqM_mem (m : ℕ → List ℤ) (i : ℕ) : nqM m i ∈ M1 :=
  hP_mem_M1 _

theorem nqG_zero_mem (hF : NQFactsAt g n m u) : nqG g 0 ∈ M1 := by
  rw [mem_M1, lineAct_nqG]
  exact hF.base

theorem Mflat_le_closure_qWords :
    Mflat ≤ Subgroup.closure {x | ∃ q ∈ [qWords[0]!, qWords[1]!, qWords[2]!, tWord],
      x = ⟨hval q, hval_mem q⟩} := by
  rw [Mflat, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact Subgroup.subset_closure ⟨qWords[0]!, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨qWords[1]!, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨qWords[2]!, by simp, rfl⟩
  · exact Subgroup.subset_closure ⟨tWord, by simp, rfl⟩


theorem nqN_mem_G2 (hF : NQFactsAt g n m u) {k : ℕ} (hk : k < 4) : nqN n k ∈ G2 := by
  rw [mem_G2]
  unfold nqN
  rw [lineActA_hval_nq, lineTwo_eq_nqL2]
  exact hF.stab k hk

theorem nq_orbit (hF : NQFactsAt g n m u) (y : Fin nL) :
    ∃ a < 36, ∃ c ∈ M1 ⊓ G2, lineAct c (lineAct (nqG g a) 0) = y := by
  obtain ⟨ks, hks, a, ha, hy⟩ := hF.forest y
  refine ⟨a, ha, (ks.map (nqN n)).prod, ?_, ?_⟩
  · refine (M1 ⊓ G2).list_prod_mem fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact ⟨nqN_mem_M1 n k, nqN_mem_G2 hF (hks k hk)⟩
  · have e : ks.map (lineAct ∘ nqN n) = ks.map fun k => nqSig (n k) :=
      List.map_congr_left fun k _ => lineAct_hval_nq (n k)
    rw [map_list_prod, List.map_map, e, lineAct_nqG]
    exact hy

theorem nq_orbit_two
    (hF : NQFactsAt g n m u) {x : Pv}
    (hx : x ∈ M1) : ∃ i < 456, lineActA x lineTwo = lineActA (nqM m i) lineTwo := by
  have hmaps : Set.MapsTo (lineActA x) {y | ∃ i < 456, y = lineActA (nqM m i) lineTwo}
      {y | ∃ i < 456, y = lineActA (nqM m i) lineTwo} := by
    refine mapsTo_of_mem_closure' (Set.toFinite _) ?_
      (Mflat_le_closure_qWords (by rw [Mflat_eq_M1]; exact hx))
    rintro _ ⟨q, hq, rfl⟩ y ⟨i, hi, rfl⟩
    obtain ⟨j, hj, e⟩ := hF.orbit i hi q hq
    refine ⟨j, hj, ?_⟩
    unfold nqM
    rw [lineActA_hval_nq, lineActA_hval_nq, lineActA_hval_nq, lineTwo_eq_nqL2]
    exact e
  have hmem : lineTwo ∈ {y | ∃ i < 456, y = lineActA (nqM m i) lineTwo} := by
    refine ⟨0, by norm_num, ?_⟩
    unfold nqM
    rw [lineActA_hval_nq, lineTwo_eq_nqL2]
    exact hF.orbit0.symm
  obtain ⟨i, hi, e⟩ := hmaps hmem
  exact ⟨i, hi, e⟩

theorem nqM_one_not_mem_G2 (hF : NQFactsAt g n m u) : nqM m 1 ∉ G2 := by
  rw [mem_G2]
  unfold nqM
  rw [lineActA_hval_nq, lineTwo_eq_nqL2]
  exact hF.orbit1

theorem nqU_mem (hF : NQFactsAt g n m u) {W : Subgroup Pv} (hN : M1 ⊓ G2 ≤ W) {a i : ℕ}
    (hγ : nqGamma g m a i ∈ W) : nqU g n m u a i ∈ W := by
  refine evalWord_mem (K := W) (ι := fun h : Fin 5 =>
    if (h : ℕ) < 4 then nqN n h else nqGamma g m a i) (fun h => ?_) (u a i)
  by_cases h4 : (h : ℕ) < 4
  · rw [if_pos h4]
    exact hN ⟨nqN_mem_M1 n h, nqN_mem_G2 hF h4⟩
  · rw [if_neg h4]
    exact hγ

theorem nqU_wit (hF : NQFactsAt g n m u) {a i : ℕ} (ha : a < 35) (hi : i < 456) :
    (nqU g n m u a i ∈ M1 ∧ nqU g n m u a i ∉ G2) ∨
      (nqU g n m u a i ∈ G2 ∧ nqU g n m u a i ∉ M1) := by
  have h0 : lineAct (nqU g n m u a i) =
      Quiver.SchreierGraph.evalWord (nqWitL nqSig nqRho g n m a i) (u a i) := by
    unfold nqU
    rw [map_evalWord]
    congr 1
    funext h
    unfold nqWitL
    simp only [Function.comp_apply]
    split_ifs
    · exact lineAct_hval_nq _
    · unfold nqGamma nqM
      rw [map_mul, lineAct_nqG, lineAct_hval_nq]
  have h1 : lineActA (nqU g n m u a i) =
      Quiver.SchreierGraph.evalWord (nqWitL nqSigA nqRhoA g n m a i) (u a i) := by
    unfold nqU
    rw [map_evalWord]
    congr 1
    funext h
    unfold nqWitL
    simp only [Function.comp_apply]
    split_ifs
    · exact lineActA_hval_nq _
    · unfold nqGamma nqM
      rw [map_mul, lineActA_nqG, lineActA_hval_nq]
  rcases hF.wit a ha i hi with ⟨e0, e1⟩ | ⟨e1, e0⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [mem_M1, h0]
      exact e0
    · rw [mem_G2, h1, lineTwo_eq_nqL2]
      exact e1
  · refine Or.inr ⟨?_, ?_⟩
    · rw [mem_G2, h1, lineTwo_eq_nqL2]
      exact e1
    · rw [mem_M1, h0]
      exact e0

end Facts

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
