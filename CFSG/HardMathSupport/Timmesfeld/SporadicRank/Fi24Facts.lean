module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbSound

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding.R3 Finset

abbrev MatN (n : ℕ) : Type := Matrix (Fin n) (Fin n) (ZMod 3)

abbrev VecN (n : ℕ) : Type := Fin n → ZMod 3

@[expose] def fixSetN (n : ℕ) (M : MatN n) : Finset (VecN n) :=
  Finset.univ.filter fun v => M.mulVec v = v

@[expose] def matSetN (n : ℕ) (Lm : List (List ℕ)) : Finset (MatN n) :=
  (Lm.map (toMatL 3 n)).toFinset

@[expose] def o3SetN (n : ℕ) (Lm : List (List ℕ)) : Finset (MatN n) :=
  (matSetN n Lm).filter fun M => M ≠ 1 ∧ M ^ 3 = 1

@[expose] def FactsN (n : ℕ) (Lm : List (List ℕ)) : Prop :=
  (o3SetN n Lm).card < 6560 ∧ (∀ M ∈ o3SetN n Lm, (fixSetN n M).card ≤ 243) ∧
  (Finset.univ.filter fun v : VecN n =>
    2186 ≤ ((o3SetN n Lm).filter fun M => v ∈ fixSetN n M).card).card ≤ 26 ∧
  (Finset.univ.filter fun v : VecN n =>
    728 ≤ ((o3SetN n Lm).filter fun M => v ∈ fixSetN n M).card).card ≤ 80 ∧
  (Finset.univ.filter fun v : VecN n => 242 ≤
    (((o3SetN n Lm).filter fun M => 243 ≤ (fixSetN n M).card).filter
      fun M => v ∈ fixSetN n M).card).card ≤ 242

abbrev Fi24Facts (Lm : List (List ℕ)) : Prop := FactsN 7 Lm

theorem length_matVecL (p n : ℕ) (M c : List ℕ) : (matVecL p n M c).length = n := by
  simp [matVecL]

theorem lt_matVecL {p : ℕ} (hp : 0 < p) (n : ℕ) (M c : List ℕ) :
    ∀ x ∈ matVecL p n M c, x < p := by
  intro x hx
  simp only [matVecL, List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact Nat.mod_lt _ hp

theorem vecOf_inj {p n : ℕ} {l l' : List ℕ} (hl : l ∈ allVecs p n) (hl' : l' ∈ allVecs p n)
    (h : vecOf p n l = vecOf p n l') : l = l' := by
  rw [mem_allVecs] at hl hl'
  refine List.ext_getElem (hl.1.trans hl'.1.symm) fun k h1 h2 => ?_
  have hk : k < n := hl.1 ▸ h1
  have h3 := congrFun h ⟨k, hk⟩
  simp only [vecOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at h3
  have h4 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h3
  rwa [Nat.mod_eq_of_lt (hl.2 _ (List.getElem_mem h1)),
    Nat.mod_eq_of_lt (hl'.2 _ (List.getElem_mem h2))] at h4

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
