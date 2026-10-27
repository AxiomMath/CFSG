module

public import CFSG.GH74.BNPair.Lemma305
public import CFSG.GH74.GLS.Stage4.Statements

public noncomputable section

universe u

open CFSG.GH74.BNPair

namespace CFSG.GH74.GLS.Stage4.Hex

@[expose] def revIdx (n : ℕ) (i : ℤ) : ℤ := if 0 < i then (n : ℤ) + 1 - i else -((n : ℤ) + 1 + i)

theorem revIdx_pos {n : ℕ} {i : ℤ} (h : 0 < i) : revIdx n i = (n : ℤ) + 1 - i := by
  simp [revIdx, h]

theorem revIdx_neg {n : ℕ} {i : ℤ} (h : i < 0) : revIdx n i = -((n : ℤ) + 1 + i) := by
  simp [revIdx, not_lt.2 h.le]

theorem revIdx_isRoot {n : ℕ} {i : ℤ} (h : IsRoot n i) : IsRoot n (revIdx n i) := by
  obtain ⟨h0, h1⟩ := h
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · rw [revIdx_neg hneg]
    exact ⟨by omega, by omega⟩
  · rw [revIdx_pos hpos]
    exact ⟨by omega, by omega⟩

theorem intList_map_sub (i j c : ℤ) :
    (intList i j).map (fun k => c - k) = (intList (c - j) (c - i)).reverse := by
  apply List.ext_getElem
  · simp [intList]
    omega
  · intro k h1 h2
    have hk : k < (j + 1 - i).toNat := by simpa [intList] using h1
    simp [intList, List.getElem_reverse]
    omega

theorem intList_map_revIdx {n : ℕ} {i j : ℤ} (hi : 1 ≤ i) :
    (intList i j).map (revIdx n) = (intList ((n : ℤ) + 1 - j) ((n : ℤ) + 1 - i)).reverse := by
  rw [← intList_map_sub]
  refine List.map_congr_left fun k hk => ?_
  obtain ⟨h1, h2⟩ := mem_intList_iff.1 hk
  exact revIdx_pos (by omega)

theorem intList_neg_map_revIdx {n : ℕ} :
    ((intList 1 n).map Neg.neg).map (revIdx n) = ((intList 1 n).map Neg.neg).reverse := by
  rw [List.map_map, ← List.map_reverse]
  have h1 : (intList 1 n).reverse = (intList 1 n).map (fun k => (n : ℤ) + 1 - k) := by
    rw [intList_map_sub]
    simp [show (n : ℤ) + 1 - n = 1 by ring, show (n : ℤ) + 1 - 1 = n by ring]
  rw [h1, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  obtain ⟨h1, h2⟩ := mem_intList_iff.1 hk
  simp only [Function.comp]
  rw [revIdx_neg (by omega)]
  ring

theorem chainProd_neg_reverse {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n) :
    chainProd D.root ((intList 1 n).map Neg.neg) =
      chainProd D.root ((intList 1 n).map Neg.neg).reverse := by
  have hn := D.three_le
  have h := (D.chainProd_good_plist (k := n - 1) (by omega) n).2
  have e : (plist (n : ℤ) (n - 1)).map (Rt n) = (intList 1 n).map Neg.neg := by
    apply List.ext_getElem
    · simp [plist, intList]
      omega
    · intro k h1 h2
      have hk : k < n := by
        simp only [plist, List.length_map, List.length_range] at h1
        omega
      simp only [plist, intList, List.getElem_map, List.getElem_range]
      rw [Rt_of_ge (by omega) (by omega)]
      ring
  rw [e] at h
  exact h

section Rev

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

@[expose] def revRoot (i : ℤ) : Subgroup X := D.root (revIdx n i)

theorem chainProd_revRoot (l : List ℤ) :
    chainProd (revRoot D) l = chainProd D.root (l.map (revIdx n)) := by
  simp [chainProd, revRoot, List.map_map, Function.comp_def]

theorem revRoot_carrier : (D.U : Set X) = chainProd (revRoot D) (intList 1 n) := by
  have hn := D.three_le
  rw [chainProd_revRoot, intList_map_revIdx (le_refl 1), show (n : ℤ) + 1 - n = 1 by ring,
    show (n : ℤ) + 1 - 1 = n by ring, ← D.roots.reverse_eq 1 n le_rfl (by omega) le_rfl]
  exact D.roots.carrier_eq

theorem revRoot_unique : ∀ f g : ℤ → X, (∀ k ∈ intList 1 ((n : ℕ) : ℤ), f k ∈ revRoot D k) →
    (∀ k ∈ intList 1 ((n : ℕ) : ℤ), g k ∈ revRoot D k) →
    ((intList 1 ((n : ℕ) : ℤ)).map f).prod = ((intList 1 ((n : ℕ) : ℤ)).map g).prod →
      ∀ k ∈ intList 1 ((n : ℕ) : ℤ), f k = g k := by
  have hn := D.three_le
  intro f g hf hg hfg k hk
  have hmemrev : ∀ j ∈ intList 1 (n : ℤ), (n : ℤ) + 1 - j ∈ intList 1 (n : ℤ) := fun j hj => by
    obtain ⟨h1, h2⟩ := mem_intList_iff.1 hj
    exact mem_intList_iff.2 ⟨by omega, by omega⟩
  have hprod : ∀ f : ℤ → X, ((intList 1 (n : ℤ)).map fun j => (f ((n : ℤ) + 1 - j))⁻¹).prod =
      (((intList 1 (n : ℤ)).map f).prod)⁻¹ := by
    intro f
    have h1 : (intList 1 (n : ℤ)).map (fun k => (n : ℤ) + 1 - k) = (intList 1 (n : ℤ)).reverse := by
      rw [intList_map_sub]
      simp [show (n : ℤ) + 1 - n = 1 by ring, show (n : ℤ) + 1 - 1 = n by ring]
    calc ((intList 1 (n : ℤ)).map fun j => (f ((n : ℤ) + 1 - j))⁻¹).prod
        = (((intList 1 (n : ℤ)).map (fun k => (n : ℤ) + 1 - k)).map (fun k => (f k)⁻¹)).prod := by
          rw [List.map_map]; rfl
      _ = (((intList 1 (n : ℤ)).reverse).map (fun k => (f k)⁻¹)).prod := by rw [h1]
      _ = (((intList 1 (n : ℤ)).map (fun k => (f k)⁻¹)).reverse).prod := by rw [List.map_reverse]
      _ = ((((intList 1 (n : ℤ)).map f).map (fun x => x⁻¹)).reverse).prod := by
          rw [List.map_map]; rfl
      _ = (((intList 1 (n : ℤ)).map f).prod)⁻¹ := (List.prod_inv_reverse _).symm
  have hF : ∀ (f : ℤ → X), (∀ k ∈ intList 1 (n : ℤ), f k ∈ revRoot D k) →
      ∀ j ∈ intList 1 (n : ℤ), (fun j => (f ((n : ℤ) + 1 - j))⁻¹) j ∈ D.root j := by
    intro f hf j hj
    have h := hf _ (hmemrev j hj)
    obtain ⟨h1, h2⟩ := mem_intList_iff.1 hj
    have e : revIdx n ((n : ℤ) + 1 - j) = j := by
      rw [revIdx_pos (by omega)]
      ring
    rw [revRoot, e] at h
    exact (D.root j).inv_mem h
  have key := D.roots.unique (fun j => (f ((n : ℤ) + 1 - j))⁻¹) (fun j => (g ((n : ℤ) + 1 - j))⁻¹)
    (hF f hf) (hF g hg) (by rw [hprod f, hprod g, hfg]) ((n : ℤ) + 1 - k) (hmemrev k hk)
  simp only [sub_sub_cancel, inv_inj] at key
  exact key

end Rev

section Rev2

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem revRoot_reverse_eq (i j : ℤ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ (n : ℤ)) :
    chainProd (revRoot D) (intList i j) = chainProd (revRoot D) (intList i j).reverse := by
  rw [chainProd_revRoot, chainProd_revRoot, List.map_reverse, intList_map_revIdx hi,
    List.reverse_reverse]
  exact (D.roots.reverse_eq _ _ (by omega) (by omega) (by omega)).symm

theorem revRoot_subgroup (i j : ℤ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ (n : ℤ)) :
    ∃ V : Subgroup X, (V : Set X) = chainProd (revRoot D) (intList i j) ∧ V ≤ D.U ∧
      (1 < i → ∀ x ∈ revRoot D (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < (n : ℤ) → ∀ x ∈ revRoot D (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) := by
  obtain ⟨V, hV, hVU, hl, hr⟩ := D.roots.subgroup ((n : ℤ) + 1 - j) ((n : ℤ) + 1 - i) (by omega)
    (by omega) (by omega)
  refine ⟨V, ?_, hVU, fun h1 x hx v hv => ?_, fun h1 x hx v hv => ?_⟩
  · rw [chainProd_revRoot, intList_map_revIdx hi, ← D.roots.reverse_eq _ _ (by omega) (by omega)
      (by omega)]
    exact hV
  · refine hr (by omega) x ?_ v hv
    have : revIdx n (i - 1) = (n : ℤ) + 1 - i + 1 := by
      rw [revIdx_pos (by omega)]
      ring
    rwa [revRoot, this] at hx
  · refine hl (by omega) x ?_ v hv
    have : revIdx n (j + 1) = (n : ℤ) + 1 - j - 1 := by
      rw [revIdx_pos (by omega)]
      ring
    rwa [revRoot, this] at hx

end Rev2

section Rev3

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem revRoot_one : revRoot D 1 = D.root n := by
  rw [revRoot, revIdx_pos one_pos]
  congr 1
  ring

theorem revRoot_neg_one : revRoot D (-1) = D.root (-n) := by
  rw [revRoot, revIdx_neg (by norm_num)]
  congr 1
  ring

theorem revRoot_n : revRoot D n = D.root 1 := by
  have hn := D.three_le
  rw [revRoot, revIdx_pos (by omega)]
  congr 1
  ring

theorem revRoot_neg_n : revRoot D (-n) = D.root (-1) := by
  have hn := D.three_le
  rw [revRoot, revIdx_neg (by omega)]
  congr 1
  ring

theorem revRoot_of_pos {i : ℤ} (hi : 0 < i) : revRoot D i = D.root ((n : ℤ) + 1 - i) := by
  rw [revRoot, revIdx_pos hi]

theorem revRoot_of_neg {i : ℤ} (hi : 0 < i) : revRoot D (-i) = D.root (-((n : ℤ) + 1 - i)) := by
  rw [revRoot, revIdx_neg (by omega)]
  congr 1

theorem revRoot_action₁ (m : D.N) (hm : (m : D.Weyl) = D.w₂) :
    conjBy (m : X) (revRoot D 1) = revRoot D (-1) ∧ conjBy (m : X) (revRoot D (-1)) = revRoot D 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ (n : ℤ) →
        conjBy (m : X) (revRoot D i) = revRoot D ((n : ℤ) + 2 - i) ∧
          conjBy (m : X) (revRoot D (-i)) = revRoot D (-((n : ℤ) + 2 - i)) := by
  obtain ⟨a1, a2, a3⟩ := D.roots.action₂ m hm
  refine ⟨by rw [revRoot_one, revRoot_neg_one]; exact a1, by rw [revRoot_one, revRoot_neg_one]; exact a2,
    fun i h2 hn => ?_⟩
  obtain ⟨b1, b2⟩ := a3 ((n : ℤ) + 1 - i) (by omega) (by omega)
  have e : (n : ℤ) - ((n : ℤ) + 1 - i) = i - 1 := by ring
  rw [e] at b1 b2
  refine ⟨?_, ?_⟩
  · rw [revRoot_of_pos D (by omega), revRoot_of_pos D (by omega)]
    rw [show (n : ℤ) + 1 - ((n : ℤ) + 2 - i) = i - 1 by ring]
    exact b1
  · rw [revRoot_of_neg D (by omega), revRoot_of_neg D (by omega)]
    rw [show (n : ℤ) + 1 - ((n : ℤ) + 2 - i) = i - 1 by ring]
    exact b2

theorem revRoot_action₂ (m : D.N) (hm : (m : D.Weyl) = D.w₁) :
    conjBy (m : X) (revRoot D n) = revRoot D (-(n : ℤ)) ∧
      conjBy (m : X) (revRoot D (-(n : ℤ))) = revRoot D n ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ (n : ℤ) - 1 →
        conjBy (m : X) (revRoot D i) = revRoot D ((n : ℤ) - i) ∧
          conjBy (m : X) (revRoot D (-i)) = revRoot D (-((n : ℤ) - i)) := by
  have hn := D.three_le
  obtain ⟨a1, a2, a3⟩ := D.roots.action₁ m hm
  refine ⟨by rw [revRoot_n, revRoot_neg_n]; exact a1, by rw [revRoot_n, revRoot_neg_n]; exact a2,
    fun i h1 hn' => ?_⟩
  obtain ⟨b1, b2⟩ := a3 ((n : ℤ) + 1 - i) (by omega) (by omega)
  have e : (n : ℤ) + 2 - ((n : ℤ) + 1 - i) = i + 1 := by ring
  rw [e] at b1 b2
  refine ⟨?_, ?_⟩
  · rw [revRoot_of_pos D (by omega), revRoot_of_pos D (by omega)]
    rw [show (n : ℤ) + 1 - ((n : ℤ) - i) = i + 1 by ring]
    exact b1
  · rw [revRoot_of_neg D (by omega), revRoot_of_neg D (by omega)]
    rw [show (n : ℤ) + 1 - ((n : ℤ) - i) = i + 1 by ring]
    exact b2

theorem revRoot_meet_one : ∀ x ∈ D.B, x ∈ chainProd (revRoot D) ((intList 1 (n : ℤ)).map Neg.neg) →
    x = 1 := by
  intro x hxB hx
  rw [chainProd_revRoot, intList_neg_map_revIdx, ← chainProd_neg_reverse D] at hx
  exact D.roots.meet_one x hxB hx

end Rev3

section Rev4

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

open Classical in
@[expose] def _root_.CFSG.GH74.BNPair.RankTwoSystem.rev : RankTwoSystem X n where
  B := D.B
  N := D.N
  normal := D.normal
  w₁ := D.w₂
  w₂ := D.w₁
  U := D.U
  root := revRoot D
  isTits := by
    have h := D.isTits
    rwa [Finset.pair_comm] at h
  w₁_ne_w₂ := D.w₁_ne_w₂.symm
  isSplit := D.isSplit
  isSaturated := D.isSaturated
  faithful := by
    intro g hg
    refine D.faithful g (fun v hv => hg v ?_)
    rcases hv with h | h
    · exact Or.inr h
    · exact Or.inl h
  card_weyl := D.card_weyl
  three_le := D.three_le
  roots :=
    { ne_bot := fun i hi => D.roots.ne_bot _ (revIdx_isRoot hi)
      invariant := fun i hi h hh x hx => D.roots.invariant _ (revIdx_isRoot hi) h hh x hx
      carrier_eq := revRoot_carrier D
      unique := revRoot_unique D
      reverse_eq := revRoot_reverse_eq D
      subgroup := revRoot_subgroup D
      action₁ := revRoot_action₁ D
      action₂ := revRoot_action₂ D
      meet_one := revRoot_meet_one D }

@[simp] theorem rev_U : D.rev.U = D.U := rfl

@[simp] theorem rev_root (i : ℤ) : D.rev.root i = D.root (revIdx n i) := rfl

end Rev4

section Orders

open CFSG.GH74.GLS.Stage4

theorem exists_system_firstOrders {G : Type} [Group G] (D : RankTwoSystem G 6) {q : ℕ}
    (h : RootOrdersD4 D.root q) :
    ∃ D' : RankTwoSystem G 6, (D' = D ∨ D' = D.rev) ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card (D'.root i) = if i % 2 = 1 then q ^ 3 else q := by
  rcases h with h | h
  · exact ⟨D, Or.inl rfl, h⟩
  · refine ⟨D.rev, Or.inr rfl, fun i h1 h6 => ?_⟩
    rw [rev_root, revIdx_pos (by omega)]
    have := h ((6 : ℤ) + 1 - i) (by omega) (by omega)
    rw [show ((6 : ℕ) : ℤ) + 1 - i = (6 : ℤ) + 1 - i by norm_num] 
    rw [this]
    by_cases hi : i % 2 = 1
    · rw [ite_eq_left hi]
      have : ¬ ((6 : ℤ) + 1 - i) % 2 = 1 := by omega
      rw [ite_eq_right this]
    · rw [ite_eq_right hi]
      have : ((6 : ℤ) + 1 - i) % 2 = 1 := by omega
      rw [ite_eq_left this]

end Orders

end CFSG.GH74.GLS.Stage4.Hex
