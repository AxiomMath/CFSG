module

public import CFSG.GH74.BNPair.RootCalc

public section

namespace CFSG.GH74.BNPair

theorem intList_nodup (i j : ℤ) : (intList i j).Nodup := by
  refine List.Nodup.map (fun a b h => ?_) List.nodup_range
  have : (a : ℤ) = b := by simpa using h
  exact_mod_cast this

theorem intList_prod_pad {X : Type*} [Group X] {l a b r : ℤ}
    (hl : l ≤ a) (ha : a ≤ b) (hb : b ≤ r) (f : ℤ → X) :
    ((intList l r).map (fun k => if a ≤ k ∧ k ≤ b then f k else 1)).prod =
      ((intList a b).map f).prod := by
  classical
  have happ : ∀ {x y z : ℤ}, x ≤ y + 1 → y ≤ z →
      intList x z = intList x y ++ intList (y + 1) z := by
    intro x y z h1 h2
    apply List.ext_getElem
    · simp only [intList, List.length_append, List.length_map, List.length_range]
      omega
    · intro t ht1 ht2
      simp only [intList, List.length_map, List.length_range] at ht1 ht2 ⊢
      by_cases ht : t < (y + 1 - x).toNat
      · rw [List.getElem_append_left (by simpa using ht)]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
        omega
  have e1 : intList l r = intList l (a - 1) ++ (intList a b ++ intList (b + 1) r) := by
    have h1 := happ (x := l) (y := a - 1) (z := r) (by omega) (by omega)
    have h2 := happ (x := a) (y := b) (z := r) (by omega) hb
    rw [show a - 1 + 1 = a by ring, h2] at h1
    exact h1
  rw [e1, List.map_append, List.map_append, List.prod_append, List.prod_append]
  have hA : ((intList l (a - 1)).map
      (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : X))).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := mem_intList_iff.1 hk
    have hk' : ¬(a ≤ k ∧ k ≤ b) := by omega
    simp [hk']
  have hC : ((intList (b + 1) r).map
      (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : X))).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := mem_intList_iff.1 hk
    have hk' : ¬(a ≤ k ∧ k ≤ b) := by omega
    simp [hk']
  have hB : (intList a b).map (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : X)) =
      (intList a b).map f := by
    apply List.map_congr_left
    intro k hk
    have := mem_intList_iff.1 hk
    simp [this]
  rw [hA, hC, hB, one_mul, mul_one]

theorem exists_fun_of_mem_chainProd {X : Type*} [Group X] (A : ℤ → Subgroup X) :
    ∀ (l : List ℤ), l.Nodup → ∀ x ∈ chainProd A l,
      ∃ f : ℤ → X, (∀ k ∈ l, f k ∈ A k) ∧ x = (l.map f).prod
  | [], _, x, hx => ⟨fun _ => 1, by simp, by simpa [chainProd] using hx⟩
  | k :: l, hnd, x, hx => by
    rw [chainProd_cons, Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hk : k ∉ l := (List.nodup_cons.1 hnd).1
    obtain ⟨f, hf, rfl⟩ := exists_fun_of_mem_chainProd A l (List.nodup_cons.1 hnd).2 b hb
    refine ⟨Function.update f k a, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj'
      · simpa using ha
      · have hjk : j ≠ k := fun h => hk (h ▸ hj')
        simpa [Function.update_of_ne hjk] using hf j hj'
    · simp only [List.map_cons, List.prod_cons, Function.update_self]
      congr 1
      congr 1
      apply List.map_congr_left
      intro j hj
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      simp [Function.update_of_ne hjk]

theorem prod_mem_chainProd {X : Type*} [Group X] (A : ℤ → Subgroup X) (f : ℤ → X) :
    ∀ l : List ℤ, (∀ k ∈ l, f k ∈ A k) → (l.map f).prod ∈ chainProd A l
  | [], _ => by simp [chainProd]
  | k :: l, h => by
    rw [chainProd_cons, List.map_cons, List.prod_cons]
    exact Set.mem_mul.2 ⟨f k, h k (by simp), (l.map f).prod,
      prod_mem_chainProd A f l (fun k' hk' => h k' (by simp [hk'])), rfl⟩


theorem list_prod_conj {G : Type*} [Group G] (g : G) (l : List G) :
    (l.map (fun x => g * x * g⁻¹)).prod = g * l.prod * g⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    group

theorem list_prod_conj_inv_reverse {α : Type*} {G : Type*} [Group G] (g : G) (l : List α)
    (h : α → G) :
    ((l.reverse.map (fun j => (g * h j * g⁻¹)⁻¹)).prod) = (g * (l.map h).prod * g⁻¹)⁻¹ := by
  rw [← list_prod_conj g (l.map h)]
  rw [List.prod_inv_reverse]
  simp only [List.map_reverse, List.map_map, Function.comp_def]

theorem intList_add (a b s : ℤ) :
    intList (a + s) (b + s) = (intList a b).map (fun k => k + s) := by
  apply List.ext_getElem
  · simp only [intList, List.length_map]
    rw [show b + s + 1 - (a + s) = b + 1 - a by ring]
  · intro t h1 h2
    simp only [intList, List.length_map, List.getElem_map, List.getElem_range]
    ring

theorem intList_map_sub (a b c : ℤ) :
    intList a b = ((intList (c - b) (c - a)).map (fun k => c - k)).reverse := by
  apply List.ext_getElem
  · simp only [intList, List.length_map, List.length_reverse]
    rw [show c - a + 1 - (c - b) = b + 1 - a by ring]
  · intro t h1 h2
    simp only [intList, List.length_map, List.length_range] at h1
    rw [List.getElem_reverse]
    · simp only [intList, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
      have hlen : (c - a + 1 - (c - b)).toNat = (b + 1 - a).toNat := by
        rw [show c - a + 1 - (c - b) = b + 1 - a by ring]
      rw [hlen]
      have hsub : ((b + 1 - a).toNat - 1 - t : ℕ) = (b - a - t).toNat := by omega
      rw [hsub]
      have hnonneg : 0 ≤ b - a - t := by omega
      rw [Int.toNat_of_nonneg hnonneg]
      ring

end CFSG.GH74.BNPair

end
