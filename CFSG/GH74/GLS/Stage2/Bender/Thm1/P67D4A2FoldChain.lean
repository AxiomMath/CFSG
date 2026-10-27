module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldDef
public import CFSG.GH74.BNPair.Eq305

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X]

theorem chain_intList_nodup (i j : ℤ) : (intList i j).Nodup :=
  List.Nodup.map (fun a b h => by simpa using h) List.nodup_range

theorem chain_mem_chainProd_iff (A : ℤ → Subgroup X) :
    ∀ l : List ℤ, l.Nodup → ∀ x : X,
      x ∈ chainProd A l ↔ ∃ f : ℤ → X, (∀ k ∈ l, f k ∈ A k) ∧ (l.map f).prod = x
  | [], _, x => by
    simp [chainProd, eq_comm]
  | k :: l, hnd, x => by
    rw [List.nodup_cons] at hnd
    rw [chainProd_cons]
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
      obtain ⟨f, hf, hfb⟩ := (chain_mem_chainProd_iff A l hnd.2 b).1 hb
      refine ⟨Function.update f k a, ?_, ?_⟩
      · intro k' hk'
        rcases List.mem_cons.1 hk' with rfl | h
        · simpa using ha
        · have : k' ≠ k := fun h' => hnd.1 (h' ▸ h)
          rw [Function.update_of_ne this]
          exact hf k' h
      · rw [List.map_cons, List.prod_cons, Function.update_self, ← hfb]
        congr 1
        congr 1
        apply List.map_congr_left
        intro k' hk'
        exact Function.update_of_ne (fun h : k' = k => hnd.1 (h ▸ hk')) _ _
    · rintro ⟨f, hf, rfl⟩
      rw [List.map_cons, List.prod_cons]
      exact Set.mul_mem_mul (hf k (by simp))
        ((chain_mem_chainProd_iff A l hnd.2 _).2 ⟨f, fun k' hk' => hf k' (by simp [hk']), rfl⟩)

theorem chain_chainProd_reverse (A : ℤ → Subgroup X) (l : List ℤ) :
    chainProd A l.reverse = (chainProd A l)⁻¹ := by
  induction l with
  | nil => simp [chainProd]
  | cons a l ih =>
    simp only [chainProd, List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
      List.map_nil] at ih ⊢
    rw [List.prod_append, List.prod_singleton, mul_inv_rev, ih, inv_coe_set]

theorem chain_prod_pad (f : ℤ → X) {a b c : ℤ} (ha : 1 ≤ a) (hab : a ≤ b + 1) (hb : b ≤ c) :
    ((intList 1 c).map (fun k => if a ≤ k ∧ k ≤ b then f k else 1)).prod =
      ((intList a b).map f).prod := by
  have h1 : intList 1 (a - 1) ++ intList a b = intList 1 b := by
    have := intList_append (a := 1) (b := a - 1) (c := b) (by omega) (by omega)
    rwa [Int.sub_add_cancel] at this
  have h2 : intList 1 b ++ intList (b + 1) c = intList 1 c := intList_append (by omega) hb
  rw [← h2, ← h1, List.append_assoc, List.map_append, List.prod_append, List.map_append,
    List.prod_append]
  have e1 : ((intList 1 (a - 1)).map (fun k => if a ≤ k ∧ k ≤ b then f k else 1)).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    have := mem_intList_iff.1 hk
    rw [ite_eq_right (by omega)]
  have e2 : ((intList a b).map (fun k => if a ≤ k ∧ k ≤ b then f k else 1)).prod =
      ((intList a b).map f).prod := by
    congr 1
    apply List.map_congr_left
    intro k hk
    have := mem_intList_iff.1 hk
    rw [ite_eq_left ⟨this.1, this.2⟩]
  have e3 : ((intList (b + 1) c).map (fun k => if a ≤ k ∧ k ≤ b then f k else 1)).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    have := mem_intList_iff.1 hk
    rw [ite_eq_right (by omega)]
  rw [e1, e2, e3, one_mul, mul_one]

theorem chain_reindex {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 3) (f g : ℤ → X)
    (he : ∀ k ∈ intList (foldLo i) (foldHi j), k % 2 = 0 → f k = 1)
    (hg : ∀ m ∈ intList i j, g m = f (2 * m - 1)) :
    ((intList (foldLo i) (foldHi j)).map f).prod = ((intList i j).map g).prod := by
  have hcases : (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 2) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 3) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show intList (foldLo 1) (foldHi 1) = [1, 2] by decide] at he ⊢
    rw [show intList 1 1 = [1] by decide] at hg ⊢
    simp at he hg
    simp [he, hg]
  · rw [show intList (foldLo 1) (foldHi 2) = [1, 2, 3, 4] by decide] at he ⊢
    rw [show intList 1 2 = [1, 2] by decide] at hg ⊢
    simp at he hg
    simp [he, hg]
  · rw [show intList (foldLo 1) (foldHi 3) = [1, 2, 3, 4, 5, 6] by decide] at he ⊢
    rw [show intList 1 3 = [1, 2, 3] by decide] at hg ⊢
    simp at he hg
    simp [he, hg]
  · rw [show intList (foldLo 2) (foldHi 2) = [2, 3, 4] by decide] at he ⊢
    rw [show intList 2 2 = [2] by decide] at hg ⊢
    simp at he hg
    simp [he, hg]
  · rw [show intList (foldLo 2) (foldHi 3) = [2, 3, 4, 5, 6] by decide] at he ⊢
    rw [show intList 2 3 = [2, 3] by decide] at hg ⊢
    simp at he hg
    simp [he, hg]
  · rw [show intList (foldLo 3) (foldHi 3) = [4, 5, 6] by decide] at he ⊢
    rw [show intList 3 3 = [3] by decide] at hg ⊢
    simp at he hg
    simp [he, hg]

theorem chain_lift_prod {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 3) (g : ℤ → X) :
    ((intList (foldLo i) (foldHi j)).map
      (fun k => if k % 2 = 1 then g ((k + 1) / 2) else 1)).prod = ((intList i j).map g).prod :=
  chain_reindex hi hij hj _ g (fun k _ hk => ite_eq_right (by omega)) (fun m _ => by
    show g m = if (2 * m - 1) % 2 = 1 then g ((2 * m - 1 + 1) / 2) else 1
    rw [ite_eq_left (by omega)]
    congr 1
    omega)

variable {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}

namespace FoldData

variable {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem chain_lift_mem {i j : ℤ} (g : ℤ → X) (hg : ∀ m ∈ intList i j, g m ∈ foldRoot φ root m) :
    ∀ k ∈ intList (foldLo i) (foldHi j),
      (if k % 2 = 1 then g ((k + 1) / 2) else 1) ∈ root k := by
  intro k hk
  have hk' := mem_intList_iff.1 hk
  by_cases hodd : k % 2 = 1
  · rw [ite_eq_left hodd]
    have hm : (k + 1) / 2 ∈ intList i j :=
      mem_intList_iff.2 ⟨by unfold foldLo at hk'; omega, by unfold foldHi at hk'; omega⟩
    have h1 := (hg _ hm).1
    have e : foldIdx ((k + 1) / 2) = k := by
      rw [foldIdx_of_pos (by unfold foldLo at hk'; omega)]
      omega
    rwa [e] at h1
  · rw [ite_eq_right hodd]
    exact (root k).one_mem

theorem chain_factors_fixed (hf : FoldData R φ) {F : ℤ → X}
    (hF : ∀ k ∈ intList 1 ((6 : ℕ) : ℤ), F k ∈ root k)
    (hfix : φ ((intList 1 ((6 : ℕ) : ℤ)).map F).prod = ((intList 1 ((6 : ℕ) : ℤ)).map F).prod) :
    ∀ k ∈ intList 1 ((6 : ℕ) : ℤ), φ (F k) = F k := by
  have hmem : ∀ k ∈ intList 1 ((6 : ℕ) : ℤ), φ (F k) ∈ root k := by
    intro k hk
    have := mem_intList_iff.1 hk
    exact hf.mem_root k (isRoot_of_pos_le this.1 this.2) _ (hF k hk)
  refine R.unique (fun k => φ (F k)) F hmem hF ?_
  rw [← hfix, map_list_prod, List.map_map]
  rfl

theorem mem_chainProd_foldRoot_iff (hf : FoldData R φ) {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ 3) (x : X) :
    x ∈ chainProd (foldRoot φ root) (intList i j) ↔
      x ∈ chainProd root (intList (foldLo i) (foldHi j)) ∧ φ x = x := by
  have hlo : 1 ≤ foldLo i := by unfold foldLo; omega
  have hhi : foldHi j ≤ 6 := by unfold foldHi; omega
  have hlh : foldLo i ≤ foldHi j + 1 := by unfold foldLo foldHi; omega
  rw [chain_mem_chainProd_iff _ _ (chain_intList_nodup i j),
    chain_mem_chainProd_iff _ _ (chain_intList_nodup _ _)]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hfix : φ ((intList i j).map g).prod = ((intList i j).map g).prod := by
      have : ((intList i j).map g).prod ∈ foldFix φ :=
        Subgroup.list_prod_mem _ (fun y hy => by
          obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
          exact (hg m hm).2)
      exact this
    exact ⟨⟨_, chain_lift_mem g hg, chain_lift_prod hi hij hj g⟩, hfix⟩
  · rintro ⟨⟨f, hfm, hfx⟩, hfix⟩
    have hFmem : ∀ k ∈ intList 1 ((6 : ℕ) : ℤ),
        (if foldLo i ≤ k ∧ k ≤ foldHi j then f k else 1) ∈ root k := by
      intro k hk
      by_cases h : foldLo i ≤ k ∧ k ≤ foldHi j
      · rw [ite_eq_left h]
        exact hfm k (mem_intList_iff.2 h)
      · rw [ite_eq_right h]
        exact (root k).one_mem
    have hprod : ((intList 1 ((6 : ℕ) : ℤ)).map
        (fun k => if foldLo i ≤ k ∧ k ≤ foldHi j then f k else 1)).prod = x := by
      rw [← hfx]
      exact chain_prod_pad f hlo hlh (by omega)
    have hfixed := hf.chain_factors_fixed hFmem (by rw [hprod]; exact hfix)
    have hfk : ∀ k ∈ intList (foldLo i) (foldHi j), φ (f k) = f k := by
      intro k hk
      have hk' := mem_intList_iff.1 hk
      have := hfixed k (mem_intList_iff.2 ⟨by omega, by omega⟩)
      rwa [ite_eq_left hk'] at this
    have hf_even : ∀ k ∈ intList (foldLo i) (foldHi j), k % 2 = 0 → f k = 1 := by
      intro k hk hk2
      have hk' := mem_intList_iff.1 hk
      exact hf.even_fix k (isRoot_of_pos_le (by omega) (by omega)) hk2 (f k) (hfm k hk) (hfk k hk)
    refine ⟨fun m => f (2 * m - 1), ?_, ?_⟩
    · intro m hm
      have hm' := mem_intList_iff.1 hm
      have hmem : 2 * m - 1 ∈ intList (foldLo i) (foldHi j) :=
        mem_intList_iff.2 ⟨by unfold foldLo; omega, by unfold foldHi; omega⟩
      refine ⟨?_, hfk _ hmem⟩
      rw [foldIdx_of_pos (by omega)]
      exact hfm _ hmem
    · rw [← hfx]
      exact (chain_reindex hi hij hj f _ hf_even (fun m hm => rfl)).symm

theorem mem_chainProd_foldRoot_rev_iff (hf : FoldData R φ) {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ 3) (x : X) :
    x ∈ chainProd (foldRoot φ root) (intList i j).reverse ↔
      x ∈ chainProd root (intList (foldLo i) (foldHi j)).reverse ∧ φ x = x := by
  rw [chain_chainProd_reverse, chain_chainProd_reverse, Set.mem_inv, Set.mem_inv,
    hf.mem_chainProd_foldRoot_iff hi hij hj x⁻¹, map_inv, inv_inj]

theorem carrier_eq_F (hf : FoldData R φ) :
    ((U ⊓ foldFix φ : Subgroup X) : Set X) =
      chainProd (foldRoot φ root) (intList 1 ((3 : ℕ) : ℤ)) := by
  ext x
  have h := hf.mem_chainProd_foldRoot_iff (i := 1) (j := 3) le_rfl (by norm_num) le_rfl x
  have e1 : foldLo 1 = 1 := by decide
  have e2 : foldHi 3 = ((6 : ℕ) : ℤ) := by decide
  rw [e1, e2] at h
  have hU : x ∈ U ↔ x ∈ chainProd root (intList 1 ((6 : ℕ) : ℤ)) := by
    rw [← SetLike.mem_coe, R.carrier_eq]
  rw [SetLike.mem_coe, Subgroup.mem_inf, hU, mem_foldFix]
  exact h.symm

theorem unique_F (hf : FoldData R φ) :
    ∀ f g : ℤ → X, (∀ k ∈ intList 1 ((3 : ℕ) : ℤ), f k ∈ foldRoot φ root k) →
      (∀ k ∈ intList 1 ((3 : ℕ) : ℤ), g k ∈ foldRoot φ root k) →
      ((intList 1 ((3 : ℕ) : ℤ)).map f).prod = ((intList 1 ((3 : ℕ) : ℤ)).map g).prod →
        ∀ k ∈ intList 1 ((3 : ℕ) : ℤ), f k = g k := by
  have _ := hf
  intro f g hf' hg' hprod k hk
  have e1 : foldLo 1 = 1 := by decide
  have e2 : foldHi 3 = ((6 : ℕ) : ℤ) := by decide
  have e3 : ((3 : ℕ) : ℤ) = 3 := by norm_num
  rw [e3] at hf' hg' hprod hk
  have hlf := chain_lift_prod (i := 1) (j := 3) le_rfl (by norm_num) le_rfl f
  have hlg := chain_lift_prod (i := 1) (j := 3) le_rfl (by norm_num) le_rfl g
  rw [e1, e2] at hlf hlg
  have hk' := mem_intList_iff.1 hk
  have := R.unique _ _ (chain_lift_mem f hf') (chain_lift_mem g hg')
    (by rw [hlf, hlg]; exact hprod) (2 * k - 1)
    (mem_intList_iff.2 ⟨by omega, by omega⟩)
  rw [ite_eq_left (by omega), ite_eq_left (by omega)] at this
  have e4 : (2 * k - 1 + 1) / 2 = k := by omega
  rwa [e4] at this

theorem reverse_eq_F (hf : FoldData R φ) :
    ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((3 : ℕ) : ℤ) →
      chainProd (foldRoot φ root) (intList i j) =
        chainProd (foldRoot φ root) (intList i j).reverse := by
  intro i j hi hij hj
  have hj' : j ≤ 3 := by omega
  have hlo : 1 ≤ foldLo i := by unfold foldLo; omega
  have hhi : foldHi j ≤ ((6 : ℕ) : ℤ) := by unfold foldHi; omega
  have hlh : foldLo i ≤ foldHi j := by unfold foldLo foldHi; omega
  ext x
  rw [hf.mem_chainProd_foldRoot_iff hi hij hj', hf.mem_chainProd_foldRoot_rev_iff hi hij hj',
    R.reverse_eq _ _ hlo hlh hhi]

theorem subgroup_F (hf : FoldData R φ) :
    ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((3 : ℕ) : ℤ) →
      ∃ V : Subgroup X, (V : Set X) = chainProd (foldRoot φ root) (intList i j) ∧
        V ≤ U ⊓ foldFix φ ∧
        (1 < i → ∀ x ∈ foldRoot φ root (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
        (j < ((3 : ℕ) : ℤ) → ∀ x ∈ foldRoot φ root (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) := by
  intro i j hi hij hj
  have hj' : j ≤ 3 := by omega
  have hlo : 1 ≤ foldLo i := by unfold foldLo; omega
  have hhi : foldHi j ≤ ((6 : ℕ) : ℤ) := by unfold foldHi; omega
  have hlh : foldLo i ≤ foldHi j := by unfold foldLo foldHi; omega
  obtain ⟨V, hV, hVU, hVl, hVh⟩ := R.subgroup (foldLo i) (foldHi j) hlo hlh hhi
  have hfix : ∀ x v : X, φ x = x → φ v = v → φ (x * v * x⁻¹) = x * v * x⁻¹ := by
    intro x v hx hv
    rw [map_mul, map_mul, map_inv, hx, hv]
  refine ⟨V ⊓ foldFix φ, ?_, inf_le_inf_right _ hVU, ?_, ?_⟩
  · ext x
    rw [SetLike.mem_coe, Subgroup.mem_inf, mem_foldFix, hf.mem_chainProd_foldRoot_iff hi hij hj',
      ← hV]
    rfl
  · intro hi1 x hx v hv
    refine ⟨hVl (by unfold foldLo; omega) x ?_ v hv.1, hfix x v hx.2 hv.2⟩
    have := hx.1
    rwa [foldIdx_of_pos (by omega),
      show 2 * (i - 1) - 1 = foldLo i - 1 by unfold foldLo; omega] at this
  · intro hj1 x hx v hv
    refine ⟨hVh (by unfold foldHi; omega) x ?_ v hv.1, hfix x v hx.2 hv.2⟩
    have := hx.1
    rwa [foldIdx_of_pos (by omega),
      show 2 * (j + 1) - 1 = foldHi j + 1 by unfold foldHi; omega] at this

end FoldData

end CFSG.GH74.GLS.SP
