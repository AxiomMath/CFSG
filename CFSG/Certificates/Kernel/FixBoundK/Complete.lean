module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.KC.FixBoundK

open Subgroup

variable {G : Type*} [Group G]

theorem eq_of_agree {α : Type*} (E : Subgroup (Equiv.Perm α)) (B : Set α)
    (hB : ∀ g ∈ E, (∀ b ∈ B, g b = b) → g = 1) {g h : Equiv.Perm α} (hg : g ∈ E) (hh : h ∈ E)
    (hgh : ∀ b ∈ B, g b = h b) : g = h := by
  have h1 : g⁻¹ * h = 1 := hB _ (E.mul_mem (E.inv_mem hg) hh) fun b hb => by
    rw [Equiv.Perm.mul_apply, ← hgh b hb]
    exact g.symm_apply_apply b
  rw [← mul_inv_cancel_left g h, h1, mul_one]

@[expose] def prodL (h : ℕ → G) (L : List ℕ) (μ : ℕ) : G :=
  (L.map fun j => if μ.testBit j then h j else 1).prod

@[expose] def prodM (h : ℕ → G) (μ : ℕ) : G := prodL h (List.range 6) μ

theorem prodL_commute {h : ℕ → G} {a : G} (ha : ∀ j, Commute a (h j)) (L : List ℕ) (μ : ℕ) :
    Commute a (prodL h L μ) := by
  refine Commute.list_prod_right _ _ fun b hb => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hb
  split_ifs
  · exact ha j
  · exact Commute.one_right a

theorem prodL_xor {h : ℕ → G} (hc : ∀ i j, Commute (h i) (h j)) (hsq : ∀ i, h i * h i = 1)
    (L : List ℕ) (μ ν : ℕ) : prodL h L (μ ^^^ ν) = prodL h L μ * prodL h L ν := by
  induction L with
  | nil => simp [prodL]
  | cons a L ih =>
    have e : ∀ κ, prodL h (a :: L) κ = (if κ.testBit a then h a else 1) * prodL h L κ := by
      intro κ
      simp [prodL]
    have hcm : Commute (if ν.testBit a then h a else 1) (prodL h L μ) := by
      split_ifs
      · exact prodL_commute (hc a) L μ
      · exact Commute.one_left _
    rw [e, e, e, ih, Nat.testBit_xor]
    calc _ = (if μ.testBit a then h a else 1) * (if ν.testBit a then h a else 1) *
          (prodL h L μ * prodL h L ν) := by
          congr 1
          cases μ.testBit a <;> cases ν.testBit a <;> simp [hsq]
      _ = _ := by
          rw [mul_assoc, ← mul_assoc _ (prodL h L μ), hcm.eq]
          simp only [mul_assoc]

theorem prodM_xor {h : ℕ → G} (hc : ∀ i j, Commute (h i) (h j)) (hsq : ∀ i, h i * h i = 1)
    (μ ν : ℕ) : prodM h (μ ^^^ ν) = prodM h μ * prodM h ν :=
  prodL_xor hc hsq _ μ ν

theorem prodL_two_pow (h : ℕ → G) {L : List ℕ} (hL : L.Nodup) {i : ℕ} (hi : i ∈ L) :
    prodL h L (2 ^ i) = h i := by
  induction L with
  | nil => exact absurd hi List.not_mem_nil
  | cons a L ih =>
    obtain ⟨haL, hnd⟩ := List.nodup_cons.1 hL
    have e : prodL h (a :: L) (2 ^ i) =
        (if (2 ^ i).testBit a then h a else 1) * prodL h L (2 ^ i) := by
      simp [prodL]
    rw [e, Nat.testBit_two_pow]
    rcases List.mem_cons.1 hi with rfl | hi'
    · have h1 : prodL h L (2 ^ i) = 1 := by
        refine List.prod_eq_one fun b hb => ?_
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
        have hji : ¬ i = j := fun e => haL (e ▸ hj)
        simp [Nat.testBit_two_pow, hji]
      simp [h1]
    · have hia : ¬ i = a := fun e => haL (e ▸ hi')
      simp [hia, ih hnd hi']

theorem prodM_two_pow (h : ℕ → G) {i : ℕ} (hi : i < 6) : prodM h (2 ^ i) = h i :=
  prodL_two_pow h List.nodup_range (List.mem_range.2 hi)

theorem prodM_zero (h : ℕ → G) : prodM h 0 = 1 :=
  List.prod_eq_one fun b hb => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hb
    simp

theorem prodL_congr {h h' : ℕ → G} (L : List ℕ) {μ : ℕ} (e : ∀ j, μ.testBit j = true → h j = h' j) :
    prodL h L μ = prodL h' L μ := by
  unfold prodL
  congr 1
  refine List.map_congr_left fun j _ => ?_
  by_cases hb : μ.testBit j = true
  · rw [if_pos hb, if_pos hb, e j hb]
  · rw [if_neg hb, if_neg hb]

theorem prodL_mem {h : ℕ → G} {K : Subgroup G} (L : List ℕ) (μ : ℕ)
    (hK : ∀ j ∈ L, μ.testBit j = true → h j ∈ K) : prodL h L μ ∈ K := by
  refine K.list_prod_mem fun b hb => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  split_ifs with hb'
  · exact hK j hj hb'
  · exact K.one_mem

@[expose] def xorL (f : ℕ → ℕ) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (if s.testBit m then f m else 0) ^^^ xorL f s m

theorem closure_eq_of_span {h y : ℕ → G} {mp : ℕ → ℕ} {m : ℕ} (hm : m ≤ 6)
    (hc : ∀ i < m, ∀ j < m, Commute (h i) (h j)) (hsq : ∀ i < m, h i * h i = 1)
    (hmp : ∀ i < m, mp i < 2 ^ m) (hy : ∀ i < m, y i = prodM h (mp i))
    (hsp : ∀ i < m, ∃ s, xorL mp s m = 2 ^ i) :
    closure (y '' {i | i < m}) = closure (h '' {i | i < m}) := by
  classical
  set h' : ℕ → G := fun j => if j < m then h j else 1 with hh'
  have hc' : ∀ i j, Commute (h' i) (h' j) := by
    intro i j
    simp only [hh']
    split_ifs with hi hj hj
    · exact hc i hi j hj
    · exact Commute.one_right _
    · exact Commute.one_left _
    · exact Commute.one_left _
  have hsq' : ∀ i, h' i * h' i = 1 := by
    intro i
    simp only [hh']
    split_ifs with hi
    · exact hsq i hi
    · exact one_mul 1
  have hlt : ∀ μ, μ < 2 ^ m → prodM h μ = prodM h' μ := fun μ hμ =>
    prodL_congr _ fun j hj => by
      have hjm : j < m := by
        by_contra hjm
        have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hμ
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hjm)))
        rw [this] at hj
        exact absurd hj (by simp)
      simp [hh', hjm]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [hy i hi]
    refine prodL_mem _ _ fun j _ hj => ?_
    have hjm : j < m := by
      by_contra hjm
      have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hmp i hi)
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hjm)))
      rw [this] at hj
      exact absurd hj (by simp)
    exact Subgroup.subset_closure ⟨j, hjm, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨s, hs⟩ := hsp i hi
    have hmem : ∀ k ≤ m, prodM h' (xorL mp s k) ∈ closure (y '' {i | i < m}) := by
      intro k
      induction k with
      | zero => intro _; rw [xorL, prodM_zero]; exact one_mem _
      | succ k ih =>
        intro hk
        rw [xorL, prodM_xor hc' hsq']
        refine mul_mem ?_ (ih (Nat.le_of_succ_le hk))
        split_ifs
        · rw [← hlt _ (hmp k hk), ← hy k hk]
          exact Subgroup.subset_closure ⟨k, hk, rfl⟩
        · rw [prodM_zero]
          exact one_mem _
    have h2 := hmem m le_rfl
    have hi' : i < m := hi
    rw [hs, prodM_two_pow h' (Nat.lt_of_lt_of_le hi hm)] at h2
    simp only [hh', if_pos hi'] at h2
    exact h2

abbrev conjG (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem conjG_mul (g g' : G) (H : Subgroup G) : conjG g' (conjG g H) = conjG (g' * g) H := by
  rw [conjG, conjG, conjG, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem conjG_closure (g : G) (s : Set G) :
    conjG g (closure s) = closure ((fun x => g * x * g⁻¹) '' s) := by
  rw [conjG, MonoidHom.map_closure]
  rfl

theorem mem_conjG_iff {g x : G} {H : Subgroup G} : g * x * g⁻¹ ∈ conjG g H ↔ x ∈ H := by
  constructor
  · rintro ⟨y, hy, e⟩
    have e' : y = x := by
      simpa [MulAut.conj_apply] using e
    exact e' ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem conjG_eq_of_pair {hs ht : ℕ → G} {r : ℕ} {x g : G} {mp : ℕ → ℕ} (hr : r + 1 ≤ 6)
    (hc : ∀ i < r + 1, ∀ j < r + 1, Commute (ht i) (ht j)) (hsq : ∀ i < r + 1, ht i * ht i = 1)
    (hmp : ∀ i < r + 1, mp i < 2 ^ (r + 1))
    (hy : ∀ i < r, g * hs i * g⁻¹ = prodM ht (mp i)) (hx : g * x * g⁻¹ = prodM ht (mp r))
    (hsp : ∀ i < r + 1, ∃ s, xorL mp s (r + 1) = 2 ^ i) :
    conjG g (closure (insert x (hs '' {i | i < r}))) = closure (ht '' {i | i < r + 1}) := by
  set y : ℕ → G := fun i => if i < r then g * hs i * g⁻¹ else g * x * g⁻¹ with hy'
  have himg : (fun z => g * z * g⁻¹) '' insert x (hs '' {i | i < r}) = y '' {i | i < r + 1} := by
    ext z
    simp only [Set.image_insert_eq, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq, hy']
    constructor
    · rintro (rfl | ⟨_, ⟨i, hi, rfl⟩, rfl⟩)
      · exact ⟨r, by omega, by simp⟩
      · exact ⟨i, by omega, by simp [hi]⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases hir : i < r
      · exact Or.inr ⟨hs i, ⟨i, hir, rfl⟩, by simp [hir]⟩
      · exact Or.inl (by simp [hir])
  rw [conjG_closure, himg]
  refine closure_eq_of_span hr hc hsq hmp (fun i hi => ?_) hsp
  by_cases hir : i < r
  · simp [hy', hir, hy i hir]
  · have hir' : i = r := by omega
    subst hir'
    simp [hy', hx]

theorem closure_insert_closure (x : G) (s : Set G) :
    closure (insert x (closure s : Set G)) = closure (insert x s) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro z (rfl | hz)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact (Subgroup.closure_mono (Set.subset_insert x s)) hz
  · exact Subgroup.closure_mono (Set.insert_subset_insert Subgroup.subset_closure)

theorem exists_conj_eq_closure (E : Subgroup G) (S : Set ℕ) (src : ℕ → Set G) (h0 : 0 ∈ S)
    (hsrc0 : src 0 = ∅)
    (hstep : ∀ s ∈ S, ∀ x ∈ E, x * x = 1 → (∀ y ∈ src s, x * y = y * x) →
      x ∈ closure (src s) ∨
        ∃ t ∈ S, ∃ g ∈ E, conjG g (closure (insert x (src s))) = closure (src t))
    (P : Subgroup G) [Finite P] (hPE : P ≤ E) (hP : CFSG.Open.IsElemAbelian 2 P) :
    ∃ t ∈ S, ∃ g ∈ E, conjG g P = closure (src t) := by
  classical
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have := hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have key : ∀ T : Finset G, (T : Set G) ⊆ P →
      ∃ t ∈ S, ∃ g ∈ E, conjG g (closure (T : Set G)) = closure (src t) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨0, h0, 1, E.one_mem, ?_⟩
      rw [hsrc0, Finset.coe_empty, Subgroup.closure_empty, conjG, Subgroup.map_bot]
    | insert x T _ ih =>
      intro hT
      rw [Finset.coe_insert] at hT ⊢
      have hxP : x ∈ P := hT (Set.mem_insert _ _)
      obtain ⟨s, hs, g, hg, e⟩ := ih (fun z hz => hT (Set.mem_insert_of_mem _ hz))
      have hTP : closure (T : Set G) ≤ P :=
        (Subgroup.closure_le P).2 fun z hz => hT (Set.mem_insert_of_mem _ hz)
      by_cases hxT : x ∈ closure (T : Set G)
      · refine ⟨s, hs, g, hg, ?_⟩
        have hcl : closure (insert x (T : Set G)) = closure (T : Set G) := by
          apply le_antisymm
          · rw [Subgroup.closure_le]
            rintro z (rfl | hz)
            · exact hxT
            · exact Subgroup.subset_closure hz
          · exact Subgroup.closure_mono (Set.subset_insert _ _)
        rw [hcl, e]
      · set x' := g * x * g⁻¹ with hx'
        have hx'E : x' ∈ E := E.mul_mem (E.mul_mem hg (hPE hxP)) (E.inv_mem hg)
        have hx2 : x' * x' = 1 := by
          have hxx : x * x = 1 := by
            rw [← pow_two]
            exact hP.2 x hxP
          calc x' * x' = g * (x * x) * g⁻¹ := by rw [hx']; group
            _ = 1 := by rw [hxx, mul_one, mul_inv_cancel]
        have hxc : ∀ y ∈ src s, x' * y = y * x' := by
          intro y hy
          have hy' : y ∈ conjG g (closure (T : Set G)) := e ▸ Subgroup.subset_closure hy
          obtain ⟨z, hz, rfl⟩ := hy'
          have hzx := hcomm x hxP z (hTP hz)
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hx']
          calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
            _ = g * (z * x) * g⁻¹ := by rw [hzx]
            _ = g * z * g⁻¹ * (g * x * g⁻¹) := by group
        rcases hstep s hs x' hx'E hx2 hxc with hin | ⟨t, ht, g', hg', e'⟩
        · rw [← e] at hin
          exact absurd (mem_conjG_iff.1 hin) hxT
        · refine ⟨t, ht, g' * g, E.mul_mem hg' hg, ?_⟩
          have h1 : closure (insert x' (src s)) =
              closure (insert x' ((fun z => g * z * g⁻¹) '' (T : Set G))) := by
            rw [← closure_insert_closure, ← e, conjG_closure, closure_insert_closure]
          rw [← conjG_mul, ← e']
          congr 1
          rw [conjG_closure, Set.image_insert_eq]
          exact h1.symm
  have hfin : (P : Set G).Finite := Set.toFinite _
  obtain ⟨t, ht, g, hg, e⟩ := key hfin.toFinset (by simp)
  refine ⟨t, ht, g, hg, ?_⟩
  rw [← e, Set.Finite.coe_toFinset, Subgroup.closure_eq]

end CFSG.KC.FixBoundK
