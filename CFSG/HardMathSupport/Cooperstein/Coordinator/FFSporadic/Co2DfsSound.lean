module

public import Certificates.Data.CFSGNative.Co2Rank.Dfs
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5

open CFSG.Sporadic.Co2Rank

variable {G : Type*} [Group G]

structure Setting (n : ℕ) (v : ℕ → G) (adj : ℕ → ℕ → Bool) (pr : ℕ → ℕ → ℕ) : Prop where
  inj : ∀ i j, i < n → j < n → v i = v j → i = j
  sq : ∀ i, i < n → v i * v i = 1 ∧ v i ≠ 1
  adj_iff : ∀ i j, adj i j = true ↔
    (i < n ∧ j < n ∧ v i * v j = v j * v i ∧ ∃ k < n, v k = v i * v j)
  pr_spec : ∀ i j, adj i j = true → pr i j < n ∧ v (pr i j) = v i * v j

@[expose] def Sset (v : ℕ → G) (S : List ℕ) : Set G := {g | g = 1 ∨ ∃ i ∈ S, v i = g}

structure SInv (n : ℕ) (v : ℕ → G) (S : List ℕ) : Prop where
  nodup : S.Nodup
  lt : ∀ i ∈ S, i < n
  closed : ∀ x ∈ Sset v S, ∀ y ∈ Sset v S, x * y ∈ Sset v S ∧ x * y = y * x

structure GoodF (n : ℕ) (v : ℕ → G) (F : Finset G) : Prop where
  one : (1 : G) ∈ F
  mul : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F ∧ x * y = y * x
  sq : ∀ x ∈ F, x * x = 1
  mem : ∀ x ∈ F, x ≠ 1 → ∃ i < n, v i = x

section

variable {n : ℕ} {v : ℕ → G} {adj : ℕ → ℕ → Bool} {pr : ℕ → ℕ → ℕ}

theorem Setting.adj_symm (h : Setting n v adj pr) {i j : ℕ} (hij : adj i j = true) :
    adj j i = true := by
  rw [h.adj_iff] at hij ⊢
  obtain ⟨hi, hj, hc, k, hk, hkv⟩ := hij
  exact ⟨hj, hi, hc.symm, k, hk, by rw [hkv]; exact hc⟩

theorem mul_eq_one_imp {x y : G} (hy : y * y = 1) (h : x * y = 1) : x = y := by
  calc x = x * (y * y) := by rw [hy, mul_one]
    _ = (x * y) * y := by rw [mul_assoc]
    _ = y := by rw [h, one_mul]

theorem card_le_Sset (S : List ℕ) {F : Finset G} (h : ∀ x ∈ F, x ∈ Sset v S) :
    F.card ≤ S.length + 1 := by
  classical
  have hsub : F ⊆ insert 1 (S.toFinset.image v) := by
    intro x hx
    rcases h x hx with rfl | ⟨i, hi, rfl⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, List.mem_toFinset.2 hi, rfl⟩)
  calc F.card ≤ (insert 1 (S.toFinset.image v)).card := Finset.card_le_card hsub
    _ ≤ (S.toFinset.image v).card + 1 := Finset.card_insert_le _ _
    _ ≤ S.toFinset.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
    _ ≤ S.length + 1 := Nat.add_le_add_right (List.toFinset_card_le S) 1

theorem adj_of_mem (hs : Setting n v adj pr) {F : Finset G} (hF : GoodF n v F) {i j : ℕ}
    (hi : i < n) (hj : j < n) (hiF : v i ∈ F) (hjF : v j ∈ F) (hij : i ≠ j) : adj i j = true := by
  rw [hs.adj_iff]
  obtain ⟨hmem, hcomm⟩ := hF.mul _ hiF _ hjF
  refine ⟨hi, hj, hcomm, ?_⟩
  have hne : v i * v j ≠ 1 := fun h1 =>
    hij (hs.inj i j hi hj (mul_eq_one_imp (hs.sq j hj).1 h1))
  exact hF.mem _ hmem hne

theorem not_mem_Sset (hs : Setting n v adj pr) {S : List ℕ} (hS : SInv n v S) {m : ℕ} (hm : m < n)
    (hmS : m ∉ S) : v m ∉ Sset v S := by
  rintro (h | ⟨i, hi, hiv⟩)
  · exact (hs.sq m hm).2 h
  · exact hmS (hs.inj i m (hS.lt i hi) hm hiv ▸ hi)

theorem closed_ext {A : Set G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A ∧ x * y = y * x) {c : G}
    (hc : c * c = 1) (hcA : ∀ x ∈ A, c * x = x * c) :
    ∀ x ∈ A ∪ (fun y => c * y) '' A, ∀ y ∈ A ∪ (fun y => c * y) '' A,
      x * y ∈ A ∪ (fun y => c * y) '' A ∧ x * y = y * x := by
  rintro x (hx | ⟨x', hx', rfl⟩) y (hy | ⟨y', hy', rfl⟩)
  · obtain ⟨h1, h2⟩ := hA x hx y hy
    exact ⟨Or.inl h1, h2⟩
  · obtain ⟨h1, h2⟩ := hA x hx y' hy'
    have hxc : c * x = x * c := hcA x hx
    refine ⟨Or.inr ⟨x * y', h1, ?_⟩, ?_⟩
    · show c * (x * y') = x * (c * y')
      rw [← mul_assoc, hxc, mul_assoc]
    · show x * (c * y') = c * y' * x
      rw [← mul_assoc, ← hxc, mul_assoc, mul_assoc, h2]
  · obtain ⟨h1, h2⟩ := hA x' hx' y hy
    have hyc : c * y = y * c := hcA y hy
    refine ⟨Or.inr ⟨x' * y, h1, ?_⟩, ?_⟩
    · show c * (x' * y) = c * x' * y
      rw [mul_assoc]
    · show c * x' * y = y * (c * x')
      calc c * x' * y = c * (x' * y) := by rw [mul_assoc]
        _ = c * (y * x') := by rw [h2]
        _ = (c * y) * x' := by rw [mul_assoc]
        _ = (y * c) * x' := by rw [hyc]
        _ = y * (c * x') := by rw [mul_assoc]
  · obtain ⟨h1, h2⟩ := hA x' hx' y' hy'
    refine ⟨Or.inl ?_, ?_⟩
    · have : c * x' * (c * y') = x' * y' := by
        have hxc : c * x' = x' * c := hcA x' hx'
        calc c * x' * (c * y') = x' * c * (c * y') := by rw [hxc]
          _ = x' * (c * c) * y' := by group
          _ = x' * y' := by rw [hc, mul_one]
      show c * x' * (c * y') ∈ A
      rw [this]; exact h1
    · show c * x' * (c * y') = c * y' * (c * x')
      have hxc : c * x' = x' * c := hcA x' hx'
      have hyc : c * y' = y' * c := hcA y' hy'
      calc c * x' * (c * y') = x' * c * (c * y') := by rw [hxc]
        _ = x' * (c * c) * y' := by group
        _ = x' * y' := by rw [hc, mul_one]
        _ = y' * x' := h2
        _ = y' * (c * c) * x' := by rw [hc, mul_one]
        _ = y' * c * (c * x') := by group
        _ = c * y' * (c * x') := by rw [hyc]

theorem comm_of_adj (hs : Setting n v adj pr) {i j : ℕ} (h : adj i j = true) :
    v i * v j = v j * v i := ((hs.adj_iff i j).1 h).2.2.1

theorem Sset_child (hs : Setting n v adj pr) {S : List ℕ} {m : ℕ}
    (hadj : ∀ s ∈ S, adj m s = true) :
    Sset v (childS pr S m) = Sset v S ∪ (fun y => v m * y) '' Sset v S := by
  ext x
  simp only [Sset, childS, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, List.mem_cons,
    List.mem_append, List.mem_map]
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inl rfl)
    · rcases hi with rfl | hi | ⟨s, hs', rfl⟩
      · exact Or.inr ⟨1, Or.inl rfl, mul_one _⟩
      · exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
      · exact Or.inr ⟨v s, Or.inr ⟨s, hs', rfl⟩, ((hs.pr_spec m s (hadj s hs')).2).symm⟩
  · rintro ((rfl | ⟨i, hi, rfl⟩) | ⟨y, (rfl | ⟨s, hs', rfl⟩), rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨i, Or.inr (Or.inl hi), rfl⟩
    · exact Or.inr ⟨m, Or.inl rfl, by simp⟩
    · exact Or.inr ⟨pr m s, Or.inr (Or.inr ⟨s, hs', rfl⟩), (hs.pr_spec m s (hadj s hs')).2⟩

theorem pr_not_mem (hs : Setting n v adj pr) {S : List ℕ} (hS : SInv n v S) {m : ℕ} (hm : m < n)
    (hmS : m ∉ S) (hadj : ∀ s ∈ S, adj m s = true) : ∀ s ∈ S, pr m s ∉ S := by
  have hvm := not_mem_Sset hs hS hm hmS
  intro s hsS hin
  apply hvm
  have h1 : v m * v s ∈ Sset v S := by
    rw [← (hs.pr_spec m s (hadj s hsS)).2]
    exact Or.inr ⟨pr m s, hin, rfl⟩
  have h2 := (hS.closed _ h1 (v s) (Or.inr ⟨s, hsS, rfl⟩)).1
  have h3 : v m * v s * v s = v m := by rw [mul_assoc, (hs.sq s (hS.lt s hsS)).1, mul_one]
  rwa [h3] at h2

theorem sinv_child (hs : Setting n v adj pr) {S : List ℕ} (hS : SInv n v S) {m : ℕ} (hm : m < n)
    (hmS : m ∉ S) (hadj : ∀ s ∈ S, adj m s = true) : SInv n v (childS pr S m) := by
  have hprv : ∀ s ∈ S, v (pr m s) = v m * v s := fun s hsS => (hs.pr_spec m s (hadj s hsS)).2
  have hprlt : ∀ s ∈ S, pr m s < n := fun s hsS => (hs.pr_spec m s (hadj s hsS)).1
  have hvm := not_mem_Sset hs hS hm hmS
  have hprS := pr_not_mem hs hS hm hmS hadj
  refine ⟨?_, ?_, ?_⟩
  · refine List.nodup_cons.2 ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_map, not_or, not_exists, not_and]
      refine ⟨hmS, fun s hsS hpm => ?_⟩
      have := hprv s hsS
      rw [hpm] at this
      have h1 : v s = 1 := by
        have : v m * v s = v m * 1 := by rw [← this, mul_one]
        exact mul_left_cancel this
      exact (hs.sq s (hS.lt s hsS)).2 h1
    · refine List.nodup_append.2 ⟨hS.nodup, ?_, ?_⟩
      · refine hS.nodup.map_on ?_
        intro x hx y hy hxy
        have h1 : v m * v x = v m * v y := by rw [← hprv x hx, ← hprv y hy, hxy]
        exact hs.inj x y (hS.lt x hx) (hS.lt y hy) (mul_left_cancel h1)
      · intro a ha1 b hb hab
        obtain ⟨s, hsS, rfl⟩ := List.mem_map.1 hb
        exact hprS s hsS (hab ▸ ha1)
  · intro i hi
    simp only [childS, List.mem_cons, List.mem_append, List.mem_map] at hi
    rcases hi with rfl | hi | ⟨s, hsS, rfl⟩
    · exact hm
    · exact hS.lt i hi
    · exact hprlt s hsS
  · rw [Sset_child hs hadj]
    refine closed_ext hS.closed (hs.sq m hm).1 ?_
    rintro x (rfl | ⟨s, hsS, rfl⟩)
    · simp
    · exact comm_of_adj hs (hadj s hsS)

theorem exists_kid (hs : Setting n v adj pr) {S cand : List ℕ} {lo : ℕ} {F : Finset G}
    (hS : SInv n v S) (hc : ∀ c < n, c ∉ S → (∀ s ∈ S, adj c s = true) → c ∈ cand)
    (hF : GoodF n v F) (hSF : ∀ i ∈ S, v i ∈ F) (hlo : ∀ i < n, v i ∈ F → i ∉ S → lo ≤ i)
    (hex : ∃ i < n, v i ∈ F ∧ i ∉ S) :
    ∃ m < n, v m ∈ F ∧ m ∉ S ∧ (∀ i < n, v i ∈ F → i ∉ S → m ≤ i) ∧
      (∀ s ∈ S, adj m s = true) ∧ m ∈ kids pr S cand lo := by
  classical
  have hex' : ∃ i, i < n ∧ v i ∈ F ∧ i ∉ S := by
    obtain ⟨i, hi, h1, h2⟩ := hex
    exact ⟨i, hi, h1, h2⟩
  obtain ⟨hm, hmF, hmS⟩ := Nat.find_spec hex'
  have hmin : ∀ i < n, v i ∈ F → i ∉ S → Nat.find hex' ≤ i := fun i hi hiF hiS =>
    Nat.find_min' hex' ⟨hi, hiF, hiS⟩
  generalize Nat.find hex' = m at hm hmF hmS hmin
  have hadj : ∀ s ∈ S, adj m s = true := fun s hsS =>
    adj_of_mem hs hF hm (hS.lt s hsS) hmF (hSF s hsS) (fun h => hmS (by rw [h]; exact hsS))
  refine ⟨m, hm, hmF, hmS, hmin, hadj, ?_⟩
  have hprS := pr_not_mem hs hS hm hmS hadj
  simp only [kids, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨hc m hm hmS hadj, hlo m hm hmF hmS, fun s hsS => ?_⟩
  obtain ⟨hlt, hv⟩ := hs.pr_spec m s (hadj s hsS)
  have hF1 : v (pr m s) ∈ F := by rw [hv]; exact (hF.mul _ hmF _ (hSF s hsS)).1
  have hle := hmin (pr m s) hlt hF1 (hprS s hsS)
  refine lt_of_le_of_ne hle fun heq => ?_
  have : v m * v s = v m * 1 := by rw [← hv, ← heq, mul_one]
  exact (hs.sq s (hS.lt s hsS)).2 (mul_left_cancel this)

theorem card_childS (pr : ℕ → ℕ → ℕ) (S : List ℕ) (m : ℕ) :
    (childS pr S m).length + 1 = 2 * (S.length + 1) := by
  simp only [childS, List.length_cons, List.length_append, List.length_map]
  omega

theorem dfs_sound (hs : Setting n v adj pr) :
    ∀ (d : ℕ) (S cand : List ℕ) (lo : ℕ) (F : Finset G), SInv n v S →
      (∀ c < n, c ∉ S → (∀ s ∈ S, adj c s = true) → c ∈ cand) → GoodF n v F →
      (∀ i ∈ S, v i ∈ F) → (∀ i < n, v i ∈ F → i ∉ S → lo ≤ i) →
      dfs adj pr d S cand lo = true → F.card ≤ 2 ^ d * (S.length + 1) := by
  intro d
  induction d with
  | zero =>
    intro S cand lo F hS hc hF hSF hlo hd
    by_cases hex : ∃ i < n, v i ∈ F ∧ i ∉ S
    · exfalso
      obtain ⟨m, -, -, -, -, -, hmk⟩ := exists_kid hs hS hc hF hSF hlo hex
      simp only [dfs, List.isEmpty_iff] at hd
      rw [hd] at hmk
      exact List.not_mem_nil hmk
    · push Not at hex
      rw [pow_zero, one_mul]
      refine card_le_Sset (v := v) S fun x hx => ?_
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · obtain ⟨i, hi, rfl⟩ := hF.mem x hx hx1
        exact Or.inr ⟨i, hex i hi hx, rfl⟩
  | succ d ih =>
    intro S cand lo F hS hc hF hSF hlo hd
    by_cases hex : ∃ i < n, v i ∈ F ∧ i ∉ S
    · obtain ⟨m, hm, hmF, hmS, hmin, hadj, hmk⟩ := exists_kid hs hS hc hF hSF hlo hex
      simp only [dfs, List.all_eq_true] at hd
      have hd' := hd m hmk
      have hS' := sinv_child hs hS hm hmS hadj
      have hprv : ∀ s ∈ S, v (pr m s) = v m * v s := fun s hsS =>
        (hs.pr_spec m s (hadj s hsS)).2
      have hih := ih (childS pr S m) (childCand adj pr S cand m) (m + 1) F hS' ?_ hF ?_ ?_ hd'
      · calc F.card ≤ 2 ^ d * ((childS pr S m).length + 1) := hih
          _ = 2 ^ d * (2 * (S.length + 1)) := by rw [card_childS]
          _ = 2 ^ (d + 1) * (S.length + 1) := by rw [pow_succ]; ring
      · intro c hcn hcS hcadj
        have hcS' : c ∉ S := fun h => hcS (by simp [childS, h])
        have hc1 : ∀ s ∈ S, adj c s = true := fun s hsS => hcadj s (by simp [childS, hsS])
        have hcm : adj c m = true := hcadj m (by simp [childS])
        have hcpr : ∀ s ∈ S, adj c (pr m s) = true := fun s hsS =>
          hcadj _ (by simp only [childS, List.mem_cons, List.mem_append, List.mem_map]
                      exact Or.inr (Or.inr ⟨s, hsS, rfl⟩))
        simp only [childCand, List.mem_filter, Bool.and_eq_true, List.all_eq_true]
        exact ⟨hc c hcn hcS' hc1, hs.adj_symm hcm, fun s hsS => hs.adj_symm (hcpr s hsS)⟩
      · intro i hi
        simp only [childS, List.mem_cons, List.mem_append, List.mem_map] at hi
        rcases hi with rfl | hi | ⟨s, hsS, rfl⟩
        · exact hmF
        · exact hSF i hi
        · rw [hprv s hsS]
          exact (hF.mul _ hmF _ (hSF s hsS)).1
      · intro i hi hiF hiS
        have hiS' : i ∉ S := fun h => hiS (by simp [childS, h])
        have him : i ≠ m := fun h => hiS (by simp [childS, h])
        have := hmin i hi hiF hiS'
        omega
    · push Not at hex
      have hle : F.card ≤ S.length + 1 := by
        refine card_le_Sset (v := v) S fun x hx => ?_
        by_cases hx1 : x = 1
        · exact Or.inl hx1
        · obtain ⟨i, hi, rfl⟩ := hF.mem x hx hx1
          exact Or.inr ⟨i, hex i hi hx, rfl⟩
      calc F.card ≤ S.length + 1 := hle
        _ ≤ 2 ^ (d + 1) * (S.length + 1) :=
          Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)

end

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5
