module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelBase

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel

namespace Rep

variable {M : RegModel} {H : Type} [Group H]

theorem getElem!_range_map_of_lt {α : Type} [Inhabited α] (f : ℕ → α) {n i : ℕ} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

theorem forall_lt_iff_forall_pt (R : Rep M H) {P : ℕ → Prop} :
    (∀ a, a < M.N → P a) ↔ ∀ h : H, P (R.pt h) := by
  constructor
  · intro hP h
    exact hP _ (R.pt_lt h)
  · intro hP a ha
    obtain ⟨h, rfl⟩ := R.pt_surj a ha
    exact hP h

theorem mem_elems {B : Array Bool} {a : ℕ} : a ∈ elems B ↔ a < B.size ∧ B[a]! = true := by
  simp [elems]

theorem elems_nodup (B : Array Bool) : (elems B).Nodup :=
  List.nodup_range.filter _

theorem mem_elems_iff_exists_pt (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) {a : ℕ} :
    a ∈ elems B ↔ ∃ h : H, R.pt h = a ∧ h ∈ R.set B := by
  rw [mem_elems, hB]
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨h, rfl⟩ := R.pt_surj a ha
    exact ⟨h, rfl, hb⟩
  · rintro ⟨h, rfl, hb⟩
    exact ⟨R.pt_lt h, hb⟩

theorem forall_elems_iff_forall_set (R : Rep M H) {B : Array Bool} (hB : B.size = M.N)
    {P : ℕ → Prop} : (∀ a ∈ elems B, P a) ↔ ∀ h ∈ R.set B, P (R.pt h) := by
  constructor
  · intro hP h hh
    exact hP _ ((R.mem_elems_iff_exists_pt hB).2 ⟨h, rfl, hh⟩)
  · intro hP a ha
    obtain ⟨h, rfl, hh⟩ := (R.mem_elems_iff_exists_pt hB).1 ha
    exact hP h hh

theorem card_eq_ncard (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) :
    card B = (R.set B).ncard := by
  refine R.length_eq_ncard (elems_nodup B) (fun a ha => ?_) (P := fun h => B[R.pt h]! = true)
    (fun h => ?_)
  · have := (mem_elems.1 ha).1
    omega
  · rw [mem_elems]
    exact ⟨fun h' => h'.2, fun h' => ⟨by have := R.pt_lt h; omega, h'⟩⟩

theorem ord_eq (R : Rep M H) (a : H) : M.ord (R.pt a) = orderOf a := by
  have hfin := R.finite
  have hN : 0 < Nat.card H := Nat.card_pos
  have hle : orderOf a ≤ M.N := by
    rw [← R.natCard]
    exact Nat.le_of_dvd hN (orderOf_dvd_natCard a)
  have hp : ∀ k, (k > 0 && M.pw (R.pt a) k == 0) = true ↔ (0 < k ∧ a ^ k = 1) := by
    intro k
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← R.pt_pow, ← R.pt_one, R.pt_inj.eq_iff]
  have key : (List.range (M.N + 1)).find? (fun k => k > 0 && M.pw (R.pt a) k == 0) =
      some (orderOf a) := by
    rw [List.find?_range_eq_some]
    refine ⟨(hp _).2 ⟨orderOf_pos a, pow_orderOf_eq_one a⟩, List.mem_range.2 (by omega),
      fun j hj => ?_⟩
    rw [Bool.not_eq_true']
    by_contra hcon
    obtain ⟨hj0, hj1⟩ := (hp j).1 (by simpa using hcon)
    exact absurd (orderOf_le_of_pow_eq_one hj0 hj1) (by omega)
  unfold RegModel.ord
  rw [key]
  rfl

theorem center_size (R : Rep M H) : M.center.size = M.N := by
  have _ := R
  simp [RegModel.center]

theorem set_center (R : Rep M H) : R.set M.center = (Subgroup.center H : Set H) := by
  ext h
  have h2 : M.center[R.pt h]! =
      (List.range M.N).all (fun b => M.m (R.pt h) b == M.m b (R.pt h)) := by
    unfold RegModel.center
    exact getElem!_range_map_of_lt _ (R.pt_lt h)
  show M.center[R.pt h]! = true ↔ _
  rw [h2, List.all_eq_true, SetLike.mem_coe, Subgroup.mem_center_iff]
  simp only [List.mem_range, beq_iff_eq]
  rw [R.forall_lt_iff_forall_pt (P := fun b => M.m (R.pt h) b = M.m b (R.pt h))]
  refine forall_congr' fun g => ?_
  rw [← R.pt_mul, ← R.pt_mul, R.pt_inj.eq_iff]
  exact eq_comm

theorem cent_size (B : Array Bool) : (M.cent B).size = M.N := by
  simp [RegModel.cent]

theorem set_cent (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) :
    R.set (M.cent B) = {h | ∀ b ∈ R.set B, h * b = b * h} := by
  ext h
  have h2 : (M.cent B)[R.pt h]! =
      (elems B).all (fun b => M.m (R.pt h) b == M.m b (R.pt h)) := by
    unfold RegModel.cent
    exact getElem!_range_map_of_lt _ (R.pt_lt h)
  show (M.cent B)[R.pt h]! = true ↔ _
  rw [h2, List.all_eq_true]
  simp only [beq_iff_eq]
  rw [R.forall_elems_iff_forall_set hB (P := fun b => M.m (R.pt h) b = M.m b (R.pt h))]
  refine forall₂_congr fun g _ => ?_
  rw [← R.pt_mul, ← R.pt_mul, R.pt_inj.eq_iff]

theorem set_bInter (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) :
    R.set (bInter A B) = R.set A ∩ R.set B := by
  ext h
  have hlt : R.pt h < A.size := hA ▸ R.pt_lt h
  have h2 : (bInter A B)[R.pt h]! = (A[R.pt h]! && B[R.pt h]!) := by
    unfold bInter
    exact getElem!_range_map_of_lt (fun i => A[i]! && B[i]!) hlt
  show (bInter A B)[R.pt h]! = true ↔ _
  rw [h2, Bool.and_eq_true]
  rfl

theorem bUnion_size (A B : Array Bool) : (bUnion A B).size = A.size := by
  simp [bUnion]

theorem set_bUnion (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) :
    R.set (bUnion A B) = R.set A ∪ R.set B := by
  ext h
  have hlt : R.pt h < A.size := hA ▸ R.pt_lt h
  have h2 : (bUnion A B)[R.pt h]! = (A[R.pt h]! || B[R.pt h]!) := by
    unfold bUnion
    exact getElem!_range_map_of_lt (fun i => A[i]! || B[i]!) hlt
  show (bUnion A B)[R.pt h]! = true ↔ _
  rw [h2, Bool.or_eq_true]
  rfl

theorem bSubset_iff (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) :
    bSubset A B = true ↔ R.set A ⊆ R.set B := by
  unfold bSubset
  rw [List.all_eq_true]
  simp only [List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  rw [hA, R.forall_lt_iff_forall_pt (P := fun i => A[i]! = false ∨ B[i]! = true)]
  refine forall_congr' fun h => ?_
  rw [R.mem_set, R.mem_set]
  constructor
  · intro hh hAh
    exact hh.resolve_left (by simp [hAh])
  · intro hh
    by_cases hAh : A[R.pt h]! = true
    · exact Or.inr (hh hAh)
    · exact Or.inl (by simpa using hAh)

theorem invols_nodup (B : Array Bool) : (M.invols B).Nodup :=
  (elems_nodup B).filter _

theorem mem_invols (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) {a : ℕ} :
    a ∈ M.invols B ↔ ∃ h : H, R.pt h = a ∧ h ∈ R.set B ∧ h ≠ 1 ∧ h * h = 1 := by
  unfold RegModel.invols
  rw [List.mem_filter, R.mem_elems_iff_exists_pt hB]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨h, rfl, hh⟩, hp⟩
    refine ⟨h, rfl, hh, ?_, ?_⟩
    · rintro rfl
      exact hp.1 R.pt_one
    · apply R.pt_inj
      rw [R.pt_mul, R.pt_one]
      exact hp.2
  · rintro ⟨h, rfl, hh, h1, h2⟩
    refine ⟨⟨h, rfl, hh⟩, fun h0 => h1 (R.pt_inj (by rw [h0, R.pt_one])), ?_⟩
    rw [← R.pt_mul, h2, R.pt_one]

theorem invols_lt (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) :
    ∀ a ∈ M.invols B, a < M.N := by
  intro a ha
  obtain ⟨h, rfl, -⟩ := (R.mem_invols hB).1 ha
  exact R.pt_lt h

theorem ord4_nodup (B : Array Bool) : (M.ord4 B).Nodup :=
  (elems_nodup B).filter _

theorem mem_ord4 (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) {a : ℕ} :
    a ∈ M.ord4 B ↔ ∃ h : H, R.pt h = a ∧ h ∈ R.set B ∧ orderOf h = 4 := by
  unfold RegModel.ord4
  rw [List.mem_filter, R.mem_elems_iff_exists_pt hB]
  simp only [beq_iff_eq]
  constructor
  · rintro ⟨⟨h, rfl, hh⟩, hp⟩
    exact ⟨h, rfl, hh, by rw [← R.ord_eq]; exact hp⟩
  · rintro ⟨h, rfl, hh, h4⟩
    exact ⟨⟨h, rfl, hh⟩, by rw [R.ord_eq]; exact h4⟩

theorem ord4_lt (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) :
    ∀ a ∈ M.ord4 B, a < M.N := by
  intro a ha
  obtain ⟨h, rfl, -⟩ := (R.mem_ord4 hB).1 ha
  exact R.pt_lt h

theorem isAbelian_iff (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) :
    M.isAbelian B = true ↔ ∀ a ∈ R.set B, ∀ b ∈ R.set B, a * b = b * a := by
  unfold RegModel.isAbelian
  simp only [List.all_eq_true, beq_iff_eq]
  rw [R.forall_elems_iff_forall_set hB (P := fun a => ∀ b ∈ elems B, M.m a b = M.m b a)]
  refine forall₂_congr fun a _ => ?_
  rw [R.forall_elems_iff_forall_set hB (P := fun b => M.m (R.pt a) b = M.m b (R.pt a))]
  refine forall₂_congr fun b _ => ?_
  rw [← R.pt_mul, ← R.pt_mul, R.pt_inj.eq_iff]

theorem isElemAb_iff (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) :
    M.isElemAb B = true ↔
      (∀ a ∈ R.set B, ∀ b ∈ R.set B, a * b = b * a) ∧ ∀ a ∈ R.set B, a * a = 1 := by
  unfold RegModel.isElemAb
  rw [Bool.and_eq_true, R.isAbelian_iff hB, List.all_eq_true]
  simp only [beq_iff_eq]
  rw [R.forall_elems_iff_forall_set hB (P := fun a => M.m a a = 0)]
  refine and_congr Iff.rfl (forall₂_congr fun a _ => ?_)
  rw [← R.pt_mul, ← R.pt_one, R.pt_inj.eq_iff]

end Rep

end CFSG.OddStandard.ChengHeld.Model
