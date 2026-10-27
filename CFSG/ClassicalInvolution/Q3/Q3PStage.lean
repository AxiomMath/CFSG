module

public import CFSG.ClassicalInvolution.Q3.Q3PBranch

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G]

theorem card_closure_pair_le_four [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 4 := by
  classical
  have hba : b * a = a * b := hab.symm
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hab' : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, hba, mul_assoc]
  have hsub : ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) ⊆
      (({1, a, b, a * b} : Finset G) : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> simp
    | one => simp
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp [mul_assoc, ha, hb, ha', hab', hba]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;> simp [mul_inv_rev, ia, ib, hba]
  calc Nat.card (Subgroup.closure ({a, b} : Set G))
      = Nat.card ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := rfl
    _ ≤ Nat.card (({1, a, b, a * b} : Finset G) : Set G) := Nat.card_mono (Set.toFinite _) hsub
    _ = Finset.card ({1, a, b, a * b} : Finset G) := Nat.card_eq_finsetCard _
    _ ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp

theorem card_closure_triple_le_four [Finite G] {u v w : G} (hu : u * u = 1) (hv : v * v = 1)
    (hw : w * w = 1) (huv : u * v = v * u) (huw : u * w = w * u) (hvw : v * w = w * v)
    (hdep : u = v ∨ u = w ∨ v = w ∨ u * v = w) :
    Nat.card (Subgroup.closure ({u, v, w} : Set G)) ≤ 4 := by
  have mem : ∀ {a b : G} {x : G}, x = a ∨ x = b → x ∈ Subgroup.closure ({a, b} : Set G) := by
    rintro a b x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  rcases hdep with h | h | h | h
  ·
    have hle : Subgroup.closure ({u, v, w} : Set G) ≤ Subgroup.closure ({u, w} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem (Or.inl rfl)
      · exact mem (Or.inl h.symm)
      · exact mem (Or.inr rfl)
    exact (Subgroup.card_le_of_le hle).trans (card_closure_pair_le_four hu hw huw)
  ·
    have hle : Subgroup.closure ({u, v, w} : Set G) ≤ Subgroup.closure ({u, v} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem (Or.inl rfl)
      · exact mem (Or.inr rfl)
      · exact mem (Or.inl h.symm)
    exact (Subgroup.card_le_of_le hle).trans (card_closure_pair_le_four hu hv huv)
  ·
    have hle : Subgroup.closure ({u, v, w} : Set G) ≤ Subgroup.closure ({u, v} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem (Or.inl rfl)
      · exact mem (Or.inr rfl)
      · exact mem (Or.inr h.symm)
    exact (Subgroup.card_le_of_le hle).trans (card_closure_pair_le_four hu hv huv)
  ·
    have hle : Subgroup.closure ({u, v, w} : Set G) ≤ Subgroup.closure ({u, v} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem (Or.inl rfl)
      · exact mem (Or.inr rfl)
      · rw [← h]
        exact mul_mem (mem (Or.inl rfl)) (mem (Or.inr rfl))
    exact (Subgroup.card_le_of_le hle).trans (card_closure_pair_le_four hu hv huv)

variable [Finite G] {Ω : Set (Subgroup G)}

theorem IndepTriple3.exists_exactTriple (h : IndepTriple3 Ω) :
    ∃ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G), ExactTriple K₁ K₂ K₃ z₁ z₂ z₃ ∧ z₁ * z₂ ≠ z₃ ∧
      (K₁ ∈ Ω ∧ IsClassicalMember3 K₁ z₁) ∧ (K₂ ∈ Ω ∧ IsClassicalMember3 K₂ z₂) ∧
      (K₃ ∈ Ω ∧ IsClassicalMember3 K₃ z₃) := by
  obtain ⟨K, z, hmem, hcomm, hA, hcard⟩ := h
  have hsq : ∀ i, z i * z i = 1 := fun i => by
    have h2 := (hmem i).2.orderOf_eq_two
    have : z i ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
    simpa [pow_two] using this
  have hcen : ∀ i, ∀ k ∈ K i, k * z i = z i * k := fun i k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le (hmem i).2.subnormal hk))
  have hzc : ∀ i j, i ≠ j → z i * z j = z j * z i := fun i j hij =>
    hcomm i j hij (z i) (hmem i).2.mem (z j) (hmem j).2.mem
  have hrange : Set.range z = ({z 0, z 1, z 2} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hle4 : ∀ hdep : z 0 = z 1 ∨ z 0 = z 2 ∨ z 1 = z 2 ∨ z 0 * z 1 = z 2, False := by
    intro hdep
    have := card_closure_triple_le_four (hsq 0) (hsq 1) (hsq 2) (hzc 0 1 (by decide))
      (hzc 0 2 (by decide)) (hzc 1 2 (by decide)) hdep
    rw [← hrange] at this
    omega
  refine ⟨K 0, K 1, K 2, z 0, z 1, z 2, ?_, fun hh => hle4 (Or.inr (Or.inr (Or.inr hh))),
    ⟨(hmem 0).1, (hmem 0).2⟩, ⟨(hmem 1).1, (hmem 1).2⟩, ⟨(hmem 2).1, (hmem 2).2⟩⟩
  exact
    { mem₁ := (hmem 0).2.mem, mem₂ := (hmem 1).2.mem, mem₃ := (hmem 2).2.mem
      central₁ := hcen 0, central₂ := hcen 1, central₃ := hcen 2
      sq₁ := hsq 0, sq₂ := hsq 1, sq₃ := hsq 2
      ne_one₁ := (hmem 0).2.ne_one, ne_one₂ := (hmem 1).2.ne_one, ne_one₃ := (hmem 2).2.ne_one
      comm₁₂ := hcomm 0 1 (by decide), comm₁₃ := hcomm 0 2 (by decide)
      comm₂₃ := hcomm 1 2 (by decide)
      ne₁₂ := fun hh => hle4 (Or.inl hh), ne₁₃ := fun hh => hle4 (Or.inr (Or.inl hh))
      ne₂₃ := fun hh => hle4 (Or.inr (Or.inr (Or.inl hh))) }

theorem IndepTriple3.of_exactTriple {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃)
    (h₁ : K₁ ∈ Ω ∧ IsClassicalMember3 K₁ z₁) (h₂ : K₂ ∈ Ω ∧ IsClassicalMember3 K₂ z₂)
    (h₃ : K₃ ∈ Ω ∧ IsClassicalMember3 K₃ z₃) : IndepTriple3 Ω := by
  have hrange : Set.range ![z₁, z₂, z₃] = ({z₁, z₂, z₃} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  refine ⟨![K₁, K₂, K₃], ![z₁, z₂, z₃], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    exacts [h₁, h₂, h₃]
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact T.comm₁₂
      | exact T.comm₁₃
      | exact T.comm₂₃
      | exact fun a ha b hb => (T.comm₁₂ b hb a ha).symm
      | exact fun a ha b hb => (T.comm₁₃ b hb a ha).symm
      | exact fun a ha b hb => (T.comm₂₃ b hb a ha).symm
  · rw [hrange]
    exact T.isElemAbelian
  · rw [hrange]
    exact T.card_eq_eight hind

theorem indepTriple3_iff :
    IndepTriple3 Ω ↔ ∃ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G),
      ExactTriple K₁ K₂ K₃ z₁ z₂ z₃ ∧ z₁ * z₂ ≠ z₃ ∧
      (K₁ ∈ Ω ∧ IsClassicalMember3 K₁ z₁) ∧ (K₂ ∈ Ω ∧ IsClassicalMember3 K₂ z₂) ∧
      (K₃ ∈ Ω ∧ IsClassicalMember3 K₃ z₃) :=
  ⟨IndepTriple3.exists_exactTriple, fun ⟨_, _, _, _, _, _, T, hind, h₁, h₂, h₃⟩ =>
    IndepTriple3.of_exactTriple T hind h₁ h₂ h₃⟩

end CFSG.ClassicalInvolution.Q3
