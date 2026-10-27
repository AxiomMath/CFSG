module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Graph
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G]

theorem cp_mul_self_eq_one_of_orderOf_eq_two {X : Type*} [Group X] {x : X}
    (h : orderOf x = 2) : x * x = 1 := by
  have hpow := pow_orderOf_eq_one x
  rwa [h, pow_two] at hpow

theorem cp_ne_one_of_orderOf_eq_two {X : Type*} [Group X] {x : X}
    (h : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  omega

private theorem elem2_mul_self (g : Elem2 2) : g * g = 1 := by
  apply Multiplicative.toAdd.injective
  show g.toAdd + g.toAdd = 0
  funext i
  exact CharTwo.add_self_eq_zero (g.toAdd i)

private theorem natCard_elem2_two : Nat.card (Elem2 2) = 4 := by
  show Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

private instance elem2Nontrivial : Nontrivial (Elem2 2) where
  exists_pair_ne := ⟨1, Multiplicative.ofAdd (fun _ : Fin 2 => (1 : ZMod 2)), by
    intro h
    have h' := congrFun (congrArg Multiplicative.toAdd h) 0
    exact (zero_ne_one (α := ZMod 2)) h'⟩

private instance elem2KleinFour : IsKleinFour (Elem2 2) where
  card_four := natCard_elem2_two
  exponent_two := by
    rw [Monoid.exponent_eq_prime_iff (p := 2) (by norm_num)]
    intro g hg
    exact orderOf_eq_prime (by rw [pow_two]; exact elem2_mul_self g) hg

theorem cp_isKleinFour_elem2 : IsKleinFour (Elem2 2) := inferInstance

private theorem mem_closure_pair_comm {X : Type*} [Group X] {u v x : X} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v = v * u) :
    x ∈ Subgroup.closure ({u, v} : Set X) ↔ x = 1 ∨ x = u ∨ x = v ∨ x = u * v := by
  have hu' : ∀ y, u * (u * y) = y := fun y => by rw [← mul_assoc, hu, one_mul]
  have hvu : ∀ y, v * (u * y) = u * (v * y) := fun y => by
    rw [← mul_assoc, ← huv, mul_assoc]
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have humem : u ∈ ({u, v} : Set X) := by simp
  have hvmem : v ∈ ({u, v} : Set X) := by simp
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, hu, hv, hu', hvu, huv.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hui, hvi, mul_inv_rev, huv.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact (Subgroup.closure ({u, v} : Set X)).one_mem
    · exact Subgroup.subset_closure humem
    · exact Subgroup.subset_closure hvmem
    · exact (Subgroup.closure ({u, v} : Set X)).mul_mem
        (Subgroup.subset_closure humem) (Subgroup.subset_closure hvmem)

private theorem closure_three_eq_pair {X : Type*} [Group X] {u v : X} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v = v * u) :
    Subgroup.closure ({u, v, u * v} : Set X) = Subgroup.closure ({u, v} : Set X) := by
  have humem : u ∈ ({u, v} : Set X) := by simp
  have hvmem : v ∈ ({u, v} : Set X) := by simp
  have humem' : u ∈ ({u, v, u * v} : Set X) := by simp
  have hvmem' : v ∈ ({u, v, u * v} : Set X) := by simp
  apply le_antisymm
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure humem
      · exact Subgroup.subset_closure hvmem
      · exact (Subgroup.closure ({u, v} : Set X)).mul_mem
          (Subgroup.subset_closure humem) (Subgroup.subset_closure hvmem)
    | one => exact (Subgroup.closure ({u, v} : Set X)).one_mem
    | mul a b _ _ ha hb => exact (Subgroup.closure ({u, v} : Set X)).mul_mem ha hb
    | inv a _ ha => exact (Subgroup.closure ({u, v} : Set X)).inv_mem ha
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Subgroup.subset_closure humem'
      · exact Subgroup.subset_closure hvmem'
    | one => exact (Subgroup.closure ({u, v, u * v} : Set X)).one_mem
    | mul a b _ _ ha hb => exact (Subgroup.closure ({u, v, u * v} : Set X)).mul_mem ha hb
    | inv a _ ha => exact (Subgroup.closure ({u, v, u * v} : Set X)).inv_mem ha

private theorem card_closure_pair_comm {X : Type*} [Group X] {u v : X} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u ≠ v) :
    Nat.card (Subgroup.closure ({u, v} : Set X)) = 4 := by
  have huv_ne_one : u * v ≠ 1 := by
    intro h
    refine hne ?_
    have hv_eq : v = u := by
      calc v = u⁻¹ * (u * v) := (inv_mul_cancel_left u v).symm
        _ = u⁻¹ * 1 := by rw [h]
        _ = u := by rw [mul_one, inv_eq_of_mul_eq_one_right hu]
    exact hv_eq.symm
  have huv_ne_u : u * v ≠ u := by
    intro h
    refine hv1 ?_
    calc v = u⁻¹ * (u * v) := (inv_mul_cancel_left u v).symm
      _ = u⁻¹ * u := by rw [h]
      _ = 1 := inv_mul_cancel u
  have huv_ne_v : u * v ≠ v := by
    intro h
    refine hu1 ?_
    calc u = (u * v) * v⁻¹ := (mul_inv_cancel_right u v).symm
      _ = v * v⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel v
  have hset : ((Subgroup.closure ({u, v} : Set X)) : Set X) = {1, u, v, u * v} := by
    ext x
    change x ∈ Subgroup.closure ({u, v} : Set X) ↔ x ∈ ({1, u, v, u * v} : Set X)
    rw [mem_closure_pair_comm hu hv huv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have h1 : (1 : X) ∉ ({u, v, u * v} : Set X) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hu1.symm, hv1.symm, huv_ne_one.symm⟩
  have h2 : u ∉ ({v, u * v} : Set X) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, huv_ne_u.symm⟩
  have h3 : v ∉ ({u * v} : Set X) := by
    simp only [Set.mem_singleton_iff]
    exact huv_ne_v.symm
  calc Nat.card (Subgroup.closure ({u, v} : Set X))
      = ((Subgroup.closure ({u, v} : Set X)) : Set X).ncard := Nat.card_coe_set_eq _
    _ = ({1, u, v, u * v} : Set X).ncard := by rw [hset]
    _ = 4 := by
        rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
          Set.ncard_insert_of_notMem h3, Set.ncard_singleton]

private theorem isKleinFour_closure_three_comm {X : Type*} [Group X] {u v : X}
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u ≠ v) :
    IsKleinFour (Subgroup.closure ({u, v, u * v} : Set X)) := by
  have hEq := closure_three_eq_pair hu hv huv
  refine ⟨?_, ?_⟩
  · rw [hEq]
    exact card_closure_pair_comm hu hv huv hu1 hv1 hne
  · have hsquare : ∀ x : ↥(Subgroup.closure ({u, v, u * v} : Set X)), x * x = 1 := by
      intro x
      have hx : (x : X) ∈ Subgroup.closure ({u, v} : Set X) := by
        rw [← hEq]
        exact x.2
      rw [mem_closure_pair_comm hu hv huv] at hx
      apply Subtype.ext
      change (x : X) * (x : X) = 1
      rcases hx with h | h | h | h
      · rw [h, one_mul]
      · rw [h]; exact hu
      · rw [h]; exact hv
      · rw [h]
        calc u * v * (u * v) = u * (v * u) * v := by group
          _ = u * (u * v) * v := by rw [← huv]
          _ = u * u * (v * v) := by group
          _ = 1 := by rw [hu, hv, mul_one]
    apply Nat.dvd_antisymm
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      rw [pow_two]
      exact hsquare x
    · let U : ↥(Subgroup.closure ({u, v, u * v} : Set X)) :=
        ⟨u, Subgroup.subset_closure (by simp)⟩
      have hU1 : U ≠ 1 := by
        intro h
        exact hu1 (by simpa [U] using congrArg Subtype.val h)
      have hUord : orderOf U = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hsquare U) hU1
      have := Monoid.order_dvd_exponent U
      rwa [hUord] at this

theorem cp_isLine_of_comm {c u v : G} (hc : c ≠ 1) (hcu : IsConj c u) (hcv : IsConj c v)
    (hcuv : IsConj c (u * v)) (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u)
    (hne : u ≠ v) : IsLine c {u, v, u * v} := by
  have hu1 : u ≠ 1 := fun h => hc (isConj_one_left.mp (h ▸ hcu))
  have hv1 : v ≠ 1 := fun h => hc (isConj_one_left.mp (h ▸ hcv))
  have huv_ne_u : u * v ≠ u := by
    intro h
    refine hv1 ?_
    calc v = u⁻¹ * (u * v) := (inv_mul_cancel_left u v).symm
      _ = u⁻¹ * u := by rw [h]
      _ = 1 := inv_mul_cancel u
  have huv_ne_v : u * v ≠ v := by
    intro h
    refine hu1 ?_
    calc u = (u * v) * v⁻¹ := (mul_inv_cancel_right u v).symm
      _ = v * v⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel v
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hcu
    · exact hcv
    · exact hcuv
  · rw [Set.ncard_eq_three]
    exact ⟨u, v, u * v, hne, huv_ne_u.symm, huv_ne_v.symm, rfl⟩
  · haveI : IsKleinFour (Subgroup.closure ({u, v, u * v} : Set G)) :=
      isKleinFour_closure_three_comm hu hv huv hu1 hv1 hne
    exact IsKleinFour.nonempty_mulEquiv

end CFSG.EvenSporadicStandard.HNRecog.Section4
