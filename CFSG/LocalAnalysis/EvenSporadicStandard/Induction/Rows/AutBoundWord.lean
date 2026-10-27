module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundRigid
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound

variable {G : Type*} [Group G]

@[expose] def tupleWord (b : ℕ → G) (w : G) (t : List ℕ) : G :=
  (t.map fun l => if l = 0 then w else b (l - 1)).prod

theorem tupleWord_nil (b : ℕ → G) (w : G) : tupleWord b w [] = 1 := rfl

theorem tupleWord_cons (b : ℕ → G) (w : G) (l : ℕ) (t : List ℕ) :
    tupleWord b w (l :: t) = (if l = 0 then w else b (l - 1)) * tupleWord b w t := by
  simp [tupleWord]

theorem map_tupleWord {H : Type*} [Group H] (φ : G →* H) (b : ℕ → G) (w : G) (t : List ℕ) :
    φ (tupleWord b w t) = tupleWord (fun j => φ (b j)) (φ w) t := by
  induction t with
  | nil => simp [tupleWord_nil]
  | cons l t ih =>
    rw [tupleWord_cons, tupleWord_cons, map_mul, ih]
    split_ifs <;> rfl

theorem aut_tupleWord (α : MulAut G) (b : ℕ → G) (w : G) (t : List ℕ)
    (h : ∀ l ∈ t, 1 ≤ l → α (b (l - 1)) = b (l - 1)) :
    α (tupleWord b w t) = tupleWord b (α w) t := by
  induction t with
  | nil => simp [tupleWord_nil]
  | cons l t ih =>
    rw [tupleWord_cons, tupleWord_cons, map_mul,
      ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]
    by_cases hl : l = 0
    · simp [hl]
    · have := h l (List.mem_cons_self ..) (by omega)
      simp [hl, this]

theorem orderOf_aut_tupleWord (α : MulAut G) (b : ℕ → G) (w : G) (t : List ℕ)
    (h : ∀ l ∈ t, 1 ≤ l → α (b (l - 1)) = b (l - 1)) :
    orderOf (tupleWord b (α w) t) = orderOf (tupleWord b w t) := by
  rw [← aut_tupleWord α b w t h]
  exact MulEquiv.orderOf_eq α _

theorem coe_tupleWord (H : Subgroup G) (b : ℕ → H) (w : H) (t : List ℕ) :
    ((tupleWord b w t : H) : G) = tupleWord (fun j => (b j : G)) (w : G) t :=
  map_tupleWord H.subtype b w t

theorem orderOf_coe_tupleWord (H : Subgroup G) (b : ℕ → H) (w : H) (t : List ℕ) :
    orderOf (tupleWord (fun j => (b j : G)) (w : G) t) = orderOf (tupleWord b w t) := by
  rw [← coe_tupleWord H b w t]
  exact Subgroup.orderOf_coe _

theorem closure_eq_top_of_closure_coe (H : Subgroup G) (b : ℕ → H) (s : Set ℕ)
    (h : Subgroup.closure ((fun j => (b j : G)) '' s) = H) : Subgroup.closure (b '' s) = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  have h1 : (Subgroup.closure (b '' s)).map H.subtype =
      Subgroup.closure (H.subtype '' (b '' s)) := MonoidHom.map_closure _ _
  have h2 : H.subtype '' (b '' s) = (fun j => (b j : G)) '' s := by
    rw [Set.image_image]
    rfl
  rw [h1, h2, h, Subgroup.map_top, Subgroup.range_subtype]

@[expose] def testClass (b : ℕ → G) (u : G) (tests : List (List ℕ × ℕ)) : Set G :=
  {w | w ∈ conjClass u ∧ ∀ t ∈ tests, orderOf (tupleWord b w t.1) = t.2}

theorem aut_mem_testClass (α : MulAut G) (b : ℕ → G) {i : ℕ} (hi : 1 ≤ i)
    (hfix : ∀ j < i, α (b j) = b j) (hcl : b i ∈ conjClass (b 0))
    {tests : List (List ℕ × ℕ)} (hlet : ∀ t ∈ tests, ∀ l ∈ t.1, l < i + 1)
    (hord : ∀ t ∈ tests, orderOf (tupleWord b (b i) t.1) = t.2) :
    α (b i) ∈ testClass b (b 0) tests := by
  refine ⟨?_, fun t ht => ?_⟩
  · obtain ⟨g, hg⟩ := mem_conjClass_iff.1 hcl
    refine mem_conjClass_iff.2 ⟨α g, ?_⟩
    rw [hg, map_mul, map_mul, hfix 0 (by omega), map_inv]
  · rw [orderOf_aut_tupleWord α b (b i) t.1 (fun l hl hl1 => hfix _ (by
      have := hlet t ht l hl
      omega))]
    exact hord t ht

theorem coe_testClass_subset (H : Subgroup G) (b : ℕ → H) (u : H) (tests : List (List ℕ × ℕ)) :
    Subtype.val '' testClass b u tests ⊆ {z : G | (∃ d ∈ H, z = d * (u : G) * d⁻¹) ∧
      ∀ t ∈ tests, orderOf (tupleWord (fun j => (b j : G)) z t.1) = t.2} := by
  rintro _ ⟨w, ⟨hwc, hw⟩, rfl⟩
  obtain ⟨g, hg⟩ := mem_conjClass_iff.1 hwc
  refine ⟨⟨(g : G), g.2, ?_⟩, fun t ht => ?_⟩
  · rw [hg]
    simp
  · rw [orderOf_coe_tupleWord H b w t.1]
    exact hw t ht

end CFSG.EvenSporadicStandard.Induction.AutBound
