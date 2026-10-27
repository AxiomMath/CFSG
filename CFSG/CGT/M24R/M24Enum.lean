module

public import CFSG.CGT.M24R.RelData
public import CFSG.Certificates.CosetTableColumns
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.CGT.M24R

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration

abbrev m24Presented : Type := PG 11 m24Rels

noncomputable abbrev n8Sub : Subgroup m24Presented :=
  genSub {r : FreeGroup (Fin 11) | r ∈ m24Rels.map FreeGroup.mk} (subsetOf 11 (List.range 10))

theorem index_genSub_le_of_subsetCheckC {m : ℕ} (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {cap n : ℕ} (h : subsetCheckC ws S cap n = true) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).index ≤ n :=
  index_le_of_check (goodColParams ws _ _ (genSub_words_mem ws (subsetOf m S)))
    (by simpa [colParams, mkParams] using closure_colLetter ws) h

@[expose] def N8Bound : Prop := Finite n8Sub ∧ Nat.card n8Sub ≤ 322560

theorem m24Presented_card_le (h : n8Sub.FiniteIndex ∧ n8Sub.index ≤ 759) (hN8 : N8Bound) :
    Finite m24Presented ∧ Nat.card m24Presented ≤ 244823040 := by
  obtain ⟨hfi, hidx⟩ := h
  obtain ⟨hfin, hcard⟩ := hN8
  have hG : Finite m24Presented := by
    have : Finite (m24Presented ⧸ n8Sub) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient n8Sub
  refine ⟨hG, ?_⟩
  rw [← n8Sub.index_mul_card]
  exact (Nat.mul_le_mul hidx hcard).trans (by norm_num)

theorem lift_castSucc_mk (w : List (Fin 10 × Bool)) :
    FreeGroup.lift (fun i : Fin 10 => (PresentedGroup.of (Fin.castSucc i) : m24Presented))
      (FreeGroup.mk w) = PresentedGroup.mk _ (FreeGroup.mk (liftW10 w)) := by
  have h : FreeGroup.lift (fun i : Fin 10 => (PresentedGroup.of (Fin.castSucc i) : m24Presented)) =
      (PresentedGroup.mk _).comp (FreeGroup.map Fin.castSucc) := by
    ext i
    simp [PresentedGroup.of]
  rw [h, MonoidHom.comp_apply, FreeGroup.map.mk]
  rfl

theorem n8Bound_of_presentation (ws : List (List (Fin 10 × Bool)))
    (hws : ∀ w ∈ ws, liftW10 w ∈ m24Rels) [Finite (PG 10 ws)]
    (hcard : Nat.card (PG 10 ws) ≤ 322560) : N8Bound := by
  set f : Fin 10 → m24Presented := fun i => PresentedGroup.of (Fin.castSucc i) with hf
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 10) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [hf, lift_castSucc_mk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (hws w hw))
  set φ : PG 10 ws →* m24Presented := PresentedGroup.toGroup hrel with hφ
  have hrange : φ.range = n8Sub := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨Fin.castSucc i, ?_, ?_⟩
      · simp [subsetOf, List.mem_filter, List.mem_range]
      · simp [φ, f]
    · rintro ⟨j, hj, rfl⟩
      have hj' : j.val < 10 := by simpa [subsetOf, List.mem_filter, List.mem_range] using hj
      exact ⟨⟨j.val, hj'⟩, by simp [φ, f, Fin.castSucc]⟩
  rw [N8Bound, ← hrange]
  have hs : Function.Surjective (fun g => (⟨φ g, g, rfl⟩ : φ.range)) :=
    fun ⟨_, g, hg⟩ => ⟨g, Subtype.ext hg⟩
  exact ⟨Finite.of_surjective _ hs, (Nat.card_le_card_of_surjective _ hs).trans hcard⟩

theorem n8Bound_of_relsN8Ten [Finite (PG 10 relsN8Ten)]
    (hcard : Nat.card (PG 10 relsN8Ten) ≤ 322560) : N8Bound :=
  n8Bound_of_presentation relsN8Ten (fun w hw => by
    rw [m24Rels, List.mem_append, List.mem_append, relsN8_eq_map]
    exact Or.inl (Or.inl (List.mem_map_of_mem hw))) hcard

end CFSG.CGT.M24R
