module

public import CFSG.CGT.A8S.RelData
public import CFSG.CGT.M24R.Words
public import CFSG.Certificates.CosetTablePresented
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable CFSG.CGT.M24R

abbrev a8Presented : Type := PG 6 a8Rels

noncomputable abbrev a8Sub : Subgroup a8Presented :=
  genSub {r : FreeGroup (Fin 6) | r ∈ a8Rels.map FreeGroup.mk} (subsetOf 6 (List.range 5))

abbrev A8SubIndex : Prop := a8Sub.FiniteIndex ∧ a8Sub.index ≤ 15

theorem lift_castSucc_mk_pg6 (ws : List A8Word) (w : List (Fin 5 × Bool)) :
    FreeGroup.lift (fun i : Fin 5 => (PresentedGroup.of (Fin.castSucc i) : PG 6 ws))
      (FreeGroup.mk w) = PresentedGroup.mk _ (FreeGroup.mk (liftW5 w)) := by
  have h : FreeGroup.lift (fun i : Fin 5 => (PresentedGroup.of (Fin.castSucc i) : PG 6 ws)) =
      (PresentedGroup.mk _).comp (FreeGroup.map Fin.castSucc) := by
    ext i
    simp [PresentedGroup.of]
  rw [h, MonoidHom.comp_apply, FreeGroup.map.mk]
  rfl

theorem genSub_five_card_le (ws : List A8Word) (vs : List (List (Fin 5 × Bool)))
    (hvs : ∀ w ∈ vs, liftW5 w ∈ ws) [Finite (PG 5 vs)] :
    Finite (genSub {r : FreeGroup (Fin 6) | r ∈ ws.map FreeGroup.mk}
        (subsetOf 6 (List.range 5))) ∧
      Nat.card (genSub {r : FreeGroup (Fin 6) | r ∈ ws.map FreeGroup.mk}
        (subsetOf 6 (List.range 5))) ≤ Nat.card (PG 5 vs) := by
  set f : Fin 5 → PG 6 ws := fun i => PresentedGroup.of (Fin.castSucc i) with hf
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ vs.map FreeGroup.mk}, FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [hf, lift_castSucc_mk_pg6]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (hvs w hw))
  set φ : PG 5 vs →* PG 6 ws := PresentedGroup.toGroup hrel with hφ
  have hrange : φ.range =
      genSub {r : FreeGroup (Fin 6) | r ∈ ws.map FreeGroup.mk} (subsetOf 6 (List.range 5)) := by
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
      have hj' : j.val < 5 := by simpa [subsetOf, List.mem_filter, List.mem_range] using hj
      exact ⟨⟨j.val, hj'⟩, by simp [φ, f, Fin.castSucc]⟩
  rw [← hrange]
  have hs : Function.Surjective (fun g => (⟨φ g, g, rfl⟩ : φ.range)) :=
    fun ⟨_, g, hg⟩ => ⟨g, Subtype.ext hg⟩
  exact ⟨Finite.of_surjective _ hs, Nat.card_le_card_of_surjective _ hs⟩

theorem liftW5_mem_a8Rels {w : List (Fin 5 × Bool)} (hw : w ∈ relsN0A8) : liftW5 w ∈ a8Rels := by
  rw [a8Rels, List.mem_append, List.mem_append]
  exact Or.inl (Or.inl (List.mem_map_of_mem hw))

theorem a8Sub_card_le [Finite (PG 5 relsN0A8)] :
    Finite a8Sub ∧ Nat.card a8Sub ≤ Nat.card (PG 5 relsN0A8) :=
  genSub_five_card_le a8Rels relsN0A8 fun _ hw => liftW5_mem_a8Rels hw

theorem a8Presented_card_le (h : A8SubIndex) [Finite (PG 5 relsN0A8)]
    (hN0 : Nat.card (PG 5 relsN0A8) ≤ 1344) :
    Finite a8Presented ∧ Nat.card a8Presented ≤ 20160 := by
  obtain ⟨hfi, hidx⟩ := h
  obtain ⟨hfin, hcard⟩ := a8Sub_card_le
  have hG : Finite a8Presented := by
    have : Finite (a8Presented ⧸ a8Sub) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient a8Sub
  refine ⟨hG, ?_⟩
  rw [← a8Sub.index_mul_card]
  exact (Nat.mul_le_mul hidx (hcard.trans hN0)).trans (by norm_num)

end CFSG.CGT.A8S
