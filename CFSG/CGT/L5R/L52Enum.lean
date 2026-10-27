module

public import CFSG.CGT.L5R.L52EnumInputs
public import CFSG.CGT.M24R.M24Enum

public section

namespace CFSG.CGT.L5R

open CFSG.CosetTable CFSG.CGT.M24R

abbrev l52Presented : Type := PG 11 l52Rels

noncomputable abbrev l52Sub : Subgroup l52Presented :=
  genSub {r : FreeGroup (Fin 11) | r ∈ l52Rels.map FreeGroup.mk} (subsetOf 11 (List.range 10))

theorem index_l52Sub_le (h : l52Enum = true) : l52Sub.FiniteIndex ∧ l52Sub.index ≤ 31 :=
  index_genSub_le_of_subsetCheckC l52Rels (List.range 10) h

theorem lift_castSucc_mk_pg (ws : List M24Word) (w : List (Fin 10 × Bool)) :
    FreeGroup.lift (fun i : Fin 10 => (PresentedGroup.of (Fin.castSucc i) : PG 11 ws))
      (FreeGroup.mk w) = PresentedGroup.mk _ (FreeGroup.mk (liftW10 w)) := by
  have h : FreeGroup.lift (fun i : Fin 10 => (PresentedGroup.of (Fin.castSucc i) : PG 11 ws)) =
      (PresentedGroup.mk _).comp (FreeGroup.map Fin.castSucc) := by
    ext i
    simp [PresentedGroup.of]
  rw [h, MonoidHom.comp_apply, FreeGroup.map.mk]
  rfl

theorem genSub_ten_card_le (ws : List M24Word) (vs : List (List (Fin 10 × Bool)))
    (hvs : ∀ w ∈ vs, liftW10 w ∈ ws) [Finite (PG 10 vs)] :
    Finite (genSub {r : FreeGroup (Fin 11) | r ∈ ws.map FreeGroup.mk}
        (subsetOf 11 (List.range 10))) ∧
      Nat.card (genSub {r : FreeGroup (Fin 11) | r ∈ ws.map FreeGroup.mk}
        (subsetOf 11 (List.range 10))) ≤ Nat.card (PG 10 vs) := by
  set f : Fin 10 → PG 11 ws := fun i => PresentedGroup.of (Fin.castSucc i) with hf
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 10) | r ∈ vs.map FreeGroup.mk}, FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [hf, lift_castSucc_mk_pg]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (hvs w hw))
  set φ : PG 10 vs →* PG 11 ws := PresentedGroup.toGroup hrel with hφ
  have hrange : φ.range =
      genSub {r : FreeGroup (Fin 11) | r ∈ ws.map FreeGroup.mk} (subsetOf 11 (List.range 10)) := by
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
  rw [← hrange]
  have hs : Function.Surjective (fun g => (⟨φ g, g, rfl⟩ : φ.range)) :=
    fun ⟨_, g, hg⟩ => ⟨g, Subtype.ext hg⟩
  exact ⟨Finite.of_surjective _ hs, Nat.card_le_card_of_surjective _ hs⟩

theorem l52Sub_card_le [Finite (PG 10 relsN8Ten)] :
    Finite l52Sub ∧ Nat.card l52Sub ≤ Nat.card (PG 10 relsN8Ten) :=
  genSub_ten_card_le l52Rels relsN8Ten fun w hw => by
    rw [l52Rels, List.mem_append, List.mem_append, relsN8_eq_map]
    exact Or.inl (Or.inl (List.mem_map_of_mem hw))

theorem l52Presented_card_le (h : l52Enum = true) [Finite (PG 10 relsN8Ten)]
    (hN8 : Nat.card (PG 10 relsN8Ten) ≤ 322560) :
    Finite l52Presented ∧ Nat.card l52Presented ≤ 9999360 := by
  obtain ⟨hfi, hidx⟩ := index_l52Sub_le h
  obtain ⟨hfin, hcard⟩ := l52Sub_card_le
  have hG : Finite l52Presented := by
    have : Finite (l52Presented ⧸ l52Sub) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient l52Sub
  refine ⟨hG, ?_⟩
  rw [← l52Sub.index_mul_card]
  exact (Nat.mul_le_mul hidx (hcard.trans hN8)).trans (by norm_num)

end CFSG.CGT.L5R
