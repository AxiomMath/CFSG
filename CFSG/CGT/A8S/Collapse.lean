module

public import CFSG.CGT.A8S.CollapseInputs

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration

abbrev CollapseA8 (k : Fin 7) : Prop :=
  (genSub {r : FreeGroup (Fin 6) | r ∈ (collRelsA8 k).map FreeGroup.mk}
      (subsetOf 6 (List.range 5))).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 6) | r ∈ (collRelsA8 k).map FreeGroup.mk}
      (subsetOf 6 (List.range 5))).index ≤ 1

theorem mem_closure_of_collapseCheckA8 {k : Fin 7} (hc : CollapseA8 k) {H : Type*}
    [Group H] (e : Fin 6 → H) (hrels : ∀ r ∈ collRelsA8 k, evalA8 e r = 1) :
    e 5 ∈ Subgroup.closure (Set.range fun i : Fin 5 => e (Fin.castSucc i)) := by
  set rels := {r : FreeGroup (Fin 6) | r ∈ (collRelsA8 k).map FreeGroup.mk}
  have htop : genSub rels (subsetOf 6 (List.range 5)) = ⊤ :=
    Subgroup.index_eq_one.mp (Nat.le_antisymm hc.2 (Nat.pos_of_ne_zero hc.1.index_ne_zero))
  have hrel : ∀ r ∈ rels, FreeGroup.lift e r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hrels w hw
  set π : PresentedGroup rels →* H := PresentedGroup.toGroup hrel with hπ
  have h5 : (PresentedGroup.of 5 : PresentedGroup rels) ∈
      genSub rels (subsetOf 6 (List.range 5)) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem π h5
  rw [MonoidHom.map_closure, hπ, PresentedGroup.toGroup.of] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hx' : x.val < 5 := by simpa [subsetOf, List.mem_filter, List.mem_range] using hx
  exact ⟨⟨x.val, hx'⟩, by rw [PresentedGroup.toGroup.of]; rfl⟩

theorem evalA8_collRelA8 {H : Type*} [Group H] (e : Fin 6 → H) (k : Fin 7) :
    evalA8 e (collRelA8 k) =
      e 5 * e 1 * e 5 * (e 1)⁻¹ * e 5 * (evalA8 e (wrongWordA8 k))⁻¹ := by
  simp only [collRelA8, nWordA8, evalA8_append, evalA8_cons_true, evalA8_invA8, evalA8_nil,
    mul_one, mul_assoc]

theorem mem_closure_of_collapseCheckA8' {k : Fin 7} (hc : CollapseA8 k) {H : Type*}
    [Group H] (e : Fin 6 → H) (hN0 : ∀ r ∈ relsN0A8, evalA8 e (liftW5 r) = 1)
    (hθ : ∀ r ∈ thetaRelsA8, evalA8 e r = 1)
    (hw : e 5 * e 1 * e 5 * (e 1)⁻¹ * e 5 = evalA8 e (wrongWordA8 k)) :
    e 5 ∈ Subgroup.closure (Set.range fun i : Fin 5 => e (Fin.castSucc i)) := by
  refine mem_closure_of_collapseCheckA8 hc e fun r hr => ?_
  simp only [collRelsA8, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with (⟨w, hw', rfl⟩ | hr) | rfl
  · exact hN0 w hw'
  · exact hθ r hr
  · rw [evalA8_collRelA8, hw, mul_inv_cancel]

end CFSG.CGT.A8S
