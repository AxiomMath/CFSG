module

public import CFSG.CGT.M24R.R3Config

public section

namespace CFSG.CGT.M24R.R3

open CFSG.CosetTable CFSG.CGT.Timmesfeld75

abbrev Collapse8 (i : Fin 16) : Prop :=
  (genSub {r : FreeGroup (Fin 11) | r ∈ (relsN8 ++ thetaRels8 ++ [collRel i]).map FreeGroup.mk}
      (subsetOf 11 (List.range 10))).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 11) | r ∈ (relsN8 ++ thetaRels8 ++ [collRel i]).map FreeGroup.mk}
      (subsetOf 11 (List.range 10))).index ≤ 1

theorem mem_closure_of_collapse {i : Fin 16} (hc : Collapse8 i) {H : Type*} [Group H]
    (e : Fin 11 → H) (hrels : ∀ r ∈ relsN8 ++ thetaRels8 ++ [collRel i], evalW e r = 1) :
    e letG ∈ Subgroup.closure (Set.range fun k : Fin 10 => e (Fin.castSucc k)) := by
  set rels := {r : FreeGroup (Fin 11) | r ∈ (relsN8 ++ thetaRels8 ++ [collRel i]).map FreeGroup.mk}
  have htop : genSub rels (subsetOf 11 (List.range 10)) = ⊤ :=
    Subgroup.index_eq_one.mp (Nat.le_antisymm hc.2 (Nat.pos_of_ne_zero hc.1.index_ne_zero))
  have hrel : ∀ r ∈ rels, FreeGroup.lift e r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hrels w hw
  set π : PresentedGroup rels →* H := PresentedGroup.toGroup hrel with hπ
  have hg : (PresentedGroup.of letG : PresentedGroup rels) ∈
      genSub rels (subsetOf 11 (List.range 10)) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem π hg
  rw [MonoidHom.map_closure, hπ, PresentedGroup.toGroup.of] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hx' : x.val < 10 := by simpa [subsetOf, List.mem_filter, List.mem_range] using hx
  exact ⟨⟨x.val, hx'⟩, by rw [PresentedGroup.toGroup.of]; rfl⟩

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem g_mem_normalizer_of_collapse (c : T1Config8 T T₁) {i : Fin 16}
    (hc : Collapse8 i) (hR : evalW c.gens (collRel i) = 1) :
    c.g ∈ Subgroup.normalizer (T : Set G) := by
  have key := mem_closure_of_collapse hc c.gens fun r hr => by
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | hr) | rfl
    · exact c.rels_N r hr
    · exact c.rel r hr
    · exact hR
  rw [gens_letG] at key
  refine Subgroup.closure_le _ |>.2 ?_ key
  rintro _ ⟨k, rfl⟩
  simp only [T1Config8.gens, genTuple8, Fin.val_castSucc, k.isLt, dite_true]
  exact (c.ψ _).2

theorem g_not_mem_normalizer (hyp : M24CtxHyp T T₁) (c : T1Config8 T T₁) :
    c.g ∉ Subgroup.normalizer (T : Set G) := by
  intro hg
  have hT : conjSubgroup c.g T = T := by
    ext x
    rw [mem_conjSubgroup, Subgroup.mem_normalizer_iff.1 hg]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  have hbot : T = ⊥ := by
    have h := hyp.inf_bot
    rw [← c.conj_g, hT, inf_idem] at h
    exact h
  have h16 := hyp.card16
  rw [hbot, Subgroup.card_bot] at h16
  omega

theorem not_collapse (hyp : M24CtxHyp T T₁) (c : T1Config8 T T₁) {i : Fin 16}
    (hc : Collapse8 i) : evalW c.gens (collRel i) ≠ 1 := fun hR =>
  g_not_mem_normalizer hyp c (g_mem_normalizer_of_collapse c hc hR)

end CFSG.CGT.M24R.R3
