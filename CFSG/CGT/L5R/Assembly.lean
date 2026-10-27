module

public import CFSG.CGT.L5R.Interfaces
public import CFSG.CGT.M24R.Assembly

public section

namespace CFSG.CGT.L5R

open CFSG.CosetTable CFSG.CGT.Timmesfeld75 CFSG.CGT.M24R

variable {G : Type} [Group G] {T : Subgroup G}

theorem evalW_genTuple8_relsN8 (ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G)))
    (g : G) : ∀ r ∈ relsN8, evalW (genTuple8 ψ g) r = 1 := by
  intro r hr
  rw [relsN8_eq_map, List.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  rw [evalW_liftW10]
  have h1 : (PresentedGroup.mk {r : FreeGroup (Fin 10) | r ∈ relsN8Ten.map FreeGroup.mk}
      (FreeGroup.mk r0)) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem hr0)
  have h2 : (FreeGroup.lift (fun i : Fin 10 => genTuple8 ψ g (Fin.castSucc i)) :
      FreeGroup (Fin 10) →* G) =
      (Subgroup.normalizer (T : Set G)).subtype.comp
        (ψ.toMonoidHom.comp (PresentedGroup.mk {r : FreeGroup (Fin 10) |
          r ∈ relsN8Ten.map FreeGroup.mk})) := by
    apply FreeGroup.ext_hom
    intro i
    simp [genTuple8, PresentedGroup.mk]
    rfl
  rw [h2]
  simp [h1]

theorem sup_le_closure_genTuple8 (ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G)))
    (g : G) : Subgroup.normalizer (T : Set G) ⊔ conjSubgroup g T ≤
      Subgroup.closure (Set.range (genTuple8 ψ g)) := by
  set X := Subgroup.closure (Set.range (genTuple8 ψ g)) with hXdef
  have hN : ∀ n : ↥(Subgroup.normalizer (T : Set G)), (n : G) ∈ X := by
    intro n
    have hw : ψ.symm n ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 10 → PG 10 relsN8Ten)) := by
      rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top _
    have key : ∀ w : PG 10 relsN8Ten, w ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 10 → PG 10 relsN8Ten)) →
        ((ψ w : ↥(Subgroup.normalizer (T : Set G))) : G) ∈ X := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        refine Subgroup.subset_closure ⟨Fin.castSucc i, ?_⟩
        simp [genTuple8]
      | one => simp
      | mul x y _ _ hx hy => simpa using X.mul_mem hx hy
      | inv x _ hx => simpa using X.inv_mem hx
    simpa using key _ hw
  have hg : g ∈ X := Subgroup.subset_closure ⟨10, by simp [genTuple8]⟩
  have hT1 : conjSubgroup g T ≤ X := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h3 := X.mul_mem (X.mul_mem hg (hN ⟨_, Subgroup.le_normalizer hx⟩)) (X.inv_mem hg)
    simpa [mul_assoc] using h3
  exact sup_le (fun x hx => hN ⟨x, hx⟩) hT1

theorem genTuple8_t (ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G)
    (j : Fin 4) :
    genTuple8 ψ g ⟨6 + j.val, by omega⟩ = ((ψ (tGen8 j) : ↥(Subgroup.normalizer (T : Set G))) :
      G) := by
  have hj : 6 + j.val < 10 := by omega
  simp only [genTuple8, hj, ↓reduceDIte, tGen8]

theorem eq_closure_genTuple8_t (ψ : PG 10 relsN8Ten ≃* ↥(Subgroup.normalizer (T : Set G)))
    (g : G) (hmap : Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen8)) =
      T.subgroupOf (Subgroup.normalizer (T : Set G))) :
    T = Subgroup.closure (Set.range fun j : Fin 4 => genTuple8 ψ g ⟨6 + j.val, by omega⟩) := by
  have hT : T = (T.subgroupOf (Subgroup.normalizer (T : Set G))).map
      (Subgroup.normalizer (T : Set G)).subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr Subgroup.le_normalizer]
  rw [← hmap, Subgroup.map_map, MonoidHom.map_closure, ← Set.range_comp] at hT
  refine hT.trans (congrArg Subgroup.closure (congrArg Set.range (funext fun j => ?_)))
  exact (genTuple8_t ψ g j).symm

theorem T1ConfigL.rels_N {T₁ : Subgroup G} (c : T1ConfigL T T₁) :
    ∀ r ∈ relsN8, evalW c.gens r = 1 :=
  evalW_genTuple8_relsN8 c.ψ c.g

theorem T1ConfigL.sup_le_closure_gens {T₁ : Subgroup G} (c : T1ConfigL T T₁) :
    Subgroup.normalizer (T : Set G) ⊔ T₁ ≤ Subgroup.closure (Set.range c.gens) := by
  have h := sup_le_closure_genTuple8 c.ψ c.g
  rwa [c.conj_g] at h

theorem T1ConfigL.eq_closure_t {T₁ : Subgroup G} (c : T1ConfigL T T₁) :
    T = Subgroup.closure (Set.range fun j : Fin 4 => c.gens ⟨6 + j.val, by omega⟩) :=
  eq_closure_genTuple8_t c.ψ c.g c.map_t

theorem T1ConfigL.rels {T₁ : Subgroup G} [Finite G] (hR3 : R3StatementL)
    (hyp : L52CtxHyp T T₁) (c : T1ConfigL T T₁) : ∀ r ∈ l52Rels, evalW c.gens r = 1 := by
  intro r hr
  simp only [l52Rels, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · exact c.rels_N r hr
  · exact c.rel r hr
  · exact hR3 G T T₁ hyp c r hr

theorem exists_mulEquiv_l52_of_parts (hN8 : N8StatementL) (hL2 : N8StatementL → L2StatementL)
    (hR3 : R3StatementL) (hR5 : R5Statement) [Finite G] {T₁ : Subgroup G}
    (hyp : L52CtxHyp T T₁) :
    ∃ c : T1ConfigL T T₁,
      Subgroup.normalizer (T : Set G) ⊔ T₁ ≤ Subgroup.closure (Set.range c.gens) ∧
      ∃ φ : ↥(Subgroup.closure (Set.range c.gens)) ≃* CFSG.GroupTheory.GL52.G52,
        ∀ i, ((φ ⟨c.gens i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : CFSG.GroupTheory.GL52.G52) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) = l52M i := by
  obtain ⟨c⟩ := hL2 hN8 G T T₁ hyp
  have hle := c.sup_le_closure_gens
  have hne : Subgroup.closure (Set.range c.gens) ≠ ⊥ := by
    intro h
    have hTle : T ≤ Subgroup.closure (Set.range c.gens) :=
      (Subgroup.le_normalizer.trans le_sup_left).trans hle
    rw [h, le_bot_iff] at hTle
    have h1 := hyp.card16
    rw [hTle, Subgroup.card_bot] at h1
    omega
  obtain ⟨φ, hφ⟩ := hR5 G c.gens (c.rels hR3 hyp) hne
  exact ⟨c, hle, φ, hφ⟩

end CFSG.CGT.L5R
