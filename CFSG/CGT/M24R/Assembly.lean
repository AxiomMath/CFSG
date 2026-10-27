module

public import CFSG.CGT.M24R.Interfaces

public section

namespace CFSG.CGT.M24R

open CFSG.CosetTable CFSG.CGT.Timmesfeld75

theorem evalW_liftW10 {H : Type*} [Group H] (e : Fin 11 → H) (w : List (Fin 10 × Bool)) :
    evalW e (liftW10 w) = FreeGroup.lift (fun i : Fin 10 => e (Fin.castSucc i))
      (FreeGroup.mk w) := by
  rw [evalW, FreeGroup.lift_mk, FreeGroup.lift_mk, liftW10, List.map_map]
  rfl

theorem T1Config8.rels_N {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1Config8 T T₁) :
    ∀ r ∈ relsN8, evalW c.gens r = 1 := by
  intro r hr
  rw [relsN8_eq_map, List.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  rw [evalW_liftW10]
  have h1 : (PresentedGroup.mk {r : FreeGroup (Fin 10) | r ∈ relsN8Ten.map FreeGroup.mk}
      (FreeGroup.mk r0)) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem hr0)
  have h2 : (FreeGroup.lift (fun i : Fin 10 => c.gens (Fin.castSucc i)) :
      FreeGroup (Fin 10) →* G) =
      (Subgroup.normalizer (T : Set G)).subtype.comp
        (c.ψ.toMonoidHom.comp (PresentedGroup.mk {r : FreeGroup (Fin 10) |
          r ∈ relsN8Ten.map FreeGroup.mk})) := by
    apply FreeGroup.ext_hom
    intro i
    simp [T1Config8.gens, genTuple8, PresentedGroup.mk]
    rfl
  rw [h2]
  simp [h1]

theorem T1Config8.sup_le_closure_gens {G : Type} [Group G] {T T₁ : Subgroup G}
    (c : T1Config8 T T₁) :
    Subgroup.normalizer (T : Set G) ⊔ T₁ ≤ Subgroup.closure (Set.range c.gens) := by
  have hN : ∀ n : ↥(Subgroup.normalizer (T : Set G)),
      (n : G) ∈ Subgroup.closure (Set.range c.gens) := by
    intro n
    have hw : c.ψ.symm n ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 10 → PG 10 relsN8Ten)) := by
      rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top _
    have key : ∀ w : PG 10 relsN8Ten, w ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 10 → PG 10 relsN8Ten)) →
        ((c.ψ w : ↥(Subgroup.normalizer (T : Set G))) : G) ∈
          Subgroup.closure (Set.range c.gens) := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        refine Subgroup.subset_closure ⟨Fin.castSucc i, ?_⟩
        simp [T1Config8.gens, genTuple8]
      | one => simp
      | mul x y _ _ hx hy =>
        simpa using (Subgroup.closure (Set.range c.gens)).mul_mem hx hy
      | inv x _ hx => simpa using (Subgroup.closure (Set.range c.gens)).inv_mem hx
    have := key _ hw
    simpa using this
  have hg : c.g ∈ Subgroup.closure (Set.range c.gens) :=
    Subgroup.subset_closure ⟨10, by simp [T1Config8.gens, genTuple8]⟩
  have hT1 : T₁ ≤ Subgroup.closure (Set.range c.gens) := by
    intro x hx
    rw [← c.conj_g, mem_conjSubgroup] at hx
    have hT : c.g⁻¹ * x * c.g ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer hx
    have := hN ⟨_, hT⟩
    have h3 := (Subgroup.closure (Set.range c.gens)).mul_mem
      ((Subgroup.closure (Set.range c.gens)).mul_mem hg this)
      ((Subgroup.closure (Set.range c.gens)).inv_mem hg)
    simpa [mul_assoc] using h3
  have hNle : Subgroup.normalizer (T : Set G) ≤ Subgroup.closure (Set.range c.gens) :=
    fun x hx => hN ⟨x, hx⟩
  exact sup_le hNle hT1

theorem exists_mulEquiv_m24_of_parts (hN8 : N8Statement) (hL2 : N8Statement → L2Statement8)
    (hR3 : R3Statement) (hR24 : R24Statement) {G : Type} [Group G] [Finite G]
    {T T₁ : Subgroup G} (hyp : M24CtxHyp T T₁) :
    ∃ X : Subgroup G, Subgroup.normalizer (T : Set G) ⊔ T₁ ≤ X ∧
      Nonempty (↥X ≃* CFSG.Blueprint.NativeSporadic.M24) := by
  obtain ⟨c⟩ := hL2 hN8 G T T₁ hyp
  have hall : ∀ r ∈ m24Rels, evalW c.gens r = 1 := by
    intro r hr
    simp only [m24Rels, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact c.rels_N r hr
    · exact c.rel r hr
    · exact hR3 G T T₁ hyp c r hr
  have hle := c.sup_le_closure_gens
  have hne : Subgroup.closure (Set.range c.gens) ≠ ⊥ := by
    intro h
    have hTle : T ≤ Subgroup.closure (Set.range c.gens) :=
      (Subgroup.le_normalizer.trans le_sup_left).trans hle
    rw [h, le_bot_iff] at hTle
    have h1 := hyp.card16
    rw [hTle, Subgroup.card_bot] at h1
    omega
  exact ⟨_, hle, hR24 G c.gens hall hne⟩

end CFSG.CGT.M24R
