module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.Open.GeneralizedFittingSelfCentralizing

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

attribute [local instance] CFSG.LocalCores.layer_characteristic

theorem genFittingLayer_eq_layer' (G : Type*) [Group G] :
    CFSG.Open.genFittingLayer G = CFSG.layer G := by
  rw [CFSG.Open.genFittingLayer.eq_sSup, CFSG.layer.eq_sSup]
  congr 1
  ext L
  exact (CFSG.isComponent_iff_open L).symm

theorem subsingleton_of_noAbel_of_layer_eq_bot {C : Type} [Group C] [Finite C]
    (hA : ∀ N : Subgroup C, N.Normal → (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → N = ⊥)
    (hL : CFSG.layer C = ⊥) : (⊤ : Subgroup C) = ⊥ := by
  have hF : CFSG.fittingSubgroup C = ⊥ := by
    by_contra hne
    set F := CFSG.fittingSubgroup C with hFdef
    haveI hFnil : Group.IsNilpotent ↥F := inferInstance
    haveI : Nontrivial ↥F := (Subgroup.nontrivial_iff_ne_bot F).2 hne
    have hcen : Subgroup.center ↥F ≠ ⊥ := Group.IsNilpotent.center_ne_bot ↥F
    haveI : Nontrivial ↥(Subgroup.center ↥F) := (Subgroup.nontrivial_iff_ne_bot _).2 hcen
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥F))
    have hFn : F.Normal := inferInstance
    have hZ : F ⊓ Subgroup.centralizer (F : Set C) = ⊥ := by
      have hnorm : (F ⊓ Subgroup.centralizer (F : Set C)).Normal :=
        ⟨fun x hx g => ⟨hFn.conj_mem x hx.1 g, by
          refine Subgroup.mem_centralizer_iff.2 fun f hf => ?_
          have h1 : g⁻¹ * f * g ∈ F := by
            simpa using hFn.conj_mem f hf g⁻¹
          have h2 := Subgroup.mem_centralizer_iff.1 hx.2 _ h1
          calc f * (g * x * g⁻¹) = g * ((g⁻¹ * f * g) * x) * g⁻¹ := by group
            _ = g * (x * (g⁻¹ * f * g)) * g⁻¹ := by rw [h2]
            _ = g * x * g⁻¹ * f := by group⟩⟩
      refine hA _ hnorm fun x hx y hy => ?_
      exact (Subgroup.mem_centralizer_iff.1 hy.2 x hx.1)
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    have hmem : (z.1 : C) ∈ F ⊓ Subgroup.centralizer (F : Set C) := by
      refine ⟨z.1.2, Subgroup.mem_centralizer_iff.2 fun f hf => ?_⟩
      have := Subgroup.mem_center_iff.1 z.2 ⟨f, hf⟩
      exact congrArg Subtype.val this
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hstar : CFSG.Open.genFittingFStar C = ⊥ := by
    rw [CFSG.Open.genFittingFStar.eq_sup, genFittingLayer_eq_layer', hL]
    show CFSG.fittingSubgroup C ⊔ ⊥ = ⊥
    rw [hF, sup_bot_eq]
  have hc := CFSG.Open.Open.generalized_fitting_self_centralizing C
  rw [hstar] at hc
  rw [eq_bot_iff]
  intro x _
  exact hc (by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := by simpa using hy
    rw [hy1]
    simp)


theorem perfectInLayer_of_noAbel_of_solvable_quotient {S : Type} [Group S] (β : MulAut S)
    [Finite ↥(fixSubgroup β)]
    (hA : ∀ N : Subgroup ↥(fixSubgroup β), N.Normal → (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) →
      N = ⊥)
    (hT : ∀ (N : Subgroup ↥(fixSubgroup β)) [N.Normal],
      N = ⊥ ∨ Group.IsSolvable (↥(fixSubgroup β) ⧸ N)) : PerfectInLayer β := by
  apply perfectInLayer_of_isSolvable_layer_quotient
  rcases hT (CFSG.layer ↥(fixSubgroup β)) with hL | hs
  · have htop := subsingleton_of_noAbel_of_layer_eq_bot hA hL
    haveI : Subsingleton ↥(fixSubgroup β) :=
      ⟨fun a b => by
        have ha : a ∈ (⊥ : Subgroup ↥(fixSubgroup β)) := htop ▸ Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup ↥(fixSubgroup β)) := htop ▸ Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]⟩
    haveI : Subsingleton (↥(fixSubgroup β) ⧸ CFSG.layer ↥(fixSubgroup β)) :=
      ⟨fun a b => by
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        rw [Subsingleton.elim a' b']⟩
    infer_instance
  · exact hs

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
