module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsFine
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (eq_of_isComponentOf_of_perfect_le
  le_of_perfect_of_solvable_quotient fixSubgroupCongrEquiv eq_bot_or_top_of_isSubnormal')
open scoped commutatorElement

@[expose] def CompsNormal (C : Type*) [Group C] : Prop :=
  ∀ K : Subgroup C, IsComponentOf K ⊤ → K.Normal

theorem CompsNormal.of_mulEquiv {C C' : Type*} [Group C] [Group C'] (e : C ≃* C')
    (h : CompsNormal C') : CompsNormal C := by
  intro K hK
  have hK' : IsComponentOf (K.map (e : C →* C')) ⊤ := by
    have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  haveI := h _ hK'
  rw [← Subgroup.comap_map_eq_self_of_injective (f := (e : C →* C')) e.injective K]
  infer_instance

theorem compNormal_of_compsNormal {S : Type*} [Group S] {β : MulAut S}
    (h : CompsNormal ↥(fixSubgroup β)) : CompNormal β := by
  intro J hJ
  have hJ' := (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hJ.1).1 hJ
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJ.1).1 (h _ hJ')

theorem compsNormal_of_normal_quasisimple {C : Type} [Group C] [Finite C] (J : Subgroup C)
    [hJ : J.Normal] (hq : CFSG.IsQuasisimple ↥J) (hsol : Group.IsSolvable (C ⧸ J)) :
    CompsNormal C := by
  intro K hK
  have hJc : IsComponentOf J ⊤ :=
    ⟨le_top, IsSubnormal.step le_top ((Subgroup.normal_subgroupOf_iff le_top).2
      fun h k hh _ => hJ.conj_mem h hh k) (IsSubnormal.refl _),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hq⟩
  obtain rfl := eq_of_isComponentOf_of_perfect_le hJc
    (fun P _ hP => le_of_perfect_of_solvable_quotient hsol hP) hK
  exact hJ

theorem compsNormal_fixSubgroup_of_le {S : Type} [Group S] [Finite S] {β : MulAut S}
    {J : Subgroup S} (hJC : J ≤ fixSubgroup β) [(J.subgroupOf (fixSubgroup β)).Normal]
    (hJq : CFSG.IsQuasisimple ↥J)
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β))) :
    CompsNormal ↥(fixSubgroup β) :=
  compsNormal_of_normal_quasisimple (J.subgroupOf (fixSubgroup β))
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hJq) hsol

theorem compsNormal_of_isSimpleGroup {C : Type*} [Group C] [IsSimpleGroup C] : CompsNormal C := by
  intro K hK
  rcases eq_bot_or_top_of_isSubnormal' hK.2.1 with rfl | rfl <;> infer_instance

theorem compsNormal_fixSubgroup_of_derived_eq_simple {S : Type} [Group S] [Finite S]
    {δ : MulAut S} {J : Subgroup S} (hder : ⁅fixSubgroup δ, fixSubgroup δ⁆ = J)
    (hs : IsSimpleGroup J) (hnc : ∃ a b : J, a * b ≠ b * a) : CompsNormal ↥(fixSubgroup δ) := by
  have hJC : J ≤ fixSubgroup δ := by
    rw [← hder]
    exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact (fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ha hb)
        ((fixSubgroup δ).inv_mem ha)) ((fixSubgroup δ).inv_mem hb)
  haveI hJnorm : (J.subgroupOf (fixSubgroup δ)).Normal := by
    rw [← hder]
    have h := Subgroup.normal_subgroupOf_commutator_sup (fixSubgroup δ) (fixSubgroup δ)
    rwa [sup_idem] at h
  have hsol : Group.IsSolvable (↥(fixSubgroup δ) ⧸ J.subgroupOf (fixSubgroup δ)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      ← hder]
    have e : (((x * y)⁻¹ * (y * x) : ↥(fixSubgroup δ)) : S) =
        ⁅((y⁻¹ : ↥(fixSubgroup δ)) : S), ((x⁻¹ : ↥(fixSubgroup δ)) : S)⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator (y⁻¹).2 (x⁻¹).2
  exact compsNormal_fixSubgroup_of_le hJC
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc)
    hsol

theorem compsNormal_fixSubgroup_of_congr {S G : Type*} [Group S] [Group G] (e : S ≃* G)
    {β : MulAut S} (h : CompsNormal ↥(fixSubgroup (MulAut.congr e β))) :
    CompsNormal ↥(fixSubgroup β) :=
  h.of_mulEquiv (fixSubgroupCongrEquiv e β)

theorem compsNormal_fixSubgroup_of_conj {S : Type*} [Group S] (γ β : MulAut S)
    (h : CompsNormal ↥(fixSubgroup (γ * β * γ⁻¹))) : CompsNormal ↥(fixSubgroup β) := by
  have hc : MulAut.congr (γ : S ≃* S) β = γ * β * γ⁻¹ := by
    ext x
    rfl
  exact compsNormal_fixSubgroup_of_congr (γ : S ≃* S) (hc ▸ h)

theorem compsNormal_fixSubgroup_of_eq {S : Type*} [Group S] {α γ : MulAut S}
    (h : fixSubgroup α = fixSubgroup γ) (hα : CompsNormal ↥(fixSubgroup α)) :
    CompsNormal ↥(fixSubgroup γ) :=
  h ▸ hα

theorem compsNormal_fixSubgroup_inv {S : Type*} [Group S] {β : MulAut S}
    (h : CompsNormal ↥(fixSubgroup β)) : CompsNormal ↥(fixSubgroup β⁻¹) :=
  compsNormal_fixSubgroup_of_eq
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq β).symm h

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
