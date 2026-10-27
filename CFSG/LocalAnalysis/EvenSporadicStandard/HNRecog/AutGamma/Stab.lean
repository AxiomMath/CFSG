module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

@[expose] def vertexStab (a : G) : Subgroup (Gamma a ≃g Gamma a) where
  carrier := {σ | act σ a = a}
  mul_mem' := fun {σ τ} hσ hτ => by
    show act (σ * τ) a = a
    rw [act_mul σ τ (IsConj.refl a)]
    have h1 : act τ a = a := hτ
    have h2 : act σ a = a := hσ
    rw [h1, h2]
  one_mem' := act_one a
  inv_mem' := fun {σ} hσ => by
    show act σ⁻¹ a = a
    have h2 : act σ a = a := hσ
    have := act_inv_act σ (IsConj.refl a)
    rwa [h2] at this

theorem mem_vertexStab {σ : Gamma a ≃g Gamma a} : σ ∈ vertexStab a ↔ act σ a = a := Iff.rfl

theorem gammaConj_mem_vertexStab_iff (g : G) : gammaConj a g ∈ vertexStab a ↔ g ∈ Gx a := by
  rw [mem_vertexStab, act_gammaConj g (IsConj.refl a), mem_Gx]
  constructor
  · intro h
    calc a * g = (g * a * g⁻¹) * g := by rw [h]
      _ = g * a := by group
  · intro h
    calc g * a * g⁻¹ = (a * g) * g⁻¹ := by rw [h]
      _ = a := by group

theorem range_sup_vertexStab : (gammaConj a).range ⊔ vertexStab a = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_act σ (IsConj.refl a))
  have hτ : (gammaConj a g)⁻¹ * σ ∈ vertexStab a := by
    rw [mem_vertexStab, act_mul _ _ (IsConj.refl a), ← map_inv,
      act_gammaConj g⁻¹ (isConj_act σ (IsConj.refl a)), ← hg]
    group
  have : σ = gammaConj a g * ((gammaConj a g)⁻¹ * σ) := by group
  rw [this]
  exact Subgroup.mul_mem_sup ⟨g, rfl⟩ hτ

@[expose] def gxToStab (a : G) :
    ↥(Gx a) →* ↥((gammaConj a).range.subgroupOf (vertexStab a)) where
  toFun g := ⟨⟨gammaConj a g, (gammaConj_mem_vertexStab_iff g.1).2 g.2⟩, ⟨g.1, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' := fun g h => Subtype.ext (Subtype.ext (map_mul _ _ _))

noncomputable def gxEquivSubgroupOf (hinj : Function.Injective (gammaConj a)) :
    ↥(Gx a) ≃* ↥((gammaConj a).range.subgroupOf (vertexStab a)) := by
  refine MulEquiv.ofBijective (gxToStab a) ⟨?_, ?_⟩
  · intro g h hgh
    have := congrArg (fun x : ↥((gammaConj a).range.subgroupOf (vertexStab a)) =>
      ((x : vertexStab a) : Gamma a ≃g Gamma a)) hgh
    exact Subtype.ext (hinj this)
  · rintro ⟨⟨σ, hσB⟩, hσA⟩
    obtain ⟨g, hg⟩ : σ ∈ (gammaConj a).range := hσA
    refine ⟨⟨g, (gammaConj_mem_vertexStab_iff g).1 (by rw [hg]; exact hσB)⟩, ?_⟩
    exact Subtype.ext (Subtype.ext hg)

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
