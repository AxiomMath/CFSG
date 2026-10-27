module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.NormalTwoGroupPerm

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def predStab (p : ι → Prop) : Subgroup (Perm ι) where
  carrier := {π | ∀ i, p i ↔ p (π i)}
  mul_mem' := by
    intro a b ha hb i
    exact (hb i).trans (ha (b i))
  one_mem' := fun _ => Iff.rfl
  inv_mem' := by
    intro a ha i
    have := ha (a⁻¹ i)
    simp at this
    exact this.symm

@[expose] noncomputable def resPred (p : ι → Prop) : ↥(predStab p) →* Perm {i // p i} where
  toFun π := (π.1).subtypePerm (fun x => (π.2 x).symm)
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl

theorem resPred_surjective (p : ι → Prop) [DecidablePred p] : Function.Surjective (resPred p) := by
  intro τ
  have hmem : (Equiv.Perm.ofSubtype τ) ∈ predStab p := by
    intro i
    by_cases h : p i
    · rw [Equiv.Perm.ofSubtype_apply_of_mem τ h]
      exact ⟨fun _ => (τ ⟨i, h⟩).2, fun _ => h⟩
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem τ h]
  refine ⟨⟨_, hmem⟩, ?_⟩
  ext ⟨i, hi⟩
  show ((Equiv.Perm.ofSubtype τ) i) = (τ ⟨i, hi⟩ : ι)
  exact Equiv.Perm.ofSubtype_apply_of_mem τ hi

theorem eq_one_of_normal_isPGroup_pred (p : ι → Prop) [DecidablePred p]
    (hp : Fintype.card {i // p i} ≠ 2 ∧ Fintype.card {i // p i} ≠ 4)
    {Q : Subgroup (Perm ι)} (hQp : IsPGroup 2 Q) (hQs : Q ≤ predStab p)
    (hQn : ∀ σ ∈ predStab p, ∀ q ∈ Q, σ * q * σ⁻¹ ∈ Q) :
    ∀ q ∈ Q, ∀ i, p i → q i = i := by
  classical
  set Q' : Subgroup ↥(predStab p) := Q.subgroupOf (predStab p) with hQ'
  have hQ'n : Q'.Normal := ⟨fun q hq σ => Subgroup.mem_subgroupOf.2
    (hQn σ.1 σ.2 q.1 (Subgroup.mem_subgroupOf.1 hq))⟩
  have hQ'p : IsPGroup 2 Q' := hQp.comap_of_injective _ (predStab p).subtype_injective
  have hR : (Q'.map (resPred p)).Normal := hQ'n.map _ (resPred_surjective p)
  have hRp : IsPGroup 2 (Q'.map (resPred p)) := hQ'p.map _
  have hbot := normal_isPGroup_perm_eq_bot_of_card hp.1 hp.2 hR hRp
  intro q hq i hi
  have hm : resPred p ⟨q, hQs hq⟩ ∈ Q'.map (resPred p) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hq)
  rw [hbot, Subgroup.mem_bot] at hm
  have := congrArg (fun f => (f ⟨i, hi⟩ : ι)) hm
  simpa [resPred] using this

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
