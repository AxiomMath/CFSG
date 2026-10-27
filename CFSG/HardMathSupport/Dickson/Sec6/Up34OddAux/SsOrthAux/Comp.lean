module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.SsOrth

open CFSG Subgroup
open CFSG.ComponentClassification.CatLeafProof (isComponent_map_subtype_of_normal)

section Dichotomy

variable {G : Type*} [Group G]

theorem exists_le_of_isComponent_of_normal_iSup [Finite G] {M : Subgroup G} {ι : Type*}
    (B : ι → Subgroup G) (hBM : ∀ i, B i ≤ M) (hn : ∀ i, ((B i).subgroupOf M).Normal)
    (hsup : ⨆ i, B i = M) {L : Subgroup G} (hLM : L ≤ M)
    (hL : CFSG.IsComponent (L.subgroupOf M)) : ∃ i, L ≤ B i := by
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ i, ⁅L.subgroupOf M, (B i).subgroupOf M⁆ = ⊥ := fun i =>
    (CFSG.LocalCores.component_normal_subgroup hL (hn i)).resolve_left fun h =>
      hcon i fun g hg => (show (⟨g, hLM hg⟩ : ↥M) ∈ (B i).subgroupOf M from h hg)
  have htop : ⨆ i, (B i).subgroupOf M = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp_rw [Subgroup.map_subgroupOf_eq_of_le (hBM _)]
    exact hsup
  have hab : ∀ a ∈ L.subgroupOf M, ∀ b ∈ L.subgroupOf M, a * b = b * a := by
    intro a ha b _
    have hb' : b ∈ ⨆ i, (B i).subgroupOf M := by rw [htop]; trivial
    refine Subgroup.iSup_induction (fun i => (B i).subgroupOf M) (C := fun y => a * y = y * a)
      hb' (fun i y hy => ?_) (by simp) (fun y z hy hz => ?_)
    · have h1 := Subgroup.commutator_mem_commutator ha hy
      rw [hcomm i, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
  obtain ⟨-, -, a, b, hab'⟩ := hL.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine hab' ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hab a a.2 b b.2)

theorem exists_isComponent_of_normal {M H : Subgroup G} (hHM : H ≤ M) (hn : (H.subgroupOf M).Normal)
    {M₁ : Subgroup ↥H} (hM₁ : CFSG.IsComponent M₁) :
    ∃ L : Subgroup G, L ≤ M ∧ CFSG.IsComponent (L.subgroupOf M) ∧
      Nonempty (↥M₁ ⧸ Subgroup.center ↥M₁ ≃* ↥L ⧸ Subgroup.center ↥L) := by
  set N : Subgroup ↥M := H.subgroupOf M
  haveI : N.Normal := hn
  let e : ↥H ≃* ↥N := (Subgroup.subgroupOfEquivOfLe hHM).symm
  have h2 : CFSG.IsComponent (M₁.map e.toMonoidHom) := CFSG.LocalCores.isComponent_map_mulEquiv e hM₁
  have h3 : CFSG.IsComponent ((M₁.map e.toMonoidHom).map N.subtype) :=
    isComponent_map_subtype_of_normal h2
  refine ⟨((M₁.map e.toMonoidHom).map N.subtype).map M.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hsub : (((M₁.map e.toMonoidHom).map N.subtype).map M.subtype).subgroupOf M =
        (M₁.map e.toMonoidHom).map N.subtype :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [hsub]
    exact h3
  · let e1 := M₁.equivMapOfInjective e.toMonoidHom e.injective
    let e2 := (M₁.map e.toMonoidHom).equivMapOfInjective N.subtype N.subtype_injective
    let e3 := ((M₁.map e.toMonoidHom).map N.subtype).equivMapOfInjective M.subtype
      M.subtype_injective
    let ef := e1.trans (e2.trans e3)
    exact ⟨QuotientGroup.congr _ _ ef (Subgroup.map_center_eq ef)⟩

theorem isComponent_subgroupOf_of_open {N I : Subgroup G} (hI : CFSG.Open.IsComponentOf I N) :
    CFSG.IsComponent (I.subgroupOf N) :=
  (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hI.1).1
    (CFSG.Assembly.isComponentOf_iff_open.2 hI)

end Dichotomy

end CFSG.HardMathSupport.Dickson.Sec6.SsOrth
