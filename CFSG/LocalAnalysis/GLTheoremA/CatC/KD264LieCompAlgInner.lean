module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def CompAlgAtWith (S : Type) [Group S] (R : MulAut S → MulAut S → Prop) : Prop :=
  ∀ β : MulAut S, β ∈ innAutDerived S → β ^ 3 = 1 → β ≠ 1 →
    ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) →
      ∀ e : TauCeti.ValidLieTypeIndex,
        (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) →
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie e).Group) →
        ∀ x ∈ innAutDerived S, x ^ 3 = 1 → β * x = x * β → R β x →
          ∀ hx : x ∈ CFSG.GroupActions.subgroupStabAut K,
            centerQuotientHom ↥K (CFSG.GroupActions.subgroupStabRestrict K ⟨x, hx⟩) ∈
              innAutDerived (↥K ⧸ Subgroup.center ↥K)

@[expose] def CompAlgInnerAt (S : Type) [Group S] : Prop :=
  CompAlgAtWith S (fun β x => β ∈ inner S ∧ x ∈ inner S)

@[expose] def CompAlgOuterAt (S : Type) [Group S] : Prop :=
  CompAlgAtWith S (fun β x => ¬ (β ∈ inner S ∧ x ∈ inner S))

theorem compAlgAt_of_inner_of_outer {S : Type} [Group S] (hI : CompAlgInnerAt S)
    (hO : CompAlgOuterAt S) : CompAlgAt S := by
  intro β hβmem hβ3 hβ1 K hK idx hidx hKiso x hxmem hx3 hβx hxstab
  by_cases hinn : β ∈ inner S ∧ x ∈ inner S
  · exact hI β hβmem hβ3 hβ1 K hK idx hidx hKiso x hxmem hx3 hβx hinn hxstab
  · exact hO β hβmem hβ3 hβ1 K hK idx hidx hKiso x hxmem hx3 hβx hinn hxstab

theorem compAlgAt_of_inner {S : Type} [Group S]
    (hS : ∀ β ∈ innAutDerived S, β ^ 3 = 1 → β ∈ inner S) (h : CompAlgInnerAt S) :
    CompAlgAt S := by
  intro β hβmem hβ3 hβ1 K hK idx hidx hKiso x hxmem hx3 hβx hxstab
  exact h β hβmem hβ3 hβ1 K hK idx hidx hKiso x hxmem hx3 hβx
    ⟨hS β hβmem hβ3, hS x hxmem hx3⟩ hxstab

theorem compAlgAtWith_of_mulEquiv {S S' : Type} [Group S] [Group S']
    {R : MulAut S → MulAut S → Prop} {R' : MulAut S' → MulAut S' → Prop} (e : S ≃* S')
    (hR : ∀ β x, R' (MulAut.congr e β) (MulAut.congr e x) → R β x)
    (h : CompAlgAtWith S R) : CompAlgAtWith S' R' := by
  intro b hbmem hb3 hb1 K' hK' idx hidx hK'iso x' hx'mem hx'3 hbx' hR' hx'stab
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ innAutDerived S := by
    rw [← mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hα3 : α ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hb3
  have hα1 : α ≠ 1 := by
    intro h1
    apply hb1
    rw [← hconj, h1, map_one]
  set K : Subgroup S := K'.map (e.symm : S' →* S) with hK
  have hfix : (fixSubgroup b).map (e.symm : S' →* S) = fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hKcomp : IsComponentOf K (fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  have hKmap : K.map (e : S →* S') = K' := by
    rw [hK, Subgroup.map_map]
    simp
  let ε : ↥K ≃* ↥K' :=
    (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
  have hKiso : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie idx).Group) := by
    obtain ⟨φ⟩ := hK'iso
    exact ⟨(QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K') ε
      (Subgroup.map_center_eq ε)).trans φ⟩
  set ξ : MulAut S := MulAut.congr e.symm x' with hξ
  have hconjξ : MulAut.congr e ξ = x' := by
    rw [hξ]
    ext y
    simp [MulAut.congr_apply]
  have hξmem : ξ ∈ innAutDerived S := by
    rw [← mem_innAutDerived_congr e, hconjξ]
    exact hx'mem
  have hξ3 : ξ ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconjξ]
    exact hx'3
  have hbξ : α * ξ = ξ * α := by
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, hconj, hconjξ]
    exact hbx'
  have hξstab : ξ ∈ CFSG.GroupActions.subgroupStabAut K := by
    change K.map ξ.toMonoidHom = K
    rw [hK, Subgroup.map_map]
    have hcomp : ξ.toMonoidHom.comp (e.symm : S' →* S) =
        (e.symm : S' →* S).comp x'.toMonoidHom := by
      ext s'
      simp [hξ, MulAut.congr_apply]
    rw [hcomp, ← Subgroup.map_map, hx'stab]
  have hRαξ : R α ξ := hR α ξ (by rw [hconj, hconjξ]; exact hR')
  have hres := h α hαmem hα3 hα1 K hKcomp idx hidx hKiso ξ hξmem hξ3 hbξ hRαξ hξstab
  have hα' : MulAut.congr ε (CFSG.GroupActions.subgroupStabRestrict K ⟨ξ, hξstab⟩) =
      CFSG.GroupActions.subgroupStabRestrict K' ⟨x', hx'stab⟩ := by
    ext k'
    obtain ⟨k, rfl⟩ : ∃ k, ε k = k' := ⟨ε.symm k', ε.apply_symm_apply k'⟩
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    simp [ε, Subgroup.coe_equivMapOfInjective_apply, MulEquiv.subgroupCongr_apply,
      CFSG.GroupActions.subgroupStabRestrict_apply, hξ, MulAut.congr_apply]
  have hnat := centerQuotientHom_congr ε (CFSG.GroupActions.subgroupStabRestrict K ⟨ξ, hξstab⟩)
  rw [hα'] at hnat
  rw [← hnat]
  exact (mem_innAutDerived_congr (QuotientGroup.congr (Subgroup.center ↥K)
    (Subgroup.center ↥K') ε (Subgroup.map_center_eq ε))).2 hres

theorem compAlgInnerAt_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : CompAlgInnerAt S) : CompAlgInnerAt S' := by
  refine compAlgAtWith_of_mulEquiv e ?_ h
  intro β x hβx
  exact ⟨(congr_mem_inner_iff e β).1 hβx.1, (congr_mem_inner_iff e x).1 hβx.2⟩

theorem compAlgOuterAt_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : CompAlgOuterAt S) : CompAlgOuterAt S' := by
  refine compAlgAtWith_of_mulEquiv e ?_ h
  intro β x hβx hβx'
  exact hβx ⟨(congr_mem_inner_iff e β).2 hβx'.1, (congr_mem_inner_iff e x).2 hβx'.2⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
