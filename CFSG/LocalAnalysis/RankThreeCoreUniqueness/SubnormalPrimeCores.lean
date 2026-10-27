module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ReducedCentralizerObstruction

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem pCoreOf_le_of_normal_subgroupOf
    {G : Type*} [Group G] (prime : ℕ) (subgroup overgroup : Subgroup G)
    (hbound : subgroup ≤ overgroup) (hnormal : (subgroup.subgroupOf overgroup).Normal) :
    pCoreOf prime subgroup ≤ pCoreOf prime overgroup := by
  have hinternal := normal_subgroup_pCore_le prime (subgroup.subgroupOf overgroup) hnormal
  have hmapped := Subgroup.map_mono (f := overgroup.subtype) hinternal
  change (pCoreOf prime (subgroup.subgroupOf overgroup)).map overgroup.subtype ≤
    pCoreOf prime overgroup at hmapped
  rwa [pCoreOf_map_subtype, Subgroup.map_subgroupOf_eq_of_le hbound] at hmapped

theorem cfsg_subnormal_pCoreOf_le
    {G : Type*} [Group G] (prime : ℕ) {subgroup overgroup : Subgroup G}
    (hsubnormal : IsSubnormal subgroup overgroup) :
    pCoreOf prime subgroup ≤ pCoreOf prime overgroup := by
  induction hsubnormal with
  | refl subgroup => exact le_rfl
  | @step subgroup intermediate overgroup hbound hnormal _hchain inductionHypothesis =>
    exact (pCoreOf_le_of_normal_subgroupOf prime subgroup intermediate hbound hnormal).trans
      inductionHypothesis

theorem pCoreOf_top_eq_pCore
    {G : Type*} [Group G] (prime : ℕ) :
    pCoreOf prime (⊤ : Subgroup G) = pCore prime G :=
  pCore_map_mulEquiv prime (Subgroup.topEquiv (G := G))

theorem cfsg_subnormal_internal_pCore_le_center_of_core_centralizing
    {G : Type*} [Group G] (prime : ℕ) (subgroup : Subgroup G)
    (hsubnormal : IsSubnormal subgroup ⊤)
    (hcentralizes : subgroup ≤ Subgroup.centralizer (pCore prime G : Set G)) :
    pCore prime subgroup ≤ Subgroup.center subgroup := by
  have hcoreLe := cfsg_subnormal_pCoreOf_le prime hsubnormal
  rw [pCoreOf_top_eq_pCore] at hcoreLe
  intro element helement
  have hambient : element.val ∈ pCore prime G :=
    hcoreLe (Subgroup.mem_map_of_mem subgroup.subtype helement)
  apply Subgroup.mem_center_iff.mpr
  intro other
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp (hcentralizes other.property)
    element.val hambient).symm

theorem primeComplementCore_map_mulEquiv_le
    {G Image : Type*} [Group G] [Finite G] [Group Image] [Finite Image]
    (prime : ℕ) (equivalence : G ≃* Image) :
    Subgroup.map equivalence.toMonoidHom (primeComplementCore prime) ≤
      primeComplementCore prime :=
  normal_coprime_le_primeComplementCore prime _
    ((primeComplementCore_normal prime).map equivalence.toMonoidHom equivalence.surjective)
    ((primeComplementCore_coprime prime).of_dvd_right
      ((primeComplementCore prime).card_map_dvd equivalence.toMonoidHom))

theorem primeComplementCore_map_mulEquiv
    {G Image : Type*} [Group G] [Finite G] [Group Image] [Finite Image]
    (prime : ℕ) (equivalence : G ≃* Image) :
    Subgroup.map equivalence.toMonoidHom (primeComplementCore prime) =
      primeComplementCore prime := by
  apply le_antisymm (primeComplementCore_map_mulEquiv_le prime equivalence)
  have hreverse := Subgroup.map_mono (f := equivalence.toMonoidHom)
    (primeComplementCore_map_mulEquiv_le prime equivalence.symm)
  have hcomp : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom =
      MonoidHom.id Image := by
    ext element
    exact equivalence.apply_symm_apply element
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at hreverse

@[expose] def primeComplementCoreOf {G : Type*} [Group G] (prime : ℕ) (subgroup : Subgroup G) :
    Subgroup G :=
  Subgroup.map subgroup.subtype (primeComplementCore prime)

theorem primeComplementCoreOf_map_subtype
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (overgroup : Subgroup G)
    (subgroup : Subgroup overgroup) :
    Subgroup.map overgroup.subtype (primeComplementCoreOf prime subgroup) =
      primeComplementCoreOf prime (Subgroup.map overgroup.subtype subgroup) := by
  let equivalence := subgroup.equivMapOfInjective overgroup.subtype overgroup.subtype_injective
  have hhom : (Subgroup.map overgroup.subtype subgroup).subtype.comp equivalence.toMonoidHom =
      overgroup.subtype.comp subgroup.subtype := by
    ext element
    rfl
  unfold primeComplementCoreOf
  rw [← primeComplementCore_map_mulEquiv prime equivalence,
    Subgroup.map_map, Subgroup.map_map, hhom]

theorem primeComplementCoreOf_le_of_normal_subgroupOf
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (subgroup overgroup : Subgroup G)
    (hbound : subgroup ≤ overgroup) (hnormal : (subgroup.subgroupOf overgroup).Normal) :
    primeComplementCoreOf prime subgroup ≤ primeComplementCoreOf prime overgroup := by
  have hinternal := normal_subgroup_primeComplementCore_le prime
    (subgroup.subgroupOf overgroup) hnormal
  have hmapped := Subgroup.map_mono (f := overgroup.subtype) hinternal
  change (primeComplementCoreOf prime (subgroup.subgroupOf overgroup)).map overgroup.subtype ≤
    primeComplementCoreOf prime overgroup at hmapped
  rwa [primeComplementCoreOf_map_subtype,
    Subgroup.map_subgroupOf_eq_of_le hbound] at hmapped

theorem cfsg_subnormal_primeComplementCoreOf_le
    {G : Type*} [Group G] [Finite G] (prime : ℕ) {subgroup overgroup : Subgroup G}
    (hsubnormal : IsSubnormal subgroup overgroup) :
    primeComplementCoreOf prime subgroup ≤ primeComplementCoreOf prime overgroup := by
  induction hsubnormal with
  | refl subgroup => exact le_rfl
  | @step subgroup intermediate overgroup hbound hnormal _hchain inductionHypothesis =>
    exact (primeComplementCoreOf_le_of_normal_subgroupOf
      prime subgroup intermediate hbound hnormal).trans inductionHypothesis

theorem primeComplementCoreOf_top_eq_primeComplementCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    primeComplementCoreOf prime (⊤ : Subgroup G) = primeComplementCore prime :=
  primeComplementCore_map_mulEquiv prime (Subgroup.topEquiv (G := G))

theorem cfsg_subnormal_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (subgroup : Subgroup G)
    (hsubnormal : IsSubnormal subgroup ⊤)
    (hcore : primeComplementCore (G := G) prime = ⊥) :
    primeComplementCore (G := subgroup) prime = ⊥ := by
  have hbound := cfsg_subnormal_primeComplementCoreOf_le prime hsubnormal
  rw [primeComplementCoreOf_top_eq_primeComplementCore, hcore] at hbound
  exact (Subgroup.map_eq_bot_iff_of_injective _ subgroup.subtype_injective).mp
    (le_bot_iff.mp hbound)

end CFSG.RankThreeCoreUniqueness.Helpers
