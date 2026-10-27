module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Factors

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

variable {C C' : Type} [Group C] [Group C'] [Finite C] [Finite C'] {Q : Subgroup C}
  {Q' : Subgroup C'} [Q.Normal] [Q'.Normal]

theorem AschbacherHyp.map_mem_of_mem (hC : AschbacherHyp C Q) (hC' : AschbacherHyp C' Q')
    (α : ↥(commutator C) ≃* ↥(commutator C')) {l : ↥(commutator C)} (hl : (l : C) ∈ Q) :
    ((α l : ↥(commutator C')) : C') ∈ Q' := by
  haveI : Finite Q := hC.plus.finite
  haveI : Finite Q' := hC'.plus.finite
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hC.plus.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q')) :=
    CFSG.GroupTheory.extraspecialQuotientModule hC'.plus.isExtraspecialPGroup
  obtain ⟨θ, -, hθsurj, hθker, -, -, -⟩ := hC.exists_hom
  obtain ⟨θ', -, hθ'surj, hθ'ker, -, -, -⟩ := hC'.exists_hom
  let f : ↥(commutator C) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
    θ'.comp α.toMonoidHom
  have hfsurj : Function.Surjective f := hθ'surj.comp α.surjective
  let QL : Subgroup ↥(commutator C) := Q.subgroupOf (commutator C)
  haveI hQLn : QL.Normal := (inferInstance : Q.Normal).subgroupOf (commutator C)
  let K : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := QL.map f
  haveI hKn : K.Normal := hQLn.map f hfsurj
  have hcard : Nat.card Q = 2 ^ 9 := by simpa using hC.plus.2.1
  have hK : ∀ p ∈ K, ∃ k : ℕ, p ^ (2 ^ k) = 1 := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hp
    have hlQ : (l : C) ∈ Q := by simpa [QL, Subgroup.mem_subgroupOf] using hl
    refine ⟨9, ?_⟩
    have hq : (⟨(l : C), hlQ⟩ : Q) ^ (2 ^ 9) = 1 := by
      rw [← hcard]; exact pow_card_eq_one'
    have hpow : l ^ (2 ^ 9) = 1 := by
      apply Subtype.ext
      change (l : C) ^ (2 ^ 9) = 1
      simpa using congrArg (Subtype.val) hq
    rw [← map_pow, hpow, map_one]
  have hKbot : K = ⊥ := Swap.eq_bot_of_normal_of_two_power K hK
  have hfl : f l = 1 := by
    have : f l ∈ K := Subgroup.mem_map_of_mem f (by simpa [QL, Subgroup.mem_subgroupOf] using hl)
    simpa [hKbot] using this
  exact (hθ'ker (α l)).1 (by simpa [f] using hfl)

theorem AschbacherHyp.map_mem_iff (hC : AschbacherHyp C Q) (hC' : AschbacherHyp C' Q')
    (α : ↥(commutator C) ≃* ↥(commutator C')) (l : ↥(commutator C)) :
    ((α l : ↥(commutator C')) : C') ∈ Q' ↔ (l : C) ∈ Q := by
  refine ⟨?_, fun hl => AschbacherHyp.map_mem_of_mem hC hC' α hl⟩
  intro h
  have := AschbacherHyp.map_mem_of_mem hC' hC α.symm (l := α l) h
  simpa using this

end CFSG.EvenSporadicStandard.HNRecog
