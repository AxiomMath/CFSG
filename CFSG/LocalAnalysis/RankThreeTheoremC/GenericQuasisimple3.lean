module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.RankThree.PartOne.KS.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped MatrixGroups commutatorElement
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.RankThree.PartOne (SectionsForceEvenRankFour)
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def GL83GenericListExclusionRed (G : Type) [Group G] [Finite G] : Prop :=
  GenericAt G fun p _ M x => 5 ≤ p → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J →
      (IsRankTwoSEGroup p Q ∨ (p = 5 ∧ IsoLie Q (.suzuki 2))) →
      ¬ Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) →
      ∃ _ : Fact p.Prime, Nonempty (Q ≃* PSL(2, GaloisField p 2))

section LiftToG

variable {G : Type} [Group G] [Finite G] {p : ℕ} {C : Subgroup G}

theorem exists_surjective_ker_primeCore [Fact p.Prime] (J : Subgroup C) [J.Normal] :
    ∃ ψ : ↥(J.map C.subtype) →* ↥(J.map (QuotientGroup.mk' (primeComplementCore (G := C) p))),
      Function.Surjective ψ ∧
        ψ.ker = (rankThreePrimeCore p (J.map C.subtype)).subgroupOf (J.map C.subtype) := by
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  let e : J ≃* J.map C.subtype := J.equivMapOfInjective C.subtype C.subtype_injective
  let ψ₀ : J →* J.map π := (π.comp J.subtype).codRestrict (J.map π)
    fun j => Subgroup.mem_map_of_mem π j.2
  let ψ : J.map C.subtype →* J.map π := ψ₀.comp e.symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, j, hj, rfl⟩
    exact ⟨e ⟨j, hj⟩, by simp [ψ, ψ₀]⟩
  have hcoe : ∀ a : J.map C.subtype, (((e.symm a : J) : C) : G) = (a : G) := by
    intro a
    conv_rhs => rw [← e.apply_symm_apply a]
    rfl
  refine ⟨ψ, hψ, ?_⟩
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, rankThreePrimeCore_map_subtype]
  constructor
  · intro ha
    have h1 : π ((e.symm a : J) : C) = 1 := by
      have := congrArg Subtype.val ha
      simpa [ψ, ψ₀] using this
    have h2 : ((e.symm a : J) : C) ∈ O := by
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨((e.symm a : J) : C), ⟨(e.symm a).2, h2⟩, hcoe a⟩
  · rintro ⟨c, ⟨hcJ, hcO⟩, hca⟩
    have hc : e.symm a = ⟨c, hcJ⟩ := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact Subtype.ext hca.symm
    apply Subtype.ext
    have : π c = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hcO
    simpa [ψ, ψ₀, hc] using this

end LiftToG

end CFSG.LocalAnalysis.RankThreeTheoremC
