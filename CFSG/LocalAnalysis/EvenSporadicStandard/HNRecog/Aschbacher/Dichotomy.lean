module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Classification
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.InvariantSubgroups
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.PlusType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

theorem aschbacherDichotomy : AschbacherDichotomy := by
  intro L _ Q hQn hplus hC hL
  haveI := hplus.finite
  have hE := hplus.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  have h8 : finrank (ZMod 2) (Additive (Abelianization Q)) = 8 := by
    rw [hplus.finrank_quotient]
  have hker : (extraspecialConjOrth hE hQn).ker = Q := ker_extraspecialConjOrth hE hC
  let ρ : L ⧸ Q →* TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hE) :=
    QuotientGroup.lift Q (extraspecialConjOrth hE hQn) fun x hx => by
      rw [hker]
      exact hx
  have hρmk : ∀ g : L, ρ (g : L ⧸ Q) = extraspecialConjOrth hE hQn g := fun g => rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ (extraspecialConjOrth hE hQn).ker := (hρmk g).symm.trans hx
    rw [hker] at hg
    exact (QuotientGroup.eq_one_iff g).2 hg
  have key := irreducible_iff_exists_stabilizer_alternatingGroup_five (extraspecialQuadForm hE)
    (extraspecialQuadForm_nondegenerate hE) h8 hplus.isPlusType_extraspecialQuadForm ρ hρinj hL
  have hinv : (∀ U : Submodule (ZMod 2) (Additive (Abelianization Q)),
        (∀ g : L, ∀ u ∈ U, ((extraspecialConjOrth hE hQn g :
          TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hE)) :
            Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) u ∈ U) →
          U = ⊥ ∨ U = ⊤) ↔
      ∀ U : Submodule (ZMod 2) (Additive (Abelianization Q)),
        (∀ g : L ⧸ Q, ∀ u ∈ U, ((ρ g : TauCeti.QuadraticMap.orthogonalGroup
          (extraspecialQuadForm hE)) : Additive (Abelianization Q) ≃ₗ[ZMod 2]
            Additive (Abelianization Q)) u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    refine forall_congr' fun U => imp_congr_left ?_
    constructor
    · intro h g
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
      exact h a
    · intro h a
      exact h (a : L ⧸ Q)
  have hstab : ∀ (x : Q) (g : L ⧸ Q),
      ((ρ g : TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hE)) :
          Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q))
          (Additive.ofMul (Abelianization.of x)) = Additive.ofMul (Abelianization.of x) ↔
        ∃ a : L, (a : L ⧸ Q) = g ∧ ⁅a, (x : L)⁆ ∈ centerOf Q := by
    intro x g
    constructor
    · intro h
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
      exact ⟨b, rfl, (extraspecialConjOrth_apply_eq_iff hE b x).1 h⟩
    · rintro ⟨a, rfl, h⟩
      exact (extraspecialConjOrth_apply_eq_iff hE a x).2 h
  have hne : ∀ x : Q, Additive.ofMul (Abelianization.of x) ≠ 0 ↔ (x : L) ∉ centerOf Q := fun x =>
    not_congr ((ofMul_of_eq_zero_iff hE x).trans (mem_centerOf_iff x).symm)
  refine (forall_invariant_subgroup_iff hE).trans (hinv.trans (key.trans ?_))
  constructor
  · rintro ⟨v, hv, S, hS, hSA⟩
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    exact ⟨(x : L), x.2, (hne x).1 hv, S, fun y => (hS y).trans (hstab x y), hSA⟩
  · rintro ⟨q, hq, hqc, S, hS, hSA⟩
    exact ⟨Additive.ofMul (Abelianization.of (⟨q, hq⟩ : Q)), (hne ⟨q, hq⟩).2 hqc, S,
      fun y => (hS y).trans (hstab ⟨q, hq⟩ y).symm, hSA⟩

end CFSG.EvenSporadicStandard.HNRecog
