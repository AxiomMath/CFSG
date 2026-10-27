module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcSmall
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedD4
import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Blueprint.Chevalley
open scoped commutatorElement

@[expose] def SmallExitD4AtThree (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (L J A : Subgroup G) (d b : G)
    (hS : Setup 3 L J A d b),
    catalogIs (PSimple 3 L) (onLie P) →
    ¬ CFSG.LocalAnalysis.GLTheoremA.I171.I171LieShapeAt 3 L → InducesInnerMod 3 L b →
    catalogIs (PSimple 3 J) (onLie fun i : TauCeti.LieTypeIndex =>
      ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) →
    MI.indAut 3 J b hS.b_norm ∈ innAutDerived (PSimple 3 J) →
    InducesInnerMod 3 J b

section Certificates


theorem inducesInnerMod_of_catD4_of_ne_three {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b) (hp3 : p ≠ 3)
    (hCatJ : catalogIs (PSimple p J) (onLie fun i : TauCeti.LieTypeIndex =>
      ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2))
    (hmem : MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J)) :
    InducesInnerMod p J b := by
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.odd
  have hbp : b ^ p = 1 := hS.elem.2 b hS.b_mem
  have hpow : MI.indAut p J b hS.b_norm ^ p = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154_indAut_pow_eq_one hS.b_norm hbp
  refine (MI.indAut_mem_inner_iff hp hS.pcomp hS.b_norm).1 ?_
  obtain ⟨i, hi, ⟨e⟩⟩ := hCatJ
  rcases i with _ | _ | ⟨d', hv⟩ | _
  · exact absurd hi (by simp [onLie])
  · exact absurd hi (by simp [onLie])
  · obtain ⟨q, rfl, -⟩ := hi
    let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
    haveI : Finite F :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.D 4 q, hv⟩
    let θ : PSimple p J ≃* adjointGroup Tag.D4 F :=
      e.trans ((CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid
          4 q hv).trans
        (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
          F).some)
    have hmem' : MulAut.congr θ (MI.indAut p J b hS.b_norm) ∈
        innAutDerived (adjointGroup Tag.D4 F) :=
      (mem_innAutDerived_congr θ).2 hmem
    have hpow' : MulAut.congr θ (MI.indAut p J b hS.b_norm) ^ p = 1 := by
      rw [← map_pow, hpow, map_one]
    obtain ⟨h, hh⟩ :=
      CFSG.ComponentClassification.OuterAutomorphisms.exists_conj_eq_of_mem_innAutDerived_D4
        hp hp2 hp3 hmem' hpow'
    refine (CFSG.HardMathSupport.Dickson.Sec6.I923.congr_mem_inner_iff_of_equiv θ _).1 ?_
    rw [hh]
    exact ⟨h, rfl⟩
  · exact absurd hi (by simp [onLie])

theorem smallExitD4At_of_three {P : TauCeti.LieTypeIndex → Prop}
    (h3 : SmallExitD4AtThree P) : SmallExitD4At P :=
  fun p L J A d b hS hcatL hshape hInnerL hCatJ hmem => by
    by_cases hp3 : p = 3
    · subst hp3
      exact h3 L J A d b hS hcatL hshape hInnerL hCatJ hmem
    · exact inducesInnerMod_of_catD4_of_ne_three hS hp3 hCatJ hmem

theorem excSmallExitD4_of_three
    (h3 : SmallExitD4AtThree fun i : TauCeti.LieTypeIndex =>
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2) :
    ExcSmallExitD4 :=
  smallExitD4At_of_three h3

theorem twE6SmallExitD4_of_three
    (h3 : SmallExitD4AtThree fun i : TauCeti.LieTypeIndex =>
      (∃ q : TauCeti.PrimePower, i = .twistedE6 q) ∧ i.characteristic = 2) :
    TwE6SmallExitD4 :=
  smallExitD4At_of_three h3

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
