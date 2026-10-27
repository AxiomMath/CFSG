module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActInnerCore
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.PerfectCentralQuotient CFSG.GroupActions
open scoped Pointwise commutatorElement


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

def InnerKindClassGroupPerfect (p : ℕ) (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) : Prop :=
  ∀ (σ : L ≃+* L),
    (∀ c : L, σ c = c ^ (S.D.q ^
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) →
    Group.IsPerfect ↥(CQ σ i)

theorem centerQuotientHom_mem_innAutDerived_innerKind
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hperf : InnerKindClassGroupPerfect p S i)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
    ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hzZ, hnorm, hz⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i hs0 hinner
  exact centerQuotientHom_mem_innAutDerived_inner_of_untwist S hT i hs hmin σ hσ hzZ hnorm hz
    (hperf σ hσ) hyZ hyF hyStab

theorem centerQuotientHom_mem_innAutDerived_innerKind_of_four_leT
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  refine centerQuotientHom_mem_innAutDerived_innerKind S hT i hkind ?_ hyZ hyF hyStab
  intro σ hσ
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hσ' : ∀ c : L, σ c = c ^
      (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) := by
    intro c
    rw [hσ, hq, ← pow_mul]
  have hQ' : 4 ≤ r ^
      (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
    rw [pow_mul, ← hq]
    exact hQ
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ'
    (Nat.mul_pos he hs0) hQ'
  haveI : Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ) (χ := rootCharHom a) ht i
  rw [CQ_eq_map (χ := rootCharHom a) (i := i) σ]
  exact Group.IsPerfect.ofSurjective
    (f := (Subgroup.equivMapOfInjective
      (componentRootSpan (fixSubfield σ) (rootCharHom a) i)
      (baseChangeGL (fixSubfield σ).subtype) (baseChangeGL_injective _)).toMonoidHom)
    (Subgroup.equivMapOfInjective
      (componentRootSpan (fixSubfield σ) (rootCharHom a) i)
      (baseChangeGL (fixSubfield σ).subtype) (baseChangeGL_injective _)).surjective

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
