module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriD4Fix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriD4Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterFix
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (twistedFixedPoints d4Nodes D4TrialityLayer)
open CFSG.Blueprint


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}

theorem excTri_D4_perfect_model (S : LangSetup .D4 L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.D4 L Fr) :
    Group.IsPerfect ↥S.D.model := by
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  haveI h2 : CharP L 2 := ‹CharP L 2›
  have hr2 : r = 2 := CharP.eq L hchar h2
  have hq2 : S.D.q = 2 ^ e := by rw [hq, hr2]
  have hperf := excTri_twistedFixedGroup_D4_perfect (L := L) (f := e) (by omega) Fr
    (fun c => by rw [hFr c, hq2])
  have hEq : S.D.fix = twistedFixedGroup TwistTag.D4 L Fr := by
    change adjointGroup Tag.D4 L ⊓ MonoidHom.eqLocus S.D.Φ (MonoidHom.id _) =
      twistedFixedGroup TwistTag.D4 L Fr
    rw [hΦ]
    rfl
  let e₁ : ↥S.D.model ≃* ↥(twistedFixedGroup TwistTag.D4 L Fr) :=
    (S.D.model.equivMapOfInjective (MulAut.conj S.D.g0).toMonoidHom
      (MulAut.conj S.D.g0).injective).trans
      (MulEquiv.subgroupCongr (S.D.map_conj_model.trans hEq))
  haveI : Group.IsPerfect ↥(twistedFixedGroup TwistTag.D4 L Fr) := hperf
  exact Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective

theorem excTri_perfect_D4 (S : LangSetup .D4 L p) {a : Fin Tag.D4.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4) :
    TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  classical
  obtain ⟨hnin, hA | ⟨hr', hc, hnin2⟩⟩ := exc_kind hk
  · obtain ⟨hr6, -⟩ := hA
    rw [hr6] at hr
    exact absurd hr (by decide)
  have hΨ : componentRoots (rootCharHom a) i = {v : Fin Tag.D4.rank → ℤ | IsRoot .D4 v} := by
    refine Set.eq_of_subset_of_ncard_le (fun γ hγ => hγ.1.1) ?_ (finite_setOf_isRoot .D4)
    rw [ncard_setOf_isRoot, hc]
    decide
  have hρ : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hΨ] at hγ ⊢
    exact (S.frob.isRoot_iff γ).2 hγ
  have hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one
      ((finite_setOf_isRoot .D4).subset fun γ hγ => hγ.1.1) hρ
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · exfalso
    rw [hs, Function.iterate_one] at hnin
    have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    refine hnin ?_
    rw [hΨ]
    exact excTri_D4_twistInner_of_untwisted S hFr hΦ'
  · cases t with
    | E6 => exact absurd ht (by decide)
    | D4 =>
      cases ht
      have hΦ' : S.D.Φ = twistHom TwistTag.D4 L Fr := by
        ext1 g
        rw [hΦ]
        rfl
      have hroot : rootSpan Tag.D4 L (componentRoots (rootCharHom a) i) =
          adjointGroup Tag.D4 L := by
        rw [hΨ, adjointGroup_eq_rootSpan]
      have hfix : fixedPointSubgroup (iterHom S.D.step 1)
          (rootSpan Tag.D4 L (componentRoots (rootCharHom a) i)) = S.D.model := by
        rw [hroot]
        refine le_antisymm ?_ ?_
        · intro x hx
          rw [LangDatum.mem_model]
          exact ⟨hx.1, by simpa [iterHom_succ, LangDatum.step] using hx.2⟩
        · intro x hx
          rw [LangDatum.mem_model] at hx
          exact ⟨hx.1, by simpa [iterHom_succ, LangDatum.step] using hx.2⟩
      have hperf := excTri_D4_perfect_model S hFr hΦ'
      rw [TwoDExcFixedPointsPerfect, hs, hfix]
      exact hperf

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
