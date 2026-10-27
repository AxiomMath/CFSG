module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreKerDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4Center
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4TwoD
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfAssemble

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict)
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynE
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


private theorem tits_twB2_of_ade {t : StatedLieTag} (ht : IsADETag t ∨ t = .trialityD4) :
    t ≠ .Tits ∧ t ≠ .twistedB2 := by
  rcases ht with ht | rfl
  · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

theorem e6_lieModel_alternative (hD4 : InnerD4FixedPointsPerfect) {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {y : ModGL Tag.E6 L}
    (hyZ : y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ (t : StatedLieTag) (n f : ℕ),
      CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) t n 2 f ∧
      t ≠ .Tits ∧ t ≠ .twistedB2 ∧
      (¬ (t = .POmegaPlus ∧ n = 4) ∨
        centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
            (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
              ⟨MulAut.conj y, hyStab⟩) ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner
            (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) := by
  classical
  have hring : ringChar L = 2 := ringChar.eq L 2
  have hp : Nat.Prime 3 := Nat.prime_three
  have hℓp : ringChar L ≠ 3 := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hD : compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    ·
      have hspec := outer_componentOrbitLength_spec S hT i
      haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
        ⟨Nat.pos_iff_ne_zero.mp hspec.1⟩
      have hZ := center_eq_bot_of_compRank_four_ncard_24 (L := L) i hD.1 hD.2
      have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
        unfold twistKind
        rw [if_pos hinner]
      have hinn := centerQuotientHom_mem_inner_twoDExcRankFour S hT i hspec.2.1 hspec.2.2 hZ
        (hD4 S hT i hkind hD.1 hD.2) hyZ hyF hyStab
      obtain ⟨t, n, f, ht, hm⟩ := tagLie_rationalComponent_E6 S hp hT hap h1 i hQS
      rw [hring] at hm
      exact ⟨t, n, f, hm, (tits_twB2_of_ade ht).1, (tits_twB2_of_ade ht).2, Or.inr hinn⟩
    ·
      obtain ⟨t, n, f, ht, hm⟩ := tagLie_rank_four_E6 S hp hpL hT hTp i hD.1 hD.2 hinner
      rw [hring] at hm
      refine ⟨t, n, f, hm, ?_, ?_, Or.inl ?_⟩ <;> rcases ht with rfl | rfl
      all_goals first | decide | (rintro ⟨h, -⟩; cases h)
  · obtain ⟨t, n, f, ht, hm⟩ := rankLie_rationalComponent_E6_of_not_d4 S hp hT hap h1 i hQS hD
    rw [hring] at hm
    refine ⟨t, n, f, hm, ?_, ?_, Or.inl ?_⟩ <;> rcases ht with rfl | rfl | ⟨rfl, hn⟩ | rfl
    all_goals first | decide | (rintro ⟨-, h⟩; exact hn h) | (rintro ⟨h, -⟩; cases h)

theorem e6ToralKernelExit_of (hD4 : InnerD4FixedPointsPerfect) : E6ToralKernelExit := by
  intro n K _ _ _ hn hK h3 wd wb hwd3 hwd1 hwb3 w g0 hg0 hF htorus Kc hKc hnorm D hinn
  haveI : Finite (TableBExc.RecipeGroup Tag.E6 K) := TableBExc.finite_recipeGroup Tag.E6 K
  obtain ⟨t, m, f, hLM, htits, hsz, hcase⟩ :=
    e6_lieModel_alternative hD4 D.S D.hT D.hap D.h1 D.i D.hQS D.hyZ D.hyF D.hyStab
  exact innDiagOn_map_conj_of_action (TableBExc.center_recipeGroup_eq_bot Tag.E6 K)
    (e6RecipeConj wb) hnorm D.e D.hyStab D.hact D.hQS hLM htits hsz hcase hinn

theorem twE6ToralKernelExit_of (hD4 : InnerD4FixedPointsPerfect) : TwE6ToralKernelExit := by
  intro n K _ _ hn hKcard h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg hn0 htorus Kc hKc hnorm D hinn
  haveI hcharK : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by
    rw [hKcard, pow_mul])
  haveI hcharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hKcard
  obtain ⟨t, m, f, hLM, htits, hsz, hcase⟩ :=
    e6_lieModel_alternative hD4 D.S D.hT D.hap D.h1 D.i D.hQS D.hyZ D.hyF D.hyStab
  exact innDiagOn_map_conj_of_action (TwE6Delta.center_recipeR_eq_bot hn hKcard)
    (TwE6Transport.recipeConj σ ε wb) hnorm D.e D.hyStab D.hact D.hQS hLM htits hsz hcase hinn

end CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit

end
