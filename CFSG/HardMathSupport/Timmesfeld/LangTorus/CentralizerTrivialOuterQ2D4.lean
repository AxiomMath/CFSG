module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighFixedAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourE8Main
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterPassFormula
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactor
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ2Three

public section
namespace CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.RankThree.Lattice
open CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterQ2Three
open scoped commutatorElement


theorem fixed_mem_rationalComponent_of_perfect
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hperf : TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
      g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hIter : iterHom S.D.step 1 = S.D.step := MonoidHom.ext fun g => by
    rw [iterHom_eq_iterate, Function.iterate_one]
  have hrr := CFSG.StandardType.F4ExplicitPos.CommonFactor.rationalRoots_eq_componentRoots_of_orbitLength_one i hs1
  let P : Subgroup (ModGL τ L) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.fixedPointSubgroup S.D.step (rootSpan τ L (componentRoots (rootCharHom a) i))
  have hPperf : ⁅P, P⁆ = P := by
    have hp : Group.IsPerfect P := by
      dsimp only [TwoDExcFixedPointsPerfect] at hperf
      rw [hs1, hIter] at hperf
      exact hperf
    exact Subgroup.isPerfect_iff.mp hp
  have hP : P ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.D.model := by
    intro g hg
    exact ⟨hrr.symm ▸ hg.1, ⟨rootSpan_le_adjointGroup _ _ hg.1, hg.2⟩⟩
  have hPR := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j.le_rationalComponent_of_perfect S i hP hPperf
  intro g hg hm
  exact hPR ⟨hrr ▸ hg, hm.2⟩


section AnyOuter


theorem outer_d4_mem_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .twoD ∨
      (twistKind S.ρ (rootCharHom a) i = .exc ∧
        compRank (componentRoots (rootCharHom a) i) = 4))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
      g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
  fixed_mem_rationalComponent_of_perfect S hT i
    (twoDExcFixedPointsPerfectAll_holds S hT i hk) hs1

theorem commute_rootSpan_of_commute_component_outer_d4_two
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}
    (S : LangSetup tau L p) (hTau : tau = .E6 ∨ tau = .E7 ∨ tau = .E8)
    (hCheck : RootOps.tableCheck tau = true) (hq : S.D.q = 2)
    {a : Fin tau.rank → Lˣ} (hT : rootDiagUnit tau a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hRank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hCard : (componentRoots (rootCharHom a) i).ncard = 24)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hNotInner : ¬ twistInner (componentRoots (rootCharHom a) i) S.ρ)
    (z : ModGL tau L)
    (hComm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan tau L (componentRoots (rootCharHom a) i), Commute z g := by
  classical
  have hsl : SimplyLacedTag tau := by
    rcases hTau with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hPsi := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hkind : twistKind S.ρ (rootCharHom a) i = .twoD ∨
      (twistKind S.ρ (rootCharHom a) i = .exc ∧
        compRank (componentRoots (rootCharHom a) i) = 4) := by
    unfold twistKind
    rw [hs1, Function.iterate_one, if_neg hNotInner]
    by_cases hexc : (compRank (componentRoots (rootCharHom a) i) = 6 ∧
        (componentRoots (rootCharHom a) i).ncard = 72) ∨
        (compRank (componentRoots (rootCharHom a) i) = 4 ∧
          (componentRoots (rootCharHom a) i).ncard = 24 ∧
          ¬ twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin tau.rank → ℤ) → _)^[2 * 1]))
    · rw [if_pos hexc]
      exact Or.inr ⟨rfl,hRank⟩
    · rw [if_neg hexc, if_pos (by rw [hRank,hCard];norm_num)]
      exact Or.inl rfl
  have hmem := outer_d4_mem_rationalComponent S hT i hkind hs1
  obtain ⟨f,z0,phi,hf,hPos,hPin,hz0,hPhi,hPhiS,hNe,w,hw,hForm⟩ :=
    outer_exists_lang_data_formula S hT i
  have hForm' : ∀ gamma, f gamma = S.ρ (w • gamma) := by
    intro gamma
    rw [hForm,hs1,Function.iterate_one]
  let delta : (Fin tau.rank → ℤ) →+ (Fin tau.rank → ℤ) :=
    S.rhoHom.comp (DistribSMul.toAddMonoidHom (Fin tau.rank → ℤ) w)
  have hDelta : ∀ gamma, delta gamma = f gamma := by intro gamma;rw [hForm'];rfl
  have hIso : ∀ x y, iform (delta x) (delta y) = iform x y := by
    intro x y
    change iform (S.ρ (w • x)) (S.ρ (w • y)) = _
    rw [iform_rho S,iform_smul]
  have hMaps : ∀ gamma ∈ componentRoots (rootCharHom a) i,
      delta gamma ∈ componentRoots (rootCharHom a) i := by
    intro gamma hg
    rw [hDelta]
    exact hf.bijOn.mapsTo hg
  have hPos' : ∀ gamma ∈ posRoots (componentRoots (rootCharHom a) i),
      delta gamma ∈ posRoots (componentRoots (rootCharHom a) i) := by
    intro gamma hg
    rw [hDelta]
    exact hPos gamma hg
  have hDeltaNotInner : ¬ twistInner (componentRoots (rootCharHom a) i) delta := by
    intro hd
    obtain ⟨u,hu,huEq⟩ := hd
    have hdFix : ∀ beta ∈ simpleRoots (componentRoots (rootCharHom a) i), u • beta ∈
        posRoots (componentRoots (rootCharHom a) i) := by
      intro beta hb
      rw [← huEq beta (simpleRoots_subset hb)]
      exact hPos' beta (simpleRoot_mem_posRoots hb)
    have huComp : u ∈ componentWeylGroup (componentRoots (rootCharHom a) i) := by
      refine (Subgroup.closure_le _).2 ?_ hu
      rintro v ⟨gamma,hg,rfl⟩
      exact rootReflection_mem_componentWeylGroup_of_mem hPsi hg
    have huOne : u = 1 := by
      by_contra hne
      obtain ⟨beta,hb,hneg⟩ := exists_smul_mem_negRoots hPsi huComp hne
      exact not_mem_negRoots_of_mem_posRoots (hdFix beta hb) hneg
    obtain ⟨gamma,hg,hmove⟩ := hNe (by simpa only [hs1,Function.iterate_one] using hNotInner)
    apply hmove
    rw [← hDelta,huEq gamma hg,huOne,one_smul]
  have hSelf : ∀ gamma ∈ componentRoots (rootCharHom a) i, iform gamma gamma = 2 :=
    fun gamma hg => outer_iform_self_of_simplyLaced hsl (hPsi.isRoot gamma hg)
  have hCases := d4_graph_root_cases_of_noninner hPsi hSelf hRank hCard
    delta hIso hMaps hPos' hDeltaNotInner
  simp only [hDelta] at hCases
  have hPinTwo : OuterPinned phi f 2 := by simpa only [hs1,hq,pow_one] using hPin
  have hFixComm := outer_two_fixed_central S i hs1 hz0 hPhi
    (fun g hg hm _ => hmem g hg hm) hComm
  have hFixed : ∀ beta ∈ componentRoots (rootCharHom a) i, f beta = beta →
      ∀ t, Commute z (z0 * pinnedX tau L beta t * z0⁻¹) := by
    intro beta hb hfix
    obtain ⟨beta',hb',hfix',hAdj⟩ := (hCases beta hb).2
    exact (outer_two_commute_fixed_of_tableCheck hTau hCheck hPsi hf hPinTwo hFixComm
      hb hb' hfix hfix' hAdj).1
  have hFixedSL : ∀ beta ∈ componentRoots (rootCharHom a) i, f beta = beta →
      ∀ x ∈ rootRankOneGroup tau L beta, Commute z (z0*x*z0⁻¹) := by
    intro beta hb hfix
    have hbneg : -beta ∈ componentRoots (rootCharHom a) i := hPsi.neg_mem _ hb
    have hfixneg : f (-beta) = -beta := by rw [hf.neg beta hb,hfix]
    exact outer_commute_rankOne_of_pm (hPsi.isRoot beta hb)
      (hFixed beta hb hfix) (hFixed (-beta) hbneg hfixneg)
  have hAll : ∀ gamma ∈ componentRoots (rootCharHom a) i, ∀ t,
      Commute z (z0*pinnedX tau L gamma t*z0⁻¹) := by
    intro gamma hg
    by_cases hfix : f gamma = gamma
    · exact hFixed gamma hg hfix
    obtain ⟨beta,hb,hfixb,hAdj⟩ := (hCases gamma hg).2
    rcases (hCases gamma hg).1 with h1 | ⟨h2,hOrth⟩ | ⟨h3,hOrth,hOrth2,hOrth3⟩
    · exact (hfix h1).elim
    · exact outer_two_commute_nonfixed hsl hPsi hf hPinTwo hFixComm
        hg hfix h2 hOrth hb hfixb hAdj (hFixedSL beta hb hfixb)
    · exact outer_three_commute_nonfixed hsl hPsi hf hPinTwo hFixComm
        hg h3 hOrth hb hfixb hAdj (hFixedSL beta hb hfixb)
  have hRootLe : (rootSpan tau L (componentRoots (rootCharHom a) i)).map
      (MulAut.conj z0).toMonoidHom ≤ Subgroup.centralizer {z} := by
    simp only [rootSpan,Subgroup.map_iSup]
    refine iSup₂_le fun gamma hg => ?_
    rw [rootSubgroup,MonoidHom.map_closure,Subgroup.closure_le]
    rintro g ⟨_,⟨t,rfl⟩,rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hAll gamma hg t).symm.eq
  intro g hg
  have hg' : z0⁻¹*g*z0 ∈ rootSpan tau L (componentRoots (rootCharHom a) i) := by
    apply (hz0 _).2
    have heq : z0 * (z0⁻¹*g*z0) * z0⁻¹ = g := by group
    rw [heq]
    exact hg
  have hc : g ∈ Subgroup.centralizer {z} := hRootLe (Subgroup.mem_map.mpr ⟨z0⁻¹*g*z0,hg',by
    change z0*(z0⁻¹*g*z0)*z0⁻¹=g
    group⟩)
  exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm


end AnyOuter

theorem twoD_four_mem_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
      g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
  fixed_mem_rationalComponent_of_perfect S hT i
    (twoDExcFixedPointsPerfect_holds S hT i hk) hs1

theorem commute_rootSpan_of_commute_component_twoD_four_two
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (S : LangSetup τ L p)
    (hTau : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hcheck : RootOps.tableCheck τ = true)
    (hq : S.D.q = 2) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    (hRank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (z : ModGL τ L) (hComm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  classical
  have hsl : SimplyLacedTag τ := by
    rcases hTau with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hPsi := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hCard : (componentRoots (rootCharHom a) i).ncard = 24 := by
    rw [(shape_of_twistKind_twoD hk).2, hRank]
  obtain ⟨f, z0, phi1, hf, hPos, hPin, hz0, hPhi1, hPhiS, hNe, w, hw, hForm⟩ :=
    outer_exists_lang_data_formula S hT i
  have hForm' : ∀ gamma, f gamma = S.ρ (w • gamma) := by
    intro gamma
    rw [hForm, hs1, Function.iterate_one]
  have hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    have h := (outer_componentOrbitLength_spec S hT i).2.1
    rwa [hs1, Function.iterate_one] at h
  let delta : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    S.rhoHom.comp (DistribSMul.toAddMonoidHom (Fin τ.rank → ℤ) w)
  have hDelta : ∀ gamma, delta gamma = f gamma := by intro gamma; rw [hForm']; rfl
  have hIso' : ∀ x y, iform (delta x) (delta y) = iform x y := by
    intro x y
    change iform (S.ρ (w • x)) (S.ρ (w • y)) = _
    rw [iform_rho S, iform_smul]
  have hMaps : ∀ gamma ∈ componentRoots (rootCharHom a) i, delta gamma ∈ componentRoots (rootCharHom a) i := by
    intro gamma hg
    rw [hDelta]
    exact hf.bijOn.mapsTo hg
  have hPos' : ∀ gamma ∈ posRoots (componentRoots (rootCharHom a) i), delta gamma ∈ posRoots (componentRoots (rootCharHom a) i) := by
    intro gamma hg
    rw [hDelta]
    exact hPos gamma hg
  have hMove : ∃ gamma ∈ componentRoots (rootCharHom a) i, delta gamma ≠ gamma := by
    obtain ⟨gamma, hg, hfg⟩ := hNe (by simpa only [hs1, Function.iterate_one] using not_twistInner_of_twistKind_twoD_exc (Or.inl hk))
    exact ⟨gamma, hg, by simpa only [hDelta] using hfg⟩
  have hMoveSimple := exists_simpleRoot_ne_of_exists_ne hPsi hMove
  have hInner2 := twistInner_iterate_two_of_twistKind_twoD hk hs1 hRank
  have hDeltaInvol : ∀ gamma ∈ componentRoots (rootCharHom a) i, delta (delta gamma) = gamma := by
    intro gamma hg
    have hwR : w ∈ componentWeylGroup (componentRoots (rootCharHom a) i) := hw
    let v := (exists_rho_conj_realization S hPsi hst hwR).choose
    have hv := (exists_rho_conj_realization S hPsi hst hwR).choose_spec
    have hDF : ∀ beta ∈ componentRoots (rootCharHom a) i, delta beta = S.rhoTwist v beta := by
      intro beta hb
      change S.ρ (w • beta) = v • S.ρ beta
      have h := hv.2 (S.ρ beta) (hst ▸ Set.mem_image_of_mem _ hb)
      rwa [Equiv.symm_apply_apply] at h
    have hPV : ∀ beta ∈ posRoots (componentRoots (rootCharHom a) i), S.rhoTwist v beta ∈ posRoots (componentRoots (rootCharHom a) i) := by
      intro beta hb
      rw [← hDF beta (posRoots_subset hb)]
      exact hPos' beta hb
    have hInv := rhoTwist_sq_eq_self S hPsi hst hInner2 hv.1 hPV gamma hg
    calc delta (delta gamma) = S.rhoTwist v (delta gamma) := hDF _ (hMaps gamma hg)
      _ = S.rhoTwist v (S.rhoTwist v gamma) := by rw [hDF gamma hg]
      _ = gamma := hInv
  have hSelf : ∀ gamma ∈ componentRoots (rootCharHom a) i, iform gamma gamma = 2 := fun gamma hg => outer_iform_self_of_simplyLaced hsl (hPsi.isRoot gamma hg)
  obtain ⟨hG, hAdj⟩ := graphTwist_and_fixed_adj_of_rankFour hPsi hSelf hRank
    (by rw [hCard,hRank]) delta hIso' hMaps hPos' hDeltaInvol hMoveSimple
  obtain ⟨hInv,hOrth,hR2,hR3⟩ := hG.root_facts hIso' hPsi hMaps hAdj
  simp only [hDelta] at hInv hOrth hR2 hR3
  have hmem := twoD_four_mem_rationalComponent S hT i hk hs1
  apply commute_rootSpan_of_commute_component_outer_two_of_tableCheck S hTau hcheck i hs1 hf
    (by simpa only [hs1,hq,pow_one] using hPin) hz0 hPhi1 hInv hOrth hR2 hR3 (fun g hg hm _ => hmem g hg hm) z hComm

end CFSG.HardMathSupport.Timmesfeld.LangTorus
