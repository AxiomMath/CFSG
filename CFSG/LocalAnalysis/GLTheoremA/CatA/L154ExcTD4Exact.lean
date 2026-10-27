module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgE7

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open
open CFSG.Blueprint (LieModel classicalTags)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups Matrix

set_option maxRecDepth 100000

@[expose] def L154ExactModel (X : Type) [Group X] : Prop :=
  (∃ (t : StatedLieTag) (n f : ℕ), LieModel X t n 2 f ∧ t ≠ .trialityD4) ∨
    Nonempty (X ≃* alternatingGroup (Fin 6))

theorem l154td4_exact_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hp : p = 2) (ht : t ≠ .trialityD4) (h : LieModel X t n p f) : L154ExactModel X := by
  subst hp
  exact Or.inl ⟨t, n, f, h, ht⟩

theorem l154td4_exact_of_statedClassical {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hp : p = 2) (ht : t ∈ classicalTags) (htd : t ≠ .trialityD4)
    (h : StatedClassicalModel X t n p f) : L154ExactModel X :=
  l154td4_exact_of_lieModel hp htd (Or.inl ⟨ht, h⟩)

section Defs


@[expose] def L154ExactClass {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) : Prop :=
  L154ExactModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
    Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

end Defs

section TypeA

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154td4_exact_typeA (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ k, a k ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    L154ExactClass S i := by
  obtain ⟨ν, f, -, -, -, hmodel⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_typeA_model S hp hT hap h1 i hA
      hqs
  rw [ringChar.eq L 2] at hmodel
  rcases hmodel with h | h
  · exact l154td4_exact_of_statedClassical rfl (by simp [classicalTags]) (by decide) h
  · exact l154td4_exact_of_statedClassical rfl (by simp [classicalTags]) (by decide) h

end TypeA

section DInner

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}

theorem l154td4_exact_dInner_E6 (S : LangSetup Tag.E6 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hTp : rootDiagUnit Tag.E6 a ^ p = 1)
    (i : KernelComponent (rootCharHom a)) (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154ExactClass S i := by
  obtain ⟨n, e, hmodel⟩ := l154_model_of_dClass_E6 S hp hpL hTor hTp i h4 hn hinner
  rw [ringChar.eq L 2] at hmodel
  exact l154td4_exact_of_statedClassical rfl (by simp [classicalTags]) (by decide) hmodel

theorem l154td4_exact_dInner_E7 (S : LangSetup Tag.E7 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E7.rank → Lˣ}
    (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus) (hTp : rootDiagUnit Tag.E7 a ^ p = 1)
    (i : KernelComponent (rootCharHom a)) (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154ExactClass S i := by
  obtain ⟨n, e, hmodel⟩ := l154_model_of_dClass_E7 S hp hpL hTor hTp i h4 hn hinner
  rw [ringChar.eq L 2] at hmodel
  exact l154td4_exact_of_statedClassical rfl (by simp [classicalTags]) (by decide) hmodel

theorem l154td4_exact_dInner_E8 (S : LangSetup Tag.E8 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E8.rank → Lˣ}
    (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus) (hTp : rootDiagUnit Tag.E8 a ^ p = 1)
    (i : KernelComponent (rootCharHom a)) (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154ExactClass S i := by
  obtain ⟨n, e, hmodel⟩ := l154_model_of_dClass_E8 S hp hpL hTor hTp i h4 hn hinner
  rw [ringChar.eq L 2] at hmodel
  exact l154td4_exact_of_statedClassical rfl (by simp [classicalTags]) (by decide) hmodel

end DInner

section TwoD

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154td4_exact_twoD {p : ℕ} (hp : p.Prime) (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154ExactClass S i := by
  obtain ⟨m, e, -, hlie⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.lieModel_rationalComponent_of_twoD_highG hp S
      hT hap h1 i h5 hn hout (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  exact l154td4_exact_of_lieModel (ringChar.eq L 2) (by decide) hlie

end TwoD

section E7Class

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154td4_exact_e7Class (S : LangSetup Tag.E8 L p₀) {p : ℕ}
    (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin Tag.E8.rank → Lˣ}
    (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus) (hTp : rootDiagUnit Tag.E8 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h7 : compRank (componentRoots (rootCharHom a) i) = 7)
    (hn : (componentRoots (rootCharHom a) i).ncard = 126)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154ExactClass S i := by
  classical
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
  have hn' : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
    rw [hn, h7]
    rfl
  obtain ⟨v, n, l, -, -, hrk, hroots, hnon, hE⟩ :=
    l154_exists_tree_of_class_rank kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card edgeE 6
      eRootCount e8_ecount e8_etrees (fun n => n = 6 ∨ n = 7 ∨ n = 8) e8_elen S hp hpL hTp i h6 hn'
  have hn7 : n = 7 := by rw [← hrk, h7]
  subst hn7
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hr2 : r = 2 := (ringChar.eq L r).symm.trans h2
  have hroots' : componentRoots (rootCharHom a) i =
      rootsOfFam (fun x => v • kacE8.extRoot x) (Set.range l) := by
    rw [hroots, l154_smul_image_rootsOf_eq]
  have hmodel := l154_rationalComponent_e7Model S (Or.inr (Or.inr (Or.inr rfl))) hTor i hinner
    (fun x => v • kacE8.extRoot x) (fun b => IsRoot.smul (kacE8.isRoot_extRoot b) v) l hroots'
    (fun c d hcd h1 h2 => by
      show iform (v • kacE8.extRoot (l c)) (v • kacE8.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (fun {F} _ c d hcd =>
      treeFrames kacE8 (fun {F} _ x y h => e8_frames x y h) v l (edgeE 7) hE (F := F) c d hcd)
    hr he hq
  subst hr2
  exact l154td4_exact_of_lieModel rfl (by decide) hmodel

end E7Class

theorem l154td4_f4_exact_of_spSurj {m f : ℕ} (hadm : StatedLieAdmissible .PSp m 2 f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) {X : Type} [Group X]
    (g : StatedSp m K →* X) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (StatedSp m K)) : L154ExactModel (X ⧸ Subgroup.center X) := by
  have hperf : commutator (StatedSp m K) = ⊤ := Group.isPerfect_def.mp
    (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible m K hadm hK).1
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hperf g hg hker
  exact Or.inl ⟨.PSp, m, f, Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK,
    ⟨e.symm.trans (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m K)⟩⟩, by decide⟩

theorem l154td4_f4_exact_of_sp42 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {X : Type} [Group X] (eR : ↥(commutator ↥(StatedSp 2 K)) ≃* X) :
    L154ExactModel (X ⧸ Subgroup.center X) := by
  let e : X ≃* alternatingGroup (Fin 6) :=
    eR.symm.trans (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK)
  exact Or.inr ⟨(QuotientGroup.congr (Subgroup.center X)
    (Subgroup.center (alternatingGroup (Fin 6))) e (Subgroup.map_center_eq e)).trans
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by norm_num))).trans
      QuotientGroup.quotientBot)⟩

section F4Cover

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154td4_exact_f4_cover (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))}
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) {m : ℕ} (hm : 2 ≤ m)
    (hQ : m = 2 → 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    (hcov : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ), 0 < f →
      Nat.card K = 2 ^ f → (m = 2 → 4 ≤ Nat.card K) → ∃ Ψ : StatedSp m K →* ModGL Tag.F4 K,
        Ψ.ker ≤ Subgroup.center (StatedSp m K) ∧ Ψ.range = subsystemGroup .F4 K J) :
    L154ExactClass S i := by
  classical
  obtain ⟨K, hfin, hcard, g, hg, hker⟩ := l154f4_exists_spSurj S hT i hinner (m := m)
    (fun K hfin hK => by
      haveI := hfin
      obtain ⟨hch, f, hf, hKf, hadm, h4⟩ := l154f4_subfield_params K hm hK hQ
      haveI := hch
      refine ⟨Group.isPerfect_def.mp
        (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible m ↥K hadm hKf).1, ?_⟩
      obtain ⟨Ψ, hΨk, hΨr⟩ := hcov ↥K f hf hKf h4
      obtain ⟨Ψ', hk', hr'⟩ := l154f4_spRange_smul v hΨk hΨr
      refine ⟨Ψ', hk', ?_⟩
      rw [hr']
      show _ = rootSpan Tag.F4 ↥K (componentRoots (rootCharHom a) i)
      rw [hroots])
  haveI := hfin
  obtain ⟨-, f, -, hKf, hadm, -⟩ := l154f4_subfield_params K hm hcard hQ
  exact l154td4_f4_exact_of_spSurj hadm hKf g hg hker

end F4Cover

section F4B2

variable
  {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem l154td4_exact_f4_b2_two (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4)
    (hroots : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 3)
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    L154ExactClass S i := by
  classical
  obtain ⟨K', hfin, C, D, hC, hD, hcard, f, hf1, -, hf2⟩ :=
    exists_inner_cover_derived_two S hT i hinner hQ
  haveI := hfin
  obtain ⟨φ, hφ⟩ := l154f4_b2Hom (K := ↥K')
  have hr : ((adjointGroup .F4 ↥K').subtype.comp φ).range = subsystemGroup .F4 ↥K' f4LeviB2 := by
    rw [MonoidHom.range_comp, hφ, map_subtype_sup_b2]
  have hψ : ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) ↥K' v)).toMonoidHom.comp
      ((adjointGroup .F4 ↥K').subtype.comp φ)).range = C := by
    rw [l154f4_conj_range v hr, hC]
    show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
    rw [hroots]
  obtain ⟨eR⟩ := l154f4_equiv_of_derived_two hcard _ hψ hD f hf1 hf2
    (l154f4_ne_bot_of_isQuasisimple hqs)
  exact l154td4_f4_exact_of_sp42 hcard eR

end F4B2

section F4Dispatch

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154td4_exact_f4 (S : LangSetup Tag.F4 L p₀) {p : ℕ} {a : Fin Tag.F4.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S p a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    L154ExactClass S i := by
  obtain ⟨hp, hp2, hT, hap, h1, hqs⟩ := hcls
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hcases := f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hA1
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · rcases hcases with ⟨v, hroots, -, -⟩ | ⟨v, J, hJ, hroots, -, -⟩
    · by_cases hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
      · exact l154td4_exact_f4_cover S hT i v hroots hinner le_rfl (fun _ => hQ)
          (fun K _ _ _ _ _ _ h4 => l154f4_cover_B2 (h4 rfl))
      · exact l154td4_exact_f4_b2_two S hT i v hroots hinner (not_le.1 hQ) hqs
    · exact l154td4_exact_f4_cover S hT i v hroots hinner (by norm_num)
        (fun h => absurd h (by norm_num)) (fun K _ _ _ _ hf hK _ => l154f4_cover_levi hJ hf hK)
  · exfalso
    rcases hcases with ⟨v, hroots, hr, hn⟩ | ⟨v, J, hJ, hroots, hr, hn⟩
    · exact hinner (twistInner_of_shape S hT i 2 8 hr hn (by omega) (by omega) (by omega)
        (by omega))
    · exact hinner (twistInner_of_shape S hT i 3 18 hr hn (by omega) (by omega) (by omega)
        (by omega))

end F4Dispatch

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
