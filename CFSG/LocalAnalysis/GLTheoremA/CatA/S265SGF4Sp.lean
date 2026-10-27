module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4StdClasses

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.CatLeafProof

section Pow


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem SG.rationalComponent_sp3_model_pow (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))}
    (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {f : ℕ} (hf : 2 ≤ f)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ f) :
    CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSp 3 2 f := by
  classical
  obtain ⟨σ, hfin, hcard, cov, hcov1, hker, hcov2⟩ := exists_inner_cover S hTor i hinner
  haveI : Fintype ↥(fixSubfield σ) := Fintype.ofFinite ↥(fixSubfield σ)
  haveI : CharP ↥(fixSubfield σ) 2 :=
    ((fixSubfield σ).subtype.charP_iff (fixSubfield σ).subtype_injective 2).2 inferInstance
  have hKcard : Nat.card ↥(fixSubfield σ) = 2 ^ f := by rw [hcard, hQ]
  have hK4 : 4 ≤ Nat.card ↥(fixSubfield σ) := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨Ψ, hΨk, hΨr⟩ : ∃ Ψ : StatedSp 3 ↥(fixSubfield σ) →* ModGL Tag.F4 ↥(fixSubfield σ),
      Ψ.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) ∧
        Ψ.range = rootSpan Tag.F4 ↥(fixSubfield σ)
          ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
    obtain ⟨Ψ0, hk0, hr0⟩ : ∃ Ψ0 : StatedSp 3 ↥(fixSubfield σ) →* ModGL Tag.F4 ↥(fixSubfield σ),
        Ψ0.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) ∧
          Ψ0.range = subsystemGroup .F4 ↥(fixSubfield σ) J := by
      rcases hJ with rfl | rfl
      · exact KSExactSp.exists_sp3_cover_f4_B3_even (by omega) hKcard hK4
      · exact KSExactSp.exists_sp3_cover_f4_C3_even (by omega) hKcard hK4
    have hsub : subsystemGroup Tag.F4 ↥(fixSubfield σ) J =
        rootSpan Tag.F4 ↥(fixSubfield σ) (parabolicRoots Tag.F4 J) :=
      CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := J)
        ↥(fixSubfield σ)
    rw [hsub] at hr0
    have hmap := (canonical_weyl_root_transport Tag.F4 ↥(fixSubfield σ)).1 v
      (parabolicRoots Tag.F4 J) (fun α hα => hα.1)
    refine ⟨(MulAut.conj (canonicalRep (coxeterSystem Tag.F4) ↥(fixSubfield σ) v)).toMonoidHom.comp
      Ψ0, fun x hx => hk0 ?_, ?_⟩
    · rw [MonoidHom.mem_ker] at hx ⊢
      exact (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) ↥(fixSubfield σ) v)).injective
        (by simpa using hx)
    · rw [MonoidHom.range_comp, hr0]
      exact hmap
  have hcomp : componentRootSpan (fixSubfield σ) (rootCharHom a) i =
      rootSpan Tag.F4 ↥(fixSubfield σ) ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
    show rootSpan Tag.F4 (fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  rw [← hcomp] at hΨr
  have hperfSp : commutator (StatedSp 3 ↥(fixSubfield σ)) = ⊤ :=
    (spFactorFacts_holds ↥(fixSubfield σ) 3 (by norm_num) (by simp)).perfect
  have hCperf : ⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i,
      componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
        componentRootSpan (fixSubfield σ) (rootCharHom a) i := by
    rw [← hΨr, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperfSp]
  have hRf : cov.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hcov2 hCperf) hcov1
  let g0 : StatedSp 3 ↥(fixSubfield σ) →*
      ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    Ψ.codRestrict _ (fun x => by rw [← hΨr]; exact ⟨x, rfl⟩)
  have hg0surj : Function.Surjective g0 := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ : y ∈ Ψ.range := hΨr ▸ hy
    exact ⟨x, Subtype.ext hx⟩
  have hg0ker : g0.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    apply hΨk
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hx
  let g : StatedSp 3 ↥(fixSubfield σ) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (cov.comp g0).codRestrict _ (fun x => by rw [← hRf]; exact ⟨g0 x, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ : y ∈ cov.range := hRf ▸ hy
    obtain ⟨x, rfl⟩ := hg0surj c
    exact ⟨x, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : cov (g0 x) = 1 := congrArg Subtype.val hx
    have h2 : g0 x ∈ Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
      hker h1
    rw [← comap_center_of_surjective hperfSp g0 hg0surj hg0ker]
    exact h2
  obtain ⟨e1⟩ := nonempty_centralQuotient_mulEquiv hperfSp g hgsurj hgker
  let e2 := QuotientGroup.quotientMulEquivOfEq
    (CFSG.LieType.Universal.Symplectic.center_eq 3 ↥(fixSubfield σ))
  have hmodel : StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSp 3 2 f :=
    ⟨⟨Nat.prime_two, by omega, by norm_num, by simp⟩, ↥(fixSubfield σ), inferInstance,
      inferInstance, hKcard, ⟨e1.symm.trans e2⟩⟩
  refine ⟨⟨?_, CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 3 2 f
    hmodel⟩, hmodel⟩
  have h1 := congrArg (Subgroup.map g) hperfSp
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective g hgsurj] at h1
  rw [commutator_def]
  exact h1

end Pow

section KernelB


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem SG.rationalComponent_model_of_kernelB (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    {f : ℕ} (hf : 2 ≤ f) (hq : S.D.q = 2 ^ f) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ i, a i = ω ^ k i) (hk : KSF4Std.KernelB k)
    (i : KernelComponent (rootCharHom a)) :
    CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSp 3 2 f := by
  classical
  have hpL : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    intro h
    have h3 : ((3 : ℕ) : L) = 3 := by norm_num
    rw [h3] at h
    have : (1 : L) = 0 := by linear_combination h - h2
    exact one_ne_zero this
  have hT3 : rootDiagUnit Tag.F4 a ^ 3 = 1 := KSF4Std.rootDiagUnit_pow_eq_one hap
  obtain ⟨v, _, _, c, -, hc, -, -, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S Nat.prime_three
      hpL hT3 i
  have hn18 := KSF4Std.ncard_componentRoots_of_kernelB hω3 hω1 hak hk i
  have hc18 : c = [1, 2, 3] ∨ c = [2, 3, 4] :=
    KSF4Std.f4_count18 c hc (hncard.symm.trans hn18)
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    Lemma27Ns.I1433.componentOrbitLength_eq_one S hT i
      (KSF4Std.rho_image_eq_of_kernelB S hT hω3 hω1 hak hk i)
  have hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ f := by
    rw [hs1, hq, pow_one]
  rcases hc18 with rfl | rfl
  · have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
    have hroots' : componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB3 := by
      rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviB3) (by decide)
        (fun j => by rw [mem_f4LeviB3]; revert j; decide)]
    exact SG.rationalComponent_sp3_model_pow S hT i v (Or.inl rfl) hroots'
      (KSF4Std.twistInner_of_rank3_card18 S hT i hr3 hn18) hf hQ
  · have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
    have hroots' : componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviC3 := by
      rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviC3) (by decide)
        (fun j => by rw [mem_f4LeviC3]; revert j; decide)]
    exact SG.rationalComponent_sp3_model_pow S hT i v (Or.inr rfl) hroots'
      (KSF4Std.twistInner_of_rank3_card18 S hT i hr3 hn18) hf hQ

end KernelB

end CFSG.LocalAnalysis.GLTheoremA.S265

end
