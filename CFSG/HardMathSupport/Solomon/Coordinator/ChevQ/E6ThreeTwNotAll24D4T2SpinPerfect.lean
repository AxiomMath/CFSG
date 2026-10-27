module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2SpinPerfectTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Inner
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2TorusDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false

section Main


theorem d4t2sp_CQ_perfect {L : Type} [Field L] [IsAlgClosed L] (σ : L ≃+* L)
    [Finite ↥(fixSubfield σ)] {l f : ℕ} (hl : l.Prime) (hf : 0 < f)
    (hK : Nat.card ↥(fixSubfield σ) = l ^ f) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    ⁅CQ σ i, CQ σ i⁆ = CQ σ i := by
  classical
  obtain ⟨_, w, m0, m1, m2, m3, m4, m5, -, hsum, -, hcl⟩ := TwE6UniqAbs.kac_class_data h3 hap
  obtain ⟨x, hx, hroots, hncard, -, -⟩ := hcl i
  have hD4 := d4t2in_cmpF_eq_sD4 hsum hx (hncard.symm.trans hc)
  have hfam : componentRoots (rootCharHom a) i =
      rootsOfFam (fun y => w⁻¹ • kacE6.extRoot y) (Set.range TwE6InnerAbs.lD4) := by
    rw [hroots, hD4, ← TwE6InnerAbs.range_lD4]
    exact TwE6InnerAbs.image_rootsOf_eq_rootsOfFam kacE6 w⁻¹ _
  obtain ⟨X, _, hX, -, g, hg, -⟩ := innerRecog_D (τ := .E6) (Or.inr (Or.inl rfl)) (n := 4) le_rfl
    (K := ↥(fixSubfield σ)) hl hf hK (fun y => w⁻¹ • kacE6.extRoot y)
    (fun y => IsRoot.smul (kacE6.isRoot_extRoot y) w⁻¹) TwE6InnerAbs.lD4
    (fun c d hcd h1 h2 => by
      show iform (w⁻¹ • kacE6.extRoot (TwE6InnerAbs.lD4 c))
        (w⁻¹ • kacE6.extRoot (TwE6InnerAbs.lD4 d)) = 0
      rw [iform_smul, kacE6_extRoot]
      exact TwE6InnerAbs.d4_hgram c d hcd h1 h2)
    (fun c d h => TwE6InnerAbs.d4_frames w⁻¹ c d h)
  have hcomm : commutator ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) = ⊤ := by
    have hcs : componentRootSpan (fixSubfield σ) (rootCharHom a) i =
        rootSpan Tag.E6 (fixSubfield σ)
          (rootsOfFam (fun y => w⁻¹ • kacE6.extRoot y) (Set.range TwE6InnerAbs.lD4)) := by
      show rootSpan Tag.E6 (fixSubfield σ) (componentRoots (rootCharHom a) i) = _
      rw [hfam]
    rw [hcs]
    have h1 := congrArg (Subgroup.map g) hX.perfect
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective g hg] at h1
    rw [commutator_def]
    exact h1
  have hperf := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hcomm)
  rw [CQ_eq_map i σ, ← Subgroup.map_commutator, hperf]

open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc in
theorem d4t2_fixedSpinPerfect : D4T2FixedSpinPerfect := by
  intro L _ _ p₀ S _ _ l f hl hf hq hl3 h3 h3q a hT hap hall hinner
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP L l := by
    rw [CharP.charP_iff_prime_eq_zero hl]
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff hf.ne').1 h
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1
  obtain ⟨α, hα⟩ : (kernelRoots (rootCharHom a)).Nonempty := by
    rw [← Set.ncard_pos hfin, hall]
    norm_num
  let i : KernelComponent (rootCharHom a) := ⟦⟨α, hα⟩⟧
  obtain ⟨hr, hc⟩ := d4t2_class_of_card h3 hap hall i
  have hsub : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) :=
    fun γ hγ => hγ.1
  have hker : kernelRoots (rootCharHom a) = componentRoots (rootCharHom a) i :=
    (Set.eq_of_subset_of_ncard_le hsub (hall.trans hc.symm).le hfin).symm
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
      (rootDiagUnitHom Tag.E6 L).map_pow a 3
    have h2 : a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, hap j, Pi.one_apply]
    rw [← h1, h2, CFSG.LieType.Chevalley.rootDiagUnit_one]
  obtain ⟨v, hv, -⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3 facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  have hinner1 : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[1]) := by
    rw [Function.iterate_one, ← hker]
    exact hinner
  obtain ⟨σ, z, hσ, -, hnorm, hz⟩ := exists_untwistT_Z S hT i (s := 1) Nat.one_pos hinner1
  have hσ' : ∀ c, σ c = c ^ (l ^ f) := fun c => by rw [hσ, pow_one, hq]
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := l) (n := f) hf σ hσ'
  haveI : Finite ↥(fixSubfield σ) := hfinK
  have hCQperf := d4t2sp_CQ_perfect σ hl hf hKcard h3 hap i hc
  have hstep : ∀ x, iterHom S.D.step 1 x = S.D.step x := fun x => rfl
  have hmodel : ∀ y, y ∈ S.D.model ↔ y ∈ adjointGroup Tag.E6 L ∧ S.D.step y = y :=
    fun y => Iff.rfl
  have hCQU : CQ σ i ≤ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, -, rfl⟩
    exact pinnedX_mem_rootSpan (by rwa [unionRoots_singleton] at hγ) c
  have hCQfix : ∀ x ∈ CQ σ i, frobGL σ x = x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨γ, -, c, hc, rfl⟩ := hx
      rw [frobGL_pinnedX, hc]
    | one => exact map_one _
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  have hM : rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model =
      (CQ σ i).map (MulAut.conj z).toMonoidHom := by
    rw [hker]
    ext y
    constructor
    · intro hy
      obtain ⟨hyU, hyM⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨-, hystep⟩ := (hmodel y).1 hyM
      obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ModGL Tag.E6 L, y₀ = z⁻¹ * y * z := ⟨_, rfl⟩
      have e : z * y₀ * z⁻¹ = y := by rw [hy₀]; group
      have hy₀U : y₀ ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) :=
        (hnorm i y₀).2 (by rw [e]; exact hyU)
      have h1 := hz y₀ hy₀U
      rw [e, hstep, hystep] at h1
      have hfix : frobGL σ y₀ = y₀ := by
        calc frobGL σ y₀ = z⁻¹ * (z * frobGL σ y₀ * z⁻¹) * z := by group
          _ = z⁻¹ * y * z := by rw [← h1]
          _ = y₀ := hy₀.symm
      exact ⟨y₀, d4t2sp_fixed_mem_CQ σ hv hy₀U hfix, e⟩
    · rintro ⟨x, hxC, rfl⟩
      have hxU := hCQU hxC
      have hyU : (MulAut.conj z).toMonoidHom x ∈
          rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := (hnorm i x).1 hxU
      refine Subgroup.mem_inf.2 ⟨hyU, (hmodel _).2 ⟨rootSpan_le_adjointGroup L _ hyU, ?_⟩⟩
      show S.D.step (z * x * z⁻¹) = z * x * z⁻¹
      rw [← hstep, hz x hxU, hCQfix x hxC]
  rw [hM, ← Subgroup.map_commutator, hCQperf]

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
