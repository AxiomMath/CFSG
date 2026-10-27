module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2SpinPerfect

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.HardMathSupport.Lang.E6Descent
open scoped Matrix MatrixGroups

section D4


variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem d4_rational_quasisimple (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) (hq2 : S.D.q = 2)
    (hAlg : S.IsAlgebraic) (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (haT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    (i : KernelComponent (rootCharHom a)) :
    componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) ∧
      rationalRoots S.ρ (rootCharHom a) i = kernelRoots (rootCharHom a) ∧
      CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      3 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hrk, hcn⟩ := d4t2_class_of_card h3 hap hall i
  have hker : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) :=
    Set.eq_of_subset_of_ncard_le (KSNotAll24.componentRoots_subset_kernelRoots _ _)
      (by rw [hall, hcn]) (KSNotAll24.finite_kernelRoots_E6 _)
  obtain ⟨ζ', w, m0, m1, m2, m3, m4, m5, hprim, hsum, hchar, hcl⟩ := kac_class_data h3 hap
  obtain ⟨x, hx, hroots, hncard, -, -⟩ := hcl i
  have hD4 := d4t2in_cmpF_eq_sD4 hsum hx (hncard.symm.trans hcn)
  have hfam : componentRoots (rootCharHom a) i =
      rootsOfFam (fun y => w⁻¹ • kacE6.extRoot y) (Set.range TwE6InnerAbs.lD4) := by
    rw [hroots, hD4, ← TwE6InnerAbs.range_lD4]
    exact TwE6InnerAbs.image_rootsOf_eq_rootsOfFam kacE6 w⁻¹ _
  have hinneg : twistInner (componentRoots (rootCharHom a) i) (fun γ => -γ) := by
    rw [hroots, hD4]
    exact TwE6InnerAbs.twistInner_neg_D4 w⁻¹ (fun _ => rfl)
  have hΨroot : ∀ γ ∈ componentRoots (rootCharHom a) i, IsRoot Tag.E6 γ :=
    fun γ hγ => hγ.1.1
  have hinρ : twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
    obtain ⟨v, hv, hvγ⟩ := hinneg
    exact ⟨v, hv, fun γ hγ => (hρ γ (hΨroot γ hγ)).trans (hvγ γ hγ)⟩
  have hρst : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hρ γ (hΨroot γ hγ)]
    exact (isRootComponent_componentRoots i).neg_mem γ hγ
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hρst
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    rw [hs1, Function.iterate_one]
    exact hinρ
  have hq' : S.D.q = 2 ^ 1 := by rw [hq2, pow_one]
  obtain ⟨hmodel, F, _, hZ⟩ := d4t2in_dModel_center S (Or.inr (Or.inl rfl)) haT i hinner
    (n := 4) le_rfl (fun y => w⁻¹ • kacE6.extRoot y)
    (fun y => IsRoot.smul (kacE6.isRoot_extRoot y) w⁻¹) TwE6InnerAbs.lD4 hfam
    (fun c d hcd h1 h2 => by
      show iform (w⁻¹ • kacE6.extRoot (TwE6InnerAbs.lD4 c))
        (w⁻¹ • kacE6.extRoot (TwE6InnerAbs.lD4 d)) = 0
      rw [iform_smul, kacE6_extRoot]
      exact TwE6InnerAbs.d4_hgram c d hcd h1 h2)
    (fun {F} _ c d h => TwE6InnerAbs.d4_frames w⁻¹ c d h) Nat.prime_two one_pos hq'
  rw [hs1, Nat.mul_one] at hmodel
  have hord : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = CFSG.Open.ordD 4 (2 ^ 1) :=
    (Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.1 rfl
  have hsimple : IsSimpleGroup (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
    have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus
      (K := K) (n := 4) (by omega)
    exact e.isSimpleGroup
  have h3dvd : 3 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
    rw [hord]
    unfold CFSG.Open.ordD
    decide
  have hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹ :=
    ⟨TwistTag.E6, rfl, Fr, hFr, fun g => by rw [hΦ]; rfl⟩
  have hinK : twistInner (kernelRoots (rootCharHom a))
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by rw [← hker]; exact hinρ
  have hperf := d4t2_fixedSpinPerfect S hS hAlg (l := 2) (f := 1) Nat.prime_two one_pos hq'
    (by norm_num) h3 (by norm_num) haT hap hall hinK
  have hR : rationalRoots S.ρ (rootCharHom a) i = kernelRoots (rootCharHom a) := by
    ext γ
    constructor
    · rintro ⟨n, δ, hδ, rfl⟩
      rw [← hker]
      induction n with
      | zero => exact hδ
      | succ n ih => rw [Function.iterate_succ_apply']; exact hρst _ ih
    · intro hγ
      exact ⟨0, γ, by rw [hker]; exact hγ, rfl⟩
  set U := rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) with hU
  set P := U ⊓ S.D.model with hP
  have hPΓ : P ≤ S.Γ := by
    have h1 : P ≤ S.D.model := inf_le_right
    rw [← hperf]
    exact Subgroup.commutator_mono h1 h1
  have hΓm : S.Γ ≤ S.D.model := commutator_le_self_of_subgroup S.D.model
  have hspan : rationalSpan S.ρ S.Γ (rootCharHom a) i = P := by
    unfold rationalSpan
    rw [hR]
    exact le_antisymm (inf_le_inf_left _ hΓm) (le_inf inf_le_left hPΓ)
  have hRP : rationalComponent S.ρ S.Γ (rootCharHom a) i = P := by
    unfold rationalComponent
    rw [hspan]
    exact hperf
  have hRperf : ⁅rationalComponent S.ρ S.Γ (rootCharHom a) i,
      rationalComponent S.ρ S.Γ (rootCharHom a) i⁆ =
        rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [hRP]
    exact hperf
  refine ⟨hker, hR, ⟨(Subgroup.isPerfect_iff.2 hRperf).commutator_eq_top, hsimple⟩, h3dvd⟩

theorem d4_component (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) (hq2 : S.D.q = 2)
    (hAlg : S.IsAlgebraic) (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a b : Fin Tag.E6.rank → Lˣ} (haT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    (hab : kernelRoots (rootCharHom a) ⊆ kernelRoots (rootCharHom b)) :
    ∃ J : Subgroup (ModGL Tag.E6 L),
      CFSG.Open.IsSubnormal J (S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 L)) ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.E6 b} : Set (ModGL Tag.E6 L))) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  classical
  obtain ⟨β₀, hβ₀⟩ : (kernelRoots (rootCharHom a)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hall]; norm_num)
  set i : KernelComponent (rootCharHom a) :=
    (⟦⟨β₀, hβ₀⟩⟧ : KernelComponent (rootCharHom a)) with hi
  obtain ⟨hker, hRK, hq, h3d⟩ := d4_rational_quasisimple S hFr hΦ hq2 hAlg hρ h3 haT hap hall i
  refine ⟨rationalComponent S.ρ S.Γ (rootCharHom a) i, ?_, hq, h3d⟩
  obtain ⟨hKNa, hKsub⟩ := langSubnormal_of_mem_torus S haT i
  have hKsub' : CFSG.Open.IsSubnormal (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 L))) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hKNa).2 hKsub
  have hKb := hKsub'.inf (Subgroup.centralizer ({rootDiagUnit Tag.E6 b} : Set (ModGL Tag.E6 L)))
  have hKC : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      Subgroup.centralizer ({rootDiagUnit Tag.E6 b} : Set (ModGL Tag.E6 L)) := by
    have h1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
      Subgroup.commutator_le_self _
    have h2 : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤
        rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) := inf_le_left
    have hR : rationalRoots S.ρ (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) := hRK.subset
    exact h1.trans (h2.trans (rootSpan_le_centralizer b (hR.trans hab)))
  rw [inf_eq_left.2 hKC] at hKb
  exact hKb

end D4

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
