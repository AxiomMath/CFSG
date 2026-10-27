module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerCases
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerFrame
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Purity
public import CFSG.LieType.SeitzGeneration.ExcHighThree.RegularSolvable
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree TauCeti
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4

set_option linter.unusedSectionVars false

namespace SeitzExcOpenRest8Aux

section Bridge

variable {G : Type*} [Group G]

theorem seitzHyperGamma_conj_le_hyperClosure (E₀ : Subgroup G) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 (E₀.map (MulAut.conj : G →* MulAut G)) ≤
      hyperClosure 3 ⊤ E₀ := by
  refine iSup₂_le fun F' hF' k hk => ?_
  apply Subgroup.subset_closure
  refine ⟨Subgroup.mem_top k, E₀ ⊓ F'.comap MulAut.conj, inf_le_left, ?_, fun f hf => ?_⟩
  · rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
    exact hF'.2
  · have h1 : (MulAut.conj f) k = k := hk (MulAut.conj f) hf.2
    rw [MulAut.conj_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1

theorem conj_injective_of_center (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [← hZ, Subgroup.mem_center_iff]
  intro y
  have h := congrArg (fun φ : MulAut G => φ y) (MonoidHom.mem_ker.1 hx)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem map_conj_map_conj_inv' (E : Subgroup G) (g : G) :
    (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = E := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id E
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.id_apply]
  group

theorem hyperGen_of_two_closingFrames {E₀ P : Subgroup G} {e e' : G}
    (hgen : P ≤ Subgroup.closure {e, e'})
    (hsol : Group.IsSolvable ↥(Subgroup.centralizer (P : Set G))) {X X' : Subgroup G}
    (hcl : ExcHighThree.ClosingFrameAt e X) (hcl' : ExcHighThree.ClosingFrameAt e' X')
    (hX : X ≤ hyperClosure 3 ⊤ E₀) (hX' : X' ≤ hyperClosure 3 ⊤ E₀) : HyperGen 3 ⊤ E₀ := by
  rw [hyperGen_iff_le]
  by_cases hN : hyperClosure 3 ⊤ E₀ ≤ Subgroup.normalizer (X : Set G)
  · exfalso
    apply hcl'.nonsolvable
    refine hcl.normalizer_solvable X' (hX'.trans hN) ?_
    have hle : X' ⊓ X ≤ Subgroup.centralizer (P : Set G) := by
      intro y hy
      have hye : y * e = e * y := Subgroup.mem_centralizer_singleton_iff.1 (hcl.centralizes hy.2)
      have hye' : y * e' = e' * y :=
        Subgroup.mem_centralizer_singleton_iff.1 (hcl'.centralizes hy.1)
      have hPy : Subgroup.closure ({e, e'} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.2 hye.symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 hye'.symm
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact Subgroup.mem_centralizer_singleton_iff.1 (hPy (hgen hp))
    haveI := hsol
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  · exact (hcl.closing _ hX hN).ge

end Bridge

section SplitFrame

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KF4
open scoped MatrixGroups


variable {K : Type} [Field K]

theorem rootChar_mulSingle_one (ω : Kˣ) (α : Fin Tag.F4.rank → ℤ) :
    rootChar (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) α = ω ^ (α 1) := by
  unfold rootChar
  rw [Finset.prod_eq_single (1 : Fin Tag.F4.rank)]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem rootCharKernel_mulSingle_one {ω : Kˣ} (hω : orderOf ω = 3) :
    rootCharKernel (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) = cosetRoots Tag.F4 1 3 := by
  ext α
  simp only [rootCharKernel, cosetRoots, Set.mem_setOf_eq, rootChar_mulSingle_one]
  rw [← orderOf_dvd_iff_zpow_eq_one, hω]

theorem toralRootGroup_mulSingle_one {ω : Kˣ} (hω : orderOf ω = 3) :
    toralRootGroup Tag.F4 K (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) =
      torusGroup Tag.F4 K ⊔ XS K := by
  rw [toralRootGroup, rootCharKernel_mulSingle_one hω]

theorem xs_le_frameActSub {ψA ψB : SL(3, K) →* ModGL Tag.F4 K}
    {σA σB : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ} (hA : IsA2Frame ψA σA) (hB : IsA2Frame ψB σB)
    (hc : ∀ A B, Commute (ψA A) (ψB B))
    (hSA : {r | ∃ i j : Fin 3, i ≠ j ∧ r = σA i j} = S1set)
    (hSB : {r | ∃ i j : Fin 3, i ≠ j ∧ r = σB i j} = S2set) :
    XS K ≤ E6Three.frameActSub ψA ⊓ E6Three.frameActSub ψB := by
  have hrA : ψA.range = X1 K := by rw [hA.range, hSA]
  have hrB : ψB.range = X2 K := by rw [hB.range, hSB]
  rw [XS_eq, ← hrA, ← hrB]
  refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
  · rintro _ ⟨A, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.toGL A, fun s => ?_⟩
    rw [E6Three.conjSL_toGL, MulAut.conj_apply, map_mul, map_mul, map_inv]
  · rintro _ ⟨A, rfl⟩
    refine ⟨1, fun s => ?_⟩
    rw [map_one, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.2 (hc A s).eq
  · rintro _ ⟨B, rfl⟩
    refine ⟨1, fun s => ?_⟩
    rw [map_one, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.2 (hc s B).symm.eq
  · rintro _ ⟨B, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.toGL B, fun s => ?_⟩
    rw [E6Three.conjSL_toGL, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem toralRootGroup_le_frameActSub {ω : Kˣ} (hω : orderOf ω = 3)
    {ψA ψB : SL(3, K) →* ModGL Tag.F4 K}
    {σA σB : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ} (hA : IsA2Frame ψA σA) (hB : IsA2Frame ψB σB)
    (hc : ∀ A B, Commute (ψA A) (ψB B))
    (hSA : {r | ∃ i j : Fin 3, i ≠ j ∧ r = σA i j} = S1set)
    (hSB : {r | ∃ i j : Fin 3, i ≠ j ∧ r = σB i j} = S2set) :
    toralRootGroup Tag.F4 K (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) ≤
      E6Three.frameActSub ψA ⊓ E6Three.frameActSub ψB := by
  rw [toralRootGroup_mulSingle_one hω]
  refine sup_le ?_ (xs_le_frameActSub hA hB hc hSA hSB)
  intro g hg
  obtain ⟨b, rfl⟩ := CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup hg
  exact ⟨E6Three.rootDiagUnit_mem_frameActSub hA b, E6Three.rootDiagUnit_mem_frameActSub hB b⟩

theorem xs_le_centralizer_zSplit {ω : Kˣ} (hω : orderOf ω = 3) :
    XS K ≤ Subgroup.centralizer
      ({rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω)} : Set (ModGL Tag.F4 K)) := by
  refine rootSpan_le_centralizer_rootDiagUnit _ fun α hα => ?_
  rw [← rootCharKernel_mulSingle_one hω] at hα
  exact hα

theorem xs_le_hyperClosure [Finite K] (hK : Nat.card K % 3 = 1) (h4 : Nat.card K ≠ 4)
    {ω : Kˣ} (hω : orderOf ω = 3) {E₀ : Subgroup (adjointGroup Tag.F4 K)}
    (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3) (hz : zSplit K ω ∈ E₀) :
    frameIn (XS K) ≤ hyperClosure 3 ⊤ E₀ := by
  classical
  have h3 : 3 ∣ Nat.card K - 1 := by omega
  obtain ⟨ψA, ψB, σA, σB, hA, hB, hcomm, hSA, hSB⟩ := exists_splitFrame_F4' K
  have hrA : ψA.range = X1 K := by rw [hA.range, hSA]
  have hrB : ψB.range = X2 K := by rw [hB.range, hSB]
  have hXS : XS K ≤ adjointGroup Tag.F4 K := rootSpan_le_adjointGroup K _
  have hZ : Subgroup.center (adjointGroup Tag.F4 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj := conj_injective_of_center hZ
  set E : Subgroup (MulAut (adjointGroup Tag.F4 K)) := E₀.map MulAut.conj with hEdef
  have hEa : IsElemAbelian 3 E :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀ _
  have hEc : Nat.card E = 27 := by
    rw [hEdef, Subgroup.card_map_of_injective hinj, hc]
    norm_num
  have h3a : ∀ i, (Pi.mulSingle (1 : Fin Tag.F4.rank) ω : Fin Tag.F4.rank → Kˣ) i ^ 3 = 1 := by
    intro i
    by_cases hi : i = 1
    · subst hi
      simp only [Pi.mulSingle_eq_same]
      rw [← hω]
      exact pow_orderOf_eq_one ω
    · simp [Pi.mulSingle_eq_of_ne hi]
  have hcent : ∀ x ∈ E₀,
      (x : ModGL Tag.F4 K) ∈ toralRootGroup Tag.F4 K (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) := by
    intro x hx
    rw [← CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_F4_three K
      _ h3a, mem_toralCentralizer]
    refine ⟨x.2, ?_⟩
    have hzx : zSplit K ω * x = x * zSplit K ω :=
      congrArg Subtype.val (hE₀.1.is_comm.comm (⟨zSplit K ω, hz⟩ : E₀) ⟨x, hx⟩)
    have hzx' := congrArg Subtype.val hzx
    simp only [Subgroup.coe_mul] at hzx'
    change rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) * (x : ModGL Tag.F4 K) *
      (rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω))⁻¹ = x
    exact mul_inv_eq_of_eq_mul hzx'
  have hact := toralRootGroup_le_frameActSub hω hA hB hcomm hSA hSB
  have hzne : zSplit K ω ≠ 1 := (f4SplitFrame_of K hK ω hω).1
  have key : ∀ (ψ : SL(3, K) →* ModGL Tag.F4 K) (σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ),
      IsA2Frame ψ σ → ψ.range ≤ XS K →
      toralRootGroup Tag.F4 K (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) ≤ E6Three.frameActSub ψ →
      ψ.range ≤ (hyperClosure 3 ⊤ E₀).map (adjointGroup Tag.F4 K).subtype := by
    intro ψ σ hψ hψX hψact
    have hmem : ∀ s, ψ s ∈ adjointGroup Tag.F4 K := fun s => hXS (hψX ⟨s, rfl⟩)
    let ρ : SL(3, K) →* adjointGroup Tag.F4 K := ψ.codRestrict _ hmem
    have hρinj : Function.Injective ρ := fun s t h => hψ.injective (congrArg Subtype.val h)
    have hσ1 : MulAut.conj (zSplit K ω) ≠ 1 := by
      intro h
      exact hzne (hinj (h.trans (map_one _).symm))
    have hσρ : ∀ s, MulAut.conj (zSplit K ω) (ρ s) = ρ s := by
      intro s
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_singleton_iff.1
        (xs_le_centralizer_zSplit hω (hψX ⟨s, rfl⟩))
      show (zSplit K ω : ModGL Tag.F4 K) * ψ s * (zSplit K ω : ModGL Tag.F4 K)⁻¹ = ψ s
      exact mul_inv_eq_of_eq_mul h1.symm
    have hρact : ∀ ε ∈ E, ∃ γ : GL (Fin 3) K, ∀ s, ε (ρ s) = ρ (E6Three.conjSL γ s) := by
      rintro ε ⟨x, hx, rfl⟩
      obtain ⟨γ, hγ⟩ := hψact (hcent x hx)
      exact ⟨γ, fun s => Subtype.ext (hγ s)⟩
    have hle := E6Three.le_seitzHyperGamma_of_acts h3 h4 hEa hEc hρinj ⟨_, hz, rfl⟩ hσ1 hσρ hρact
    rintro _ ⟨s, rfl⟩
    exact ⟨ρ s, seitzHyperGamma_conj_le_hyperClosure E₀ (hle ⟨s, rfl⟩), rfl⟩
  have hXSle : XS K ≤ (hyperClosure 3 ⊤ E₀).map (adjointGroup Tag.F4 K).subtype := by
    rw [XS_eq, ← hrA, ← hrB]
    refine sup_le (key ψA σA hA ?_ fun g hg => (hact hg).1) (key ψB σB hB ?_ fun g hg => (hact hg).2)
    · rw [hrA]
      exact X1_le_XS K
    · rw [hrB]
      exact X2_le_XS K
  intro y hy
  obtain ⟨h, hh, hhy⟩ := hXSle (Subgroup.mem_subgroupOf.1 hy)
  have : h = y := Subtype.ext hhy
  exact this ▸ hh

theorem closingFrameAt_zSplit_xs [Finite K] (hK : Nat.card K % 3 = 1) {ω : Kˣ}
    (hω : orderOf ω = 3) : ClosingFrameAt (zSplit K ω) (frameIn (XS K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK4 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hXS : XS K ≤ adjointGroup .F4 K := rootSpan_le_adjointGroup K _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hy' : (y : ModGL .F4 K) ∈ XS K := hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (xs_le_centralizer_zSplit hω hy')
  · refine nonsolvable_frameIn hXS ?_
    intro hs
    haveI := hs
    haveI h2 : Group.IsSolvable ↥(X2 K) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective (X2_le_XS K))
    obtain ⟨hperf, -, a₀, b₀, hab⟩ := X2_quasisimple K
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
    haveI : Nontrivial ↥(X2 K) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
    exact (IsSolvable.commutator_lt_top_of_nontrivial (↥(X2 K))).ne hperf.commutator_eq_top
  · exact closing_of_twFrameClosing hXS
      ((frameClosing_iff Tag.F4 K _).1
        (frameClosing_of_detection_F4 K (by omega) (DetectF4.frameDetection_F4 K (by omega))))
  · exact normalizerSolvable_of_twFrame hXS
      ((frameNormalizerSolvable_iff Tag.F4 K _).1 (frameNormalizerSolvable_F4 K hK4))

theorem frame_conj_le_hyperClosure [Finite K] (hK : Nat.card K % 3 = 1) (h4 : Nat.card K ≠ 4)
    {ω : Kˣ} (hω : orderOf ω = 3) {E₀ : Subgroup (adjointGroup Tag.F4 K)}
    (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3) {e g : adjointGroup Tag.F4 K}
    (he : e ∈ E₀) (hg : g * e * g⁻¹ = zSplit K ω) :
    (frameIn (XS K)).map (MulAut.conj g⁻¹).toMonoidHom ≤ hyperClosure 3 ⊤ E₀ := by
  have hE₁a : IsElemAbelian 3 (E₀.map (MulAut.conj g).toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀ _
  have hE₁c : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]
  have hz : zSplit K ω ∈ E₀.map (MulAut.conj g).toMonoidHom := ⟨e, he, by rw [← hg]; rfl⟩
  have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
    (xs_le_hyperClosure hK h4 hω hE₁a hE₁c hz)
  refine h1.trans ?_
  have h2 := map_hyperClosure_le (p := 3) (⊤ : Subgroup (adjointGroup Tag.F4 K))
    (E₀.map (MulAut.conj g).toMonoidHom) g⁻¹
  rwa [map_conj_map_conj_inv'] at h2

end SplitFrame

end SeitzExcOpenRest8Aux

section F4Split

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8Aux


theorem hyperGen_F4_of_regularPlane {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    (h4 : Nat.card K ≠ 4) {E₀ : Subgroup (adjointGroup .F4 K)} (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) {P : Subgroup (adjointGroup .F4 K)} (hPE : P ≤ E₀)
    (hPc : Nat.card P = 3 ^ 2) (D : LangPlaneData .F4 K P)
    (hreg : ∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α → ¬ D.Kills α) : HyperGen 3 ⊤ E₀ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 := by
    have h3' : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units]; omega
    exact exists_prime_orderOf_dvd_card' 3 h3'
  have hPexp : ∀ x ∈ P, x ^ 3 = 1 := fun x hx => hE₀.2 x (hPE hx)
  obtain ⟨e, heP, e', he'P, he1, he'1, hgen⟩ := exists_gens_of_plane (p := 3) hPexp hPc
  obtain ⟨g, hg⟩ := f4PureSplit_holds K hK ω hω P hPexp hPc D hreg e heP he1
  obtain ⟨g', hg'⟩ := f4PureSplit_holds K hK ω hω P hPexp hPc D hreg e' he'P he'1
  have hcl := (closingFrameAt_zSplit_xs hK hω).conj g⁻¹
  rw [show g⁻¹ * zSplit K ω * g⁻¹⁻¹ = e by rw [← hg]; group] at hcl
  have hcl' := (closingFrameAt_zSplit_xs hK hω).conj g'⁻¹
  rw [show g'⁻¹ * zSplit K ω * g'⁻¹⁻¹ = e' by rw [← hg']; group] at hcl'
  exact hyperGen_of_two_closingFrames hgen (isSolvable_centralizer_of_regular D hreg) hcl hcl'
    (frame_conj_le_hyperClosure hK h4 hω hE₀ hc (hPE heP) hg)
    (frame_conj_le_hyperClosure hK h4 hω hE₀ hc (hPE he'P) hg')

end F4Split

section Residual


@[expose] def F4NonToralRegularPlane : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → ThreeScope LieTypeIndex.F4 K →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → IsEmpty (LangPlaneData .F4 K E₀) →
      ∃ P : Subgroup (adjointGroup .F4 K), P ≤ E₀ ∧ Nat.card P = 3 ^ 2 ∧
        ∃ D : LangPlaneData .F4 K P, ∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α → ¬ D.Kills α

end Residual

theorem card_ne_four_of_threeScope_F4 {K : Type} [Field K] [Finite K]
    (hs : ThreeScope LieTypeIndex.F4 K) : Nat.card K ≠ 4 := by
  obtain ⟨q, hv, hKq, hgood, -⟩ := hs
  intro h4
  have hpe : q.p ^ q.exponent = 4 := by rw [← PrimePower.card_def, ← hKq, h4]
  have hp2 : q.p = 2 := by
    have hdvd : q.p ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hpe]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
  have he2 : q.exponent = 2 := by
    rw [hp2] at hpe
    have : (2 : ℕ) ^ q.exponent = 2 ^ 2 := by rw [hpe]; norm_num
    exact Nat.pow_right_injective le_rfl this
  rcases hgood with hg | hg
  · apply hg
    refine Or.inr ⟨rfl, Or.inr (Or.inl ?_)⟩
    show q.p = 2 ∧ q.exponent = 2
    exact ⟨hp2, he2⟩
  · rcases hg with hg | hg | hg
    · have h3 : q.exponent = 3 := hg.2
      omega
    · exact hg
    · exact hg

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
