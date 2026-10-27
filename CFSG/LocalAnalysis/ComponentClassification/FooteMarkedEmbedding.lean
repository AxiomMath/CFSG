module

public import CFSG.LocalAnalysis.ComponentClassification.FooteTopExclusionMarkedSwap
public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedEmbeddingCover
public import CFSG.LocalAnalysis.ComponentClassification.TBLitComponents
public import CFSG.Quasithin.Background.F7TwoInvL2OddUnipGen
public import CFSG.Quasithin.Background.HA7
public import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.Open
open scoped commutatorElement
open CFSG.ComponentClassification.FooteMarked
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

theorem footeCounterexample_familyType {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L) : FooteFamilyType L :=
  hce.1.2.2.2.2.1

theorem footeFamilyType_top_simple {L : Subgroup G} (hFT : FooteFamilyType L) :
    IsSimpleGroup (L ⧸ Open.fusionZStar L) := by
  rcases hFT with h | ⟨p, f, hp, hp2, hf, h5, hLM⟩
  · let e := Classical.choice h
    haveI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hLM

theorem footeFamilyType_top_nonabelian {L : Subgroup G} (hFT : FooteFamilyType L) :
    ∃ a b : L ⧸ Open.fusionZStar L, a * b ≠ b * a := by
  rcases hFT with h | ⟨p, f, hp, hp2, hf, h5, hLM⟩
  · let e := Classical.choice h
    obtain ⟨a, b, hab⟩ : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact CFSG.Quasithin.H.A7.not_comm_A7 h
    exact ⟨e.symm a, e.symm b, fun h => hab (by
      simpa using congrArg (fun x => e x) h)⟩
  · have hSCM := hLM.statedClassicalModel (by decide)
    obtain ⟨-, F, hField, hFinite, hF, he⟩ := hSCM
    let e := Classical.choice he
    letI := hField
    letI := hFinite
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      omega
    obtain ⟨x, y, hxy⟩ := CFSG.Quasithin.F7Two.psl2_nonabelian (K := F)
    let e' : (L ⧸ Open.fusionZStar L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    exact ⟨e'.symm x, e'.symm y, fun h => hxy (by
      simpa using congrArg (fun z => e' z) h)⟩

theorem footeFamilyType_outer_solvable {L : Subgroup G} (hFT : FooteFamilyType L) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (L ⧸ Open.fusionZStar L)) := by
  rcases hFT with h | ⟨p, f, hp, hp2, hf, h5, hLM⟩
  · let e := Classical.choice h
    exact CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_solvable_of_equiv_outside_six
      (Or.inr (by norm_num)) e
  · have hSCM := hLM.statedClassicalModel (by decide)
    obtain ⟨-, F, hField, hFinite, hF, he⟩ := hSCM
    letI := hField
    letI := hFinite
    let e := Classical.choice he
    let e' : (L ⧸ Open.fusionZStar L) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.outer_solvable_of_equiv F e'

theorem footeSwapSetting_outer_solvable {t : G} {L : Subgroup G} {𝓢 : Set (Subgroup G)}
    (hset : FooteSwapSetting G t L 𝓢) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (L ⧸ Open.fusionZStar L)) :=
  footeFamilyType_outer_solvable (footeCounterexample_familyType hset.2.1)

theorem footeFamilyType_top_rank {L : Subgroup G} (hFT : FooteFamilyType L) :
    2 ≤ CFSG.pRank 2 (L ⧸ Open.fusionZStar L) := by
  haveI : IsSimpleGroup (L ⧸ Open.fusionZStar L) := footeFamilyType_top_simple hFT
  have hq : CFSG.IsQuasisimple (L ⧸ Open.fusionZStar L) :=
    CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup
      (footeFamilyType_top_nonabelian hFT)
  have hcenter : Odd (Nat.card (Subgroup.center (L ⧸ Open.fusionZStar L))) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup
      (footeFamilyType_top_nonabelian hFT)]
    simp
  exact CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq hcenter

theorem footeSwapSetting_top_rank {t : G} {L : Subgroup G} {𝓢 : Set (Subgroup G)}
    (hset : FooteSwapSetting G t L 𝓢) :
    2 ≤ CFSG.pRank 2 (L ⧸ Open.fusionZStar L) :=
  footeFamilyType_top_rank (footeCounterexample_familyType hset.2.1)

theorem footeSwapSetting_top_simple {t : G} {L : Subgroup G} {𝓢 : Set (Subgroup G)}
    (hset : FooteSwapSetting G t L 𝓢) : IsSimpleGroup (L ⧸ Open.fusionZStar L) :=
  footeFamilyType_top_simple (footeCounterexample_familyType hset.2.1)

theorem footeSwapSetting_top_nonabelian {t : G} {L : Subgroup G} {𝓢 : Set (Subgroup G)}
    (hset : FooteSwapSetting G t L 𝓢) :
    ∃ a b : L ⧸ Open.fusionZStar L, a * b ≠ b * a :=
  footeFamilyType_top_nonabelian (footeCounterexample_familyType hset.2.1)

theorem footeSwapSetting_kProper {t : G} {L : Subgroup G} {𝓢 : Set (Subgroup G)}
    (hset : FooteSwapSetting G t L 𝓢) : CFSG.Assembly.KProper Blueprint.Catalog G :=
  hset.2.1.1.1

theorem footeSwapSetting_isomorphicFamily {t : G} {L : Subgroup G} {𝓢 : Set (Subgroup G)}
    (hset : FooteSwapSetting G t L 𝓢) :
    FooteMarked.IsomorphicFamily 𝓢 (L ⧸ Open.fusionZStar L) :=
  hset.2.2.2.2.1

@[expose] def MarkedFusionControl (S : Set (Subgroup G)) (T : Type*) [Group T]
    (M : Subgroup G) : Prop :=
  ∀ K ∈ markedComponents S T M, ∀ K' ∈ markedComponents S T M, ∀ t g : G,
    (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G →
    (∀ a ∈ K ⊔ oddCoreIn (markedLayer S T M),
      t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn (markedLayer S T M)) →
    (∀ a ∈ K' ⊔ oddCoreIn (markedLayer S T M),
      (g⁻¹ * t * g)⁻¹ * a⁻¹ * (g⁻¹ * t * g) * a ∈ oddCoreIn (markedLayer S T M)) →
    g ∈ M

@[expose] def MarkedCoverControl (S : Set (Subgroup G)) (T : Type*) [Group T]
    (M : Subgroup G) : Prop :=
  ∀ K ∈ markedComponents S T M, ∀ (g : G) (X : Subgroup G),
    X ≤ conjugate M g →
    (∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (markedLayer S T M), a = x * o) → g ∈ M

theorem markedCount_conjugate {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) (M : Subgroup G) (g : G) :
    markedCount S T (conjugate M g) = markedCount S T M := by
  let e : ↥(markedComponents S T M) ≃ ↥(markedComponents S T (conjugate M g)) :=
  { toFun := fun K => ⟨conjugate K.1 g, mem_markedComponents_conjugate (hFam := hFam) K.2 g⟩
    invFun := fun J => ⟨conjugate J.1 g⁻¹, by
      have h := mem_markedComponents_conjugate (hFam := hFam) J.2 g⁻¹
      rwa [UnbalancedLayer.conjugate_conjugate, mul_inv_cancel, conjugate_one] at h⟩
    left_inv := fun K => by
      apply Subtype.ext
      change conjugate (conjugate K.1 g) g⁻¹ = K.1
      rw [UnbalancedLayer.conjugate_conjugate, mul_inv_cancel, conjugate_one]
    right_inv := fun J => by
      apply Subtype.ext
      change conjugate (conjugate J.1 g⁻¹) g = J.1
      rw [UnbalancedLayer.conjugate_conjugate]
      simp }
  have hcard : Nat.card ↥(markedComponents S T (conjugate M g)) =
      Nat.card ↥(markedComponents S T M) := (Nat.card_congr e).symm
  simpa [markedCount, Nat.card_coe_set_eq] using hcard

theorem card_baseKernel_conjugate {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) (M : Subgroup G) (g : G) :
    Nat.card (baseKernel S T (conjugate M g)) = Nat.card (baseKernel S T M) := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  have hD' : (markedLayer S T M).map φ.toMonoidHom = markedLayer S T (M.map φ.toMonoidHom) := by
    simpa [φ, CFSG.conjugate] using markedLayer_conjugate_general hFam M g
  have hbase : baseKernel S T (conjugate M g) = Subgroup.map φ.toMonoidHom (baseKernel S T M) := by
    change (oddTwoCoreIn (Subgroup.map φ.toMonoidHom M) ⊔
        twoLayerIn (Subgroup.map φ.toMonoidHom M)) ⊓
        coreActionKernel (markedLayer S T (Subgroup.map φ.toMonoidHom M)) =
      Subgroup.map φ.toMonoidHom
        ((oddTwoCoreIn M ⊔ twoLayerIn M) ⊓ coreActionKernel (markedLayer S T M))
    have hO : Subgroup.map φ.toMonoidHom (oddTwoCoreIn M) = oddTwoCoreIn (Subgroup.map φ.toMonoidHom M) := by
      simpa using Sol76.map_oddTwoCoreIn (φ := φ) M
    have hL : Subgroup.map φ.toMonoidHom (twoLayerIn M) = twoLayerIn (Subgroup.map φ.toMonoidHom M) := by
      simpa using Sol76.map_twoLayerIn (φ := φ) M
    have hK : Subgroup.map φ.toMonoidHom (coreActionKernel (markedLayer S T M)) =
        coreActionKernel (Subgroup.map φ.toMonoidHom (markedLayer S T M)) := by
      simpa using Sol76.map_coreActionKernel (φ := φ) _
    rw [Subgroup.map_inf_eq (H := oddTwoCoreIn M ⊔ twoLayerIn M)
        (K := coreActionKernel (markedLayer S T M)) (f := φ.toMonoidHom) φ.injective,
      Subgroup.map_sup, hO, hL, hK, hD']
  rw [hbase]
  exact (Nat.card_congr (MulEquiv.subgroupMap φ (baseKernel S T M)).toEquiv).symm

theorem balanced_conjugate {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) {M : Subgroup G} (hBal : Balanced S T M) (g : G) :
    Balanced S T (conjugate M g) := by
  obtain ⟨h2, h3 | heven⟩ := hBal
  · refine ⟨?_, Or.inl ?_⟩
    · rw [markedCount_conjugate hFam]
      exact h2
    · rw [markedCount_conjugate hFam]
      exact h3
  · refine ⟨?_, Or.inr ?_⟩
    · rw [markedCount_conjugate hFam]
      exact h2
    · rw [card_baseKernel_conjugate hFam]
      exact heven

theorem mem_coreActionKernel_of_centralizes_mod {D K : Subgroup G}
    (hK : IsTwoComponentIn K D) {t : G} (htD : t⁻¹ ∈ Subgroup.normalizer (D : Set G))
    (htK : ∀ a ∈ K, t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn D)
    (hinv : ∃ b ∈ K, orderOf b = 2) :
    t ∈ UnbalancedLayer.coreActionKernel K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' : Subgroup G := K.map (MulAut.conj t⁻¹).toMonoidHom with hK'def
  have hK'c : IsTwoComponentIn K' D := isTwoComponentIn_map_conj hK htD
  have hK'le : K' ≤ oddCoreIn D ⊔ K := by
    rintro _ ⟨a, ha, rfl⟩
    have e : (MulAut.conj t⁻¹).toMonoidHom a = t⁻¹ * a * t * a⁻¹ * a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e]
    refine mul_mem (mem_sup_left ?_) (mem_sup_right ha)
    have h := htK a⁻¹ (inv_mem ha)
    rwa [inv_inv] at h
  have hinv' : ∃ b ∈ K', orderOf b = 2 := by
    obtain ⟨b, hb, hb2⟩ := hinv
    refine ⟨(MulAut.conj t⁻¹).toMonoidHom b, mem_map_of_mem _ hb, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    exact hb2
  have hK'K : K' = K := eq_of_le_oddCoreIn_sup hK'c hK hK'le hinv'
  have htN' : t⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr hK'K
  have htN : t ∈ Subgroup.normalizer (K : Set G) := by simpa using inv_mem htN'
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨htN, fun j hj => ?_⟩
  have h1 : j⁻¹ * t⁻¹ * j * t ∈ oddCoreIn D := by
    have h := inv_mem (htK j hj)
    rwa [show (t⁻¹ * j⁻¹ * t * j)⁻¹ = j⁻¹ * t⁻¹ * j * t by group] at h
  have h2 : j⁻¹ * t⁻¹ * j * t ∈ K := by
    have h3 : t⁻¹ * j * t ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp htN' j).mp hj
      simpa using this
    rw [show j⁻¹ * t⁻¹ * j * t = j⁻¹ * (t⁻¹ * j * t) by group]
    exact mul_mem (inv_mem hj) h3
  have hmem : j⁻¹ * t⁻¹ * j * t ∈ K ⊓ oddCoreIn D := mem_inf.mpr ⟨h2, h1⟩
  rw [inf_oddCoreIn_eq hK] at hmem
  simpa [oddCoreIn] using hmem

theorem two_le_open_pRank_of_markedFactor {S : Set (Subgroup G)} {T : Type*} [Group T]
    [Finite T] {M K : Subgroup G} (hK : K ∈ markedComponents S T M)
    (hTrank : 2 ≤ CFSG.pRank 2 T) : 2 ≤ Open.pRank 2 K :=
  two_le_pRank_of_marked hK.2 hTrank

theorem markedFusionControl_of_cover_of_kernel
    {S : Set (Subgroup G)} {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hFam : IsomorphicFamily S T) (hTrank : 2 ≤ CFSG.pRank 2 T)
    {M : Subgroup G}
    (hCpure : ∀ K ∈ markedComponents S T M, ∀ x ∈ K, orderOf x = 2 →
      centralizer ({x} : Set G) ≤ M)
    (hcover : MarkedCoverControl S T M) : MarkedFusionControl S T M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro K hK K' hK' t g ht htZ htK htK'
  set D : Subgroup G := markedLayer S T M with hD
  have hKD : K ≤ D := le_sSup hK
  have hK'D : K' ≤ D := le_sSup hK'
  have hDM : D ≤ M := markedLayer_le S T M
  have hKtwo : IsTwoComponentIn K D := isTwoComponentIn_of_le hK.1 hKD hDM
  have hK'two : IsTwoComponentIn K' D := isTwoComponentIn_of_le hK'.1 hK'D hDM
  obtain ⟨b, hbK, hb2⟩ := exists_orderOf_eq_two_of_pRank
    (by have := two_le_open_pRank_of_markedFactor hK hTrank; omega :
      1 ≤ Open.pRank 2 K)
  obtain ⟨b', hb'K', hb'2⟩ := exists_orderOf_eq_two_of_pRank
    (by have := two_le_open_pRank_of_markedFactor hK' hTrank; omega :
      1 ≤ Open.pRank 2 K')
  obtain ⟨k, hk⟩ := ht
  have htM : t ∈ M :=
    mem_of_centralizes_quotient hKD hDM hbK hb2 (hCpure K hK b hbK hb2) hk htK
  have hk' : (g⁻¹ * t * g) ^ (2 ^ k) = 1 := by
    rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hk]
    group
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ one_mem _)
  have ht'1 : g⁻¹ * t * g ≠ 1 := fun h => ht1 (by
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have htgM : g⁻¹ * t * g ∈ M :=
    mem_of_centralizes_quotient hK'D hDM hb'K' hb'2 (hCpure K' hK' b' hb'K' hb'2) hk' htK'
  have htD : t ∈ Subgroup.normalizer (D : Set G) := markedLayer_le_normalizer hFam M htM
  have htKernel : t ∈ UnbalancedLayer.coreActionKernel K :=
    mem_coreActionKernel_of_centralizes_mod hKtwo (inv_mem htD)
      (fun a ha => htK a (mem_sup_left ha)) ⟨b, hbK, hb2⟩
  have hker : oddCoreIn (centralizer ({t} : Set G)) ⊔
      twoLayerIn (centralizer ({t} : Set G)) ≤ M :=
    oddCore_sup_twoLayerIn_centralizer_le_of_marked_topRank hFam hK.1 hK.2
      (hCpure K hK) hk ht1 htKernel hTrank
  have hker_g : oddCoreIn (centralizer ({g⁻¹ * t * g} : Set G)) ⊔
      twoLayerIn (centralizer ({g⁻¹ * t * g} : Set G)) ≤ conjugate M g := by
    have eO : (oddCoreIn (centralizer ({t} : Set G))).map
        (MulAut.conj g⁻¹).toMonoidHom =
        oddCoreIn (centralizer ({g⁻¹ * t * g} : Set G)) := by
      rw [show (oddCoreIn (centralizer ({t} : Set G))).map
          (MulAut.conj g⁻¹).toMonoidHom =
          conjugate (oddCoreIn (centralizer ({t} : Set G))) g from rfl,
        oddCoreIn_conjugate]
      change oddCoreIn ((centralizer ({t} : Set G)).map
        (MulAut.conj g⁻¹).toMonoidHom) = oddCoreIn (centralizer ({g⁻¹ * t * g} : Set G))
      rw [Subgroup.map_conj_centralizer_singleton, inv_inv]
    have eL : (twoLayerIn (centralizer ({t} : Set G))).map
        (MulAut.conj g⁻¹).toMonoidHom =
        twoLayerIn (centralizer ({g⁻¹ * t * g} : Set G)) := by
      rw [map_twoLayerIn]
      change twoLayerIn ((centralizer ({t} : Set G)).map
        (MulAut.conj g⁻¹).toMonoidHom) = twoLayerIn (centralizer ({g⁻¹ * t * g} : Set G))
      rw [Subgroup.map_conj_centralizer_singleton, inv_inv]
    have hmap := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hker
    rw [Subgroup.map_sup, eO, eL] at hmap
    simpa only [conjugate] using hmap
  let U : Subgroup G := zpowers (g⁻¹ * t * g)
  have hU2 : IsPGroup 2 U := isPGroup_zpowers_of_pow hk'
  have hUne : U ≠ ⊥ := fun h => ht'1 (zpowers_eq_bot.mp h)
  have ht'D : g⁻¹ * t * g ∈ Subgroup.normalizer (D : Set G) :=
    markedLayer_le_normalizer hFam M htgM
  have ht'Kernel : g⁻¹ * t * g ∈ UnbalancedLayer.coreActionKernel K' :=
    mem_coreActionKernel_of_centralizes_mod hK'two (inv_mem ht'D)
      (fun a ha => htK' a (mem_sup_left ha)) ⟨b', hb'K', hb'2⟩
  have hUK' : U ≤ UnbalancedLayer.coreActionKernel K' := zpowers_le.mpr ht'Kernel
  obtain ⟨H, hHcomp, -, hHclosure, hHcover⟩ :=
    markedST_of_isomorphicFamily hFam K' hK'.2 U hU2 hUK' hUne
  let C : Subgroup G := centralizer (U : Set G)
  let Y : Subgroup G := fixedShadow K' U
  have hCU : C = centralizer ({g⁻¹ * t * g} : Set G) := by
    dsimp only [C, U]
    exact UnbalancedLayer.centralizer_zpowers_eq _
  have hH2 : IsTwoComponentIn H C := hHcomp
  have hYC : Y ≤ C := (fixedShadow_le_inf K' U).trans inf_le_right
  have hYH : Y ≤ H := by
    rw [← hHclosure]
    exact FooteLit.le_conjClosure Y (twoLayerIn C)
  have hYL : Y ≤ twoLayerIn C := hYH.trans (le_twoLayerIn_of_isTwoComponentIn hH2)
  have hYg : Y ≤ conjugate M g := by
    have h1 : Y ≤ twoLayerIn (centralizer ({g⁻¹ * t * g} : Set G)) := by rwa [hCU] at hYL
    exact h1.trans ((le_sup_right : _ ≤ oddCoreIn _ ⊔ _).trans hker_g)
  have hK'q : IsQuasisimple (K' ⧸ pPrimeCore 2 K') := hK'.2.quotient_quasisimple hFam
  obtain ⟨hcoverK', -, -⟩ := fixedShadow_cover_quotient hK'q hU2 hUK'
  have hcov : ∀ a ∈ K', ∃ x ∈ Y, ∃ o ∈ oddCoreIn D, a = x * o := by
    intro a ha
    have ha' : a ∈ Y ⊔ oddCoreIn K' := by rw [hcoverK']; exact ha
    have hYO : Y ≤ Subgroup.normalizer (oddCoreIn K' : Set G) :=
      (fixedShadow_le K' U).trans (le_normalizer_oddCoreIn K')
    have ha'' : a ∈ oddCoreIn K' ⊔ Y := by rwa [sup_comm]
    obtain ⟨o, ho, y, hy, rfl⟩ := exists_mul_of_mem_sup_normalizer hYO ha''
    refine ⟨y, hy, y⁻¹ * o * y, ?_, by group⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hYO (inv_mem hy)) o).mp ho
    rw [inv_inv] at h1
    exact oddCoreIn_le_of_isTwoComponentIn hK'two h1
  exact hcover K' hK' g Y hYg hcov

theorem false_of_markedEmbedding_of_controls
    {S : Set (Subgroup G)} {T : Type*} [Group T] [Finite T]
    (hFam : FooteMarked.IsomorphicFamily S T)
    (hTrank : 2 ≤ CFSG.pRank 2 T)
    {M : Subgroup G} (hMtop : M ≠ ⊤) (hMbal : FooteMarked.Balanced S T M)
    (hDnorm : Subgroup.normalizer (FooteMarked.markedLayer S T M : Set G) = M)
    (hfusion : MarkedFusionControl S T M) (hcover : MarkedCoverControl S T M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin ↥(FooteMarked.markedComponents S T M)
  let K : Fin r → Subgroup G :=
    fun i => ((e.symm i : ↥(FooteMarked.markedComponents S T M)) : Subgroup G)
  have hKiff : ∀ J, J ∈ FooteMarked.markedComponents S T M ↔ ∃ i, K i = J := by
    intro J
    refine ⟨fun hJ => ⟨e ⟨J, hJ⟩, ?_⟩, ?_⟩
    · simp [K]
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
  have hKinj : Function.Injective K := fun i j h =>
    e.symm.injective (Subtype.ext h)
  have hKmem : ∀ i, K i ∈ FooteMarked.markedComponents S T M := fun i =>
    (hKiff (K i)).mpr ⟨i, rfl⟩
  have hcard : r = FooteMarked.markedCount S T M := by
    have h1 : Nat.card ↥(FooteMarked.markedComponents S T M) = r := by
      rw [Nat.card_congr e]
      simp
    rw [FooteMarked.markedCount, ← Nat.card_coe_set_eq, ← h1]
  have hr2 : 2 ≤ r := by
    rw [hcard]
    exact hMbal.1
  set D : Subgroup G := FooteMarked.markedLayer S T M with hD
  have hKD : ∀ i, K i ≤ D := fun i => le_sSup (hKmem i)
  have hDgen : ⨆ i, K i = D := by
    apply le_antisymm
    · exact iSup_le fun i => le_sSup (hKmem i)
    · refine sSup_le fun J hJ => ?_
      obtain ⟨i, rfl⟩ := (hKiff J).mp hJ
      exact le_iSup K i
  have hDM : D ≤ M := FooteMarked.markedLayer_le S T M
  have hKtwo : ∀ i, IsTwoComponentIn (K i) D := fun i =>
    isTwoComponentIn_of_le (hKmem i).1 (hKD i) hDM
  have hcommD : ∀ i j, i ≠ j → ⁅K i, K j⁆ ≤ oddCoreIn D := by
    intro i j hij
    have hne : K i ≠ K j := fun h => hij (hKinj h)
    exact (TBLit.commutator_le_oddCoreIn_of_ne (hKtwo i).1 (hKtwo j).1
      (hKtwo i).2 (hKtwo j).2 hne).trans (oddCoreIn_le_of_isTwoComponentIn (hKtwo i))
  set Abar : Fin r → Subgroup (↥D ⧸ aschbacherThm5OddCore ↥D) :=
    fun i => ((K i).subgroupOf D).map (QuotientGroup.mk' _) with hAbar
  have hpre : ∀ i, aschbacherThm5Preimage D (Abar i) = K i ⊔ oddCoreIn D := fun i =>
    aschbacherThm5Preimage_map_subgroupOf (hKD i)
  have hcore : aschbacherThm5Core D = oddCoreIn D := aschbacherThm5Core_eq_oddCoreIn D
  have hq : ∀ i, CFSG.IsQuasisimple ↥(Abar i) := fun i =>
    isQuasisimple_image (hKtwo i) _ (aschbacherThm5OddCore_eq_pPrimeCore' _)
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x := by
    rintro i j hij _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, aschbacherThm5OddCore_eq_pPrimeCore']
    have hmem : ((a * b)⁻¹ * (b * a) : D) ∈ ((oddCoreIn D).subgroupOf D) := by
      rw [mem_subgroupOf]
      have h3 : (((a * b)⁻¹ * (b * a) : D) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv, mul_inv_rev]
        group
      rw [h3]
      exact hcommD j i (Ne.symm hij) (commutator_mem_commutator (inv_mem hb) (inv_mem ha))
    rw [mem_subgroupOf] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    rwa [Subtype.ext hyx] at hy
  have hdistinct : Function.Injective Abar := by
    intro i j hij
    by_contra hne
    obtain ⟨-, -, a, b, hab⟩ := hq i
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have hbj : (b : ↥D ⧸ aschbacherThm5OddCore ↥D) ∈ Abar j := by rw [← hij]; exact b.2
    exact Subtype.ext (hcomm i j hne a a.2 b hbj)
  have hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i) := fun i =>
    ⟨1, fun _ => Abar i, one_pos,
      fun _ => ⟨le_rfl, (hq i).1.commutator_eq_top, (hq i).2.1⟩,
      fun l m hlm => absurd (Subsingleton.elim l m) hlm, iSup_const⟩
  have hgen : ⨆ i, Abar i = ⊤ := iSup_map_subgroupOf_eq_top hKD hDgen _
  have hperm : ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j) := by
    intro h hh i
    simp only [hpre]
    exact exists_map_conj_eq hKtwo hDgen hh i
  have hrank : ∀ i, 2 ≤ CFSG.pRank 2 (aschbacherThm5Preimage D (Abar i)) := by
    intro i
    rw [hpre]
    rw [show CFSG.pRank 2 ↥(K i ⊔ oddCoreIn D) = Open.pRank 2 (K i ⊔ oddCoreIn D) from
      (by rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup])]
    exact (two_le_open_pRank_of_markedFactor (hKmem i) hTrank).trans
      (SectionRank.pRank_mono (p := 2) (by norm_num)
        (le_sup_left : K i ≤ K i ⊔ oddCoreIn D))
  have hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) →
      t ∉ Subgroup.center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) →
      g ∈ Subgroup.normalizer (D : Set G) := by
    intro i j t g ht htZ hti htj
    rw [hcore, hpre] at hti htj
    have hM := hfusion (K i) (hKmem i) (K j) (hKmem j) t g ht htZ hti htj
    rw [hDnorm]
    exact hM
  have hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) →
      g ∈ Subgroup.normalizer (D : Set G) := by
    intro i g X hX hXa
    rw [hcore, hpre] at hXa
    have hX' : X ≤ conjugate M g := by
      rwa [hDnorm] at hX
    have hM := hcover (K i) (hKmem i) g X hX'
      (fun a ha => hXa a (mem_sup_left ha))
    rw [hDnorm]
    exact hM
  have hH : Subgroup.normalizer (D : Set G) ≠ ⊤ := by
    intro htop
    apply hMtop
    rw [← hDnorm, htop]
  exact CFSG.ComponentClassification.Sol76.false_of_semisimple_family hr2 Abar hdistinct
    hsemisimple hcomm hgen hperm hi hii hH hrank

theorem false_of_markedEmbedding_of_cover
    {S : Set (Subgroup G)} {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hFam : FooteMarked.IsomorphicFamily S T)
    (hTrank : 2 ≤ CFSG.pRank 2 T)
    {M : Subgroup G} (hMtop : M ≠ ⊤) (hMbal : FooteMarked.Balanced S T M)
    (hDnorm : Subgroup.normalizer (FooteMarked.markedLayer S T M : Set G) = M)
    (hCpure : ∀ K ∈ FooteMarked.markedComponents S T M, ∀ x ∈ K, orderOf x = 2 →
      centralizer ({x} : Set G) ≤ M)
    (hcover : MarkedCoverControl S T M) : False :=
  false_of_markedEmbedding_of_controls hFam hTrank hMtop hMbal hDnorm
    (markedFusionControl_of_cover_of_kernel hFam hTrank hCpure hcover) hcover

theorem footeMarkedEmbeddingExclusion_of_absorption
    (hA : FooteMarkedAbsorption) : FooteMarkedEmbeddingExclusion := by
  intro G _ _ t L 𝓢 hset M hMtop hMbal hDnorm hCpure
  let T := L ⧸ Open.fusionZStar L
  have hFam : FooteMarked.IsomorphicFamily 𝓢 T := footeSwapSetting_isomorphicFamily hset
  haveI : IsSimpleGroup T := footeSwapSetting_top_simple hset
  have hTnonab : ∃ a b : T, a * b ≠ b * a := footeSwapSetting_top_nonabelian hset
  have hTrank : 2 ≤ CFSG.pRank 2 T := footeSwapSetting_top_rank hset
  have hOutT : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) :=
    footeSwapSetting_outer_solvable hset
  have hAbs : FooteMarked.MarkedAbsorptionLocal 𝓢 T :=
    fun H P hHne hHbal hP hPH hker =>
      hA G t L 𝓢 hset H P hHne hHbal hP hPH hker
  exact false_of_markedEmbedding_of_cover hFam hTrank hMtop hMbal hDnorm hCpure
    (FooteMarked.markedCoverControl_of_absorption (S := 𝓢) (T := T)
      hFam hAbs hTrank hTnonab hOutT hMtop hMbal
      (fun g => balanced_conjugate hFam hMbal g) hDnorm hCpure)

end CFSG.ComponentClassification.FooteLit
