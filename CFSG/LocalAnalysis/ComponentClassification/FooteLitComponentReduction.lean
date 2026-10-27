module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitIsoTransport
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInitial
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSubgroupChain
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem ne_bot_of_isPComponent {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : IsPComponent 2 K) : K ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro rfl
  apply CatalogueBPrimeJoin.core_ne_top 2 _ hK
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x = 1 := Subtype.ext ((mem_bot).mp x.2)
  rw [hx]
  exact one_mem _

section Layer

variable {G₀ : Subgroup G} {t : G}

omit [Finite G] in
theorem normal_subgroupOf_sup_zpowers (htN : t ∈ normalizer (G₀ : Set G)) :
    (G₀.subgroupOf (G₀ ⊔ zpowers t)).Normal :=
  (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le le_normalizer ((zpowers_le).mpr htN))

omit [Finite G] in
theorem isComponent_subgroupOf_sup_zpowers (hG₀ : IsComponent G₀)
    (htN : t ∈ normalizer (G₀ : Set G)) : IsComponent (G₀.subgroupOf (G₀ ⊔ zpowers t)) :=
  ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm hG₀.1,
    (normal_subgroupOf_sup_zpowers htN).isSubnormal⟩

theorem isPComponent_subgroupOf_sup_zpowers (hG₀ : IsPComponent 2 G₀)
    (htN : t ∈ normalizer (G₀ : Set G)) : IsPComponent 2 (G₀.subgroupOf (G₀ ⊔ zpowers t)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 G₀ ⊤ le_top).mp
    (isPComponent_subgroupOf_top_iff'.mpr hG₀)
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 G₀ _ le_sup_left).mpr
    ⟨(normal_subgroupOf_sup_zpowers htN).isSubnormal, h.2.1, h.2.2⟩

theorem eq_of_isPComponent_sup_zpowers (hG₀ : IsComponent G₀)
    (htN : t ∈ normalizer (G₀ : Set G)) {K : Subgroup ↥(G₀ ⊔ zpowers t)}
    (hK : IsPComponent 2 K) : K = G₀.subgroupOf (G₀ ⊔ zpowers t) := by
  have hKp : ⁅K, K⁆ = K := by
    have : Group.IsPerfect K := CatalogueBAlternating.pComponent_perfect hK
    exact Subgroup.commutator_eq_self
  have hKG : K ≤ G₀.subgroupOf (G₀ ⊔ zpowers t) := by
    have hKmp : ⁅K.map (G₀ ⊔ zpowers t).subtype, K.map (G₀ ⊔ zpowers t).subtype⁆ =
        K.map (G₀ ⊔ zpowers t).subtype := by
      rw [← map_commutator, hKp]
    have h1 := le_of_le_sup_zpowers_of_perfect htN (map_subtype_le K) hKmp
    intro x hx
    exact mem_subgroupOf.mpr (h1 ⟨x, hx, rfl⟩)
  have hKsub : K.IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hK
    exact hs
  rcases LocalCores.component_subnormal_subgroup (isComponent_subgroupOf_sup_zpowers hG₀ htN)
    hKsub with hle | hcomm
  · exact le_antisymm hKG hle
  · exfalso
    apply ne_bot_of_isPComponent hK
    rw [eq_bot_iff, ← hKp, ← hcomm]
    exact commutator_mono hKG le_rfl

theorem pLayer_sup_zpowers (hG₀c : IsComponent G₀) (hG₀ : IsPComponent 2 G₀)
    (htN : t ∈ normalizer (G₀ : Set G)) :
    pLayer ↥(G₀ ⊔ zpowers t) 2 = G₀.subgroupOf (G₀ ⊔ zpowers t) :=
  le_antisymm (sSup_le fun _ hK => (eq_of_isPComponent_sup_zpowers hG₀c htN hK).le)
    (le_sSup (isPComponent_subgroupOf_sup_zpowers hG₀ htN))

end Layer

theorem conjClosure_eq_of_isComponent {G₀ L : Subgroup G} (hG₀ : IsComponent G₀)
    (hLG₀ : L ≤ G₀) (hLp : ⁅L, L⁆ = L) (hL : L ≠ ⊥) : conjClosure L G₀ = G₀ := by
  set N := conjClosure L G₀ with hN
  have hNG₀ : N ≤ G₀ := by
    rw [hN, conjClosure_eq_iSup]
    refine iSup₂_le fun g hg => ?_
    calc conjugate L g ≤ conjugate G₀ g := map_mono hLG₀
      _ = G₀ := conjugate_eq_of_mem_normalizer (le_normalizer hg)
  have hLN : L ≤ N := le_conjClosure L G₀
  have hNn : (N.subgroupOf G₀).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hNG₀]
    intro g hg
    rw [hN, conjClosure_eq_iSup]
    exact mem_normalizer_iSup_conjugate_of_mem hg
  have hNsub : N.IsSubnormal := Subgroup.IsSubnormal.step N G₀ hNG₀ hG₀.2 hNn
  rcases LocalCores.component_subnormal_subgroup hG₀ hNsub with hle | hcomm
  · exact le_antisymm hNG₀ hle
  · exfalso
    apply hL
    rw [eq_bot_iff, ← hLp, ← hcomm]
    exact commutator_mono hLG₀ hLN

omit [Finite G] in
theorem mem_zpowers_mk_iff {H : Subgroup G} {t : G} (htH : t ∈ H) (y : H) :
    y ∈ zpowers (⟨t, htH⟩ : H) ↔ (y : G) ∈ zpowers t := by
  rw [mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [Subgroup.coe_zpow]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩

theorem footeConclusion_of_subgroupOf {H A L : Subgroup G} {t : G} (htH : t ∈ H) (hAH : A ≤ H)
    (hLH : L ≤ H) (hHA : A ⊔ zpowers t = H) (hAt : conjugate A t = A)
    (huniq : ∀ K : Subgroup H, IsPComponent 2 K → K = A.subgroupOf H)
    (h : FooteConclusion (⟨t, htH⟩ : H) (L.subgroupOf H) (A.subgroupOf H)) :
    FooteConclusion t L A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : H := ⟨t, htH⟩ with ht'
  let eA : A.subgroupOf H ≃* A := subgroupOfEquivOfLe hAH
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  let qA := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 eA
  let qL := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 eL
  rcases h with ⟨⟨e⟩⟩ | ⟨K, hK, hKt, -⟩ | h3 | ⟨hs, he, hcl⟩ | ⟨hs, hodd⟩
  ·
    exact Or.inl ⟨qA.symm.trans (e.trans qL)⟩
  ·
    exfalso
    apply hKt
    rw [huniq K hK, conjugate_subgroupOf_eq, hAt]
  ·
    right; right; left
    rcases h3 with ⟨⟨e₁⟩, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩
    · exact Or.inl ⟨⟨qA.symm.trans e₁⟩, ⟨qL.symm.trans e₂⟩⟩
    · exact Or.inr (Or.inl ⟨⟨qA.symm.trans e₁⟩, ⟨qL.symm.trans e₂⟩⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨qA.symm.trans e₁⟩, ⟨qL.symm.trans e₂⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨qA.symm.trans e₁⟩, ⟨qL.symm.trans e₂⟩⟩))
  ·
    right; right; right; left
    refine ⟨qA.symm.isSimpleGroup, ⟨fun f => he.false (qA.trans (f.trans qL.symm))⟩, ?_⟩
    have hCmap : (coreActionKernel (L.subgroupOf H)).map H.subtype =
        coreActionKernel L ⊓ H := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact mem_inf.mpr ⟨(mem_coreActionKernel_subgroupOf_iff hLH y).mp hy, y.2⟩
      · intro hx
        exact ⟨⟨x, (mem_inf.mp hx).2⟩,
          (mem_coreActionKernel_subgroupOf_iff hLH _).mpr (mem_inf.mp hx).1, rfl⟩
    have hAtmap : (A.subgroupOf H ⊔ zpowers t').map H.subtype = A ⊔ zpowers t := by
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAH, MonoidHom.map_zpowers]
      rfl
    have hX : (((A.subgroupOf H) ⊔ zpowers t') ⊓ coreActionKernel (L.subgroupOf H)).map
        H.subtype = (A ⊔ zpowers t) ⊓ coreActionKernel L := by
      rw [Subgroup.map_inf_eq _ _ _ H.subtype_injective, hAtmap, hCmap, hHA, inf_comm _ H,
        ← inf_assoc, inf_idem, inf_comm]
    have hY : ((A.subgroupOf H) ⊓ coreActionKernel (L.subgroupOf H)).map H.subtype =
        A ⊓ coreActionKernel L := by
      rw [Subgroup.map_inf_eq _ _ _ H.subtype_injective, map_subgroupOf_eq_of_le hAH, hCmap,
        ← inf_assoc, inf_comm _ (coreActionKernel L), inf_assoc,
        inf_eq_left.mpr (show A ≤ H from hAH), inf_comm]
    rcases hcl with ⟨P, hP⟩ | hrank
    · left
      let eX : ↥(((A.subgroupOf H) ⊔ zpowers t') ⊓ coreActionKernel (L.subgroupOf H)) ≃*
          ↥((A ⊔ zpowers t) ⊓ coreActionKernel L) :=
        ((((A.subgroupOf H) ⊔ zpowers t') ⊓ coreActionKernel (L.subgroupOf H)).equivMapOfInjective
          H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hX)
      refine ⟨P.mapSurjective (f := eX.toMonoidHom)
        (show Function.Surjective eX.toMonoidHom from eX.surjective), ?_⟩
      change (P : Subgroup _).map eX.toMonoidHom = _
      rw [hP]
      ext y
      rw [mem_map, mem_subgroupOf]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [mem_subgroupOf, mem_zpowers_mk_iff] at hx
        exact hx
      · intro hy
        obtain ⟨x, hx⟩ := eX.surjective y
        refine ⟨x, ?_, hx⟩
        rw [mem_subgroupOf, mem_zpowers_mk_iff]
        rw [← hx] at hy
        exact hy
    · right
      rw [← hrank]
      exact (pRank_eq_of_mulEquiv one_lt_two
        ((((A.subgroupOf H) ⊓ coreActionKernel (L.subgroupOf H)).equivMapOfInjective H.subtype
          H.subtype_injective).trans (MulEquiv.subgroupCongr hY))).symm
  ·
    right; right; right; right
    exact ⟨qA.symm.isSimpleGroup, (ClassicalInvolution.oddLieType_congr qA.symm).2 hodd⟩

theorem footeComponentReduction_of_inputs (hLB : FooteLBalanceInput) :
    FooteComponentReduction := by
  intro G _ _ t L hmin hce hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨hA2c, hAt, hLA, -, -⟩ := exists_component_of_counterexample hce
  obtain ⟨⟨hKp, hcore, -, hmax, hfam, hrank⟩, hcon⟩ := hce
  generalize hG₀def : conjClosure L (pLayer G 2) = G₀ at *
  have hG₀c : IsComponent G₀ := GSThmB.B5a.isComponent_of_isPComponent hO hA2c
  have htN : t ∈ normalizer (G₀ : Set G) := mem_normalizer_of_conjugate_eq hAt
  set H := G₀ ⊔ zpowers t with hH
  have hlt : Nat.card H < Nat.card G := by
    rw [← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
  have htH : t ∈ H := mem_sup_right (mem_zpowers t)
  have hLH : L ≤ H := hLA.trans le_sup_left
  have hG₀H : G₀ ≤ H := le_sup_left
  have hmax' := footePointedMaximal_subgroupOf hLB (componentsLift_sup_zpowers hG₀c htN) htH
    hLH hmax
  have hLp : ⁅L, L⁆ = L :=
    GSThmB.commutator_eq_self_of_isPComponent hmax.1.2.1 hmax.1.2.2
  have hLne : L ≠ ⊥ := by
    intro hL
    have h1 := ne_bot_of_isPComponent hmax.1.2.2
    apply h1
    rw [hL]
    exact Subgroup.bot_subgroupOf _
  have hA' : conjClosure (L.subgroupOf H) (pLayer ↥H 2) = G₀.subgroupOf H := by
    rw [pLayer_sup_zpowers hG₀c hA2c htN]
    apply map_injective H.subtype_injective
    rw [map_conjClosure, map_subgroupOf_eq_of_le hLH, map_subgroupOf_eq_of_le hG₀H]
    exact conjClosure_eq_of_isComponent hG₀c hLA hLp hLne
  refine hmin.2 ↥H hlt ⟨t, htH⟩ (L.subgroupOf H) ⟨⟨kProper_subgroup' hKp H,
    footeCoreHypothesis_subgroup hcore H, hmax'.1, hmax',
    footeFamilyType_of_mulEquiv (subgroupOfEquivOfLe hLH) hfam, ?_⟩, ?_⟩
  · rw [pRank_eq_of_mulEquiv one_lt_two (subgroupOfEquivOfLe hLH)]
    exact hrank
  · intro hconc
    rw [hA'] at hconc
    exact hcon (footeConclusion_of_subgroupOf htH hG₀H hLH rfl hAt
      (fun K hK => eq_of_isPComponent_sup_zpowers hG₀c htN hK) hconc)

end CFSG.ComponentClassification.FooteLit
