module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSetup
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Inputs
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Swap
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxGen

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

@[expose] def AltAt (K A : Subgroup G) (n : ℕ) : Prop :=
  ∀ M : Subgroup G, IsTwoComponentIn M (centralizer (A : Set G)) →
    ¬ twoLayerIn (K ⊓ centralizer (A : Set G)) ≤ coreActionKernel M →
    ∃ m : ℕ, Odd m ∧ n ≤ m ∧ Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m))

omit [Group G] in
theorem normal_of_le_center_aux {Q : Type*} [Group Q] {N : Subgroup Q} (hN : N ≤ center Q) :
    N.Normal :=
  ⟨fun n hn g => by rw [mem_center_iff.mp (hN hn) g, mul_inv_cancel_right]; exact hn⟩

variable [Finite G]

theorem altAt_of_sup_zpowers (hPump : Sol78.AlternatingPumpUpInput) {K A : Subgroup G} {x : G}
    {n : ℕ} (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hA2 : IsPGroup 2 A)
    (hAQ : A ≤ coreActionKernel K) (hx : IsPGroup 2 (zpowers x)) (hxQ : x ∈ coreActionKernel K)
    (hxA : x ∈ normalizer (A : Set G)) (hx2A : x ^ 2 ∈ A) (hxnA : x ∉ A) (hn9 : 9 ≤ n)
    (hKH : SectionRank.IsKGroupCat ↥(centralizer (A : Set G) ⊔ zpowers x))
    (hexact : ∀ T : Subgroup G,
      IsTwoComponentIn T (centralizer ((A ⊔ zpowers x : Subgroup G) : Set G)) →
      ∀ m : ℕ, Odd m → 9 ≤ m → Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* alternatingGroup (Fin m)) →
        Open.fusionZStar ↥T = pPrimeCore 2 ↥T)
    (hstarB : StarAt K (A ⊔ zpowers x)) (haltB : AltAt K (A ⊔ zpowers x) n) :
    StarAt K A ∧ AltAt K A n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := A ⊔ zpowers x with hB
  set Y := centralizer (A : Set G) with hY
  set CB := centralizer (B : Set G) with hCB
  have hzA : zpowers x ≤ normalizer (A : Set G) := zpowers_le.mpr hxA
  have hB2 : IsPGroup 2 B := by
    have := IsPGroup.to_sup_of_normal_right' hx hA2 hzA
    rwa [sup_comm] at this
  have hBQ : B ≤ coreActionKernel K := sup_le hAQ (zpowers_le.mpr hxQ)
  have hBA : B ≤ normalizer (A : Set G) := sup_le le_normalizer hzA
  have hstarA : StarAt K A :=
    Sol76.twoLayer_inf_centralizer_le_of_normalizes hKq hA2 hB2 le_sup_left hBA hBQ hstarB
  refine ⟨hstarA, fun M hM hmoveA => ?_⟩
  have hmoveB : ¬ twoLayerIn (K ⊓ CB) ≤ coreActionKernel M := fun h =>
    hmoveA (le_coreActionKernel_of_layerAt hKq hA2 hB2 le_sup_left hBQ hstarA hM h)
  set H := Y ⊔ zpowers x with hH
  have hYH : Y ≤ H := le_sup_left
  have hxH : x ∈ H := mem_sup_right (mem_zpowers x)
  set xH : ↥H := ⟨x, hxH⟩ with hxHdef
  have hNc : zpowers (xH ^ 2) ≤ center ↥H := zpowers_sq_le_center hxH (le_centralizer_sq hx2A)
  have : (zpowers (xH ^ 2)).Normal := normal_of_le_center_aux hNc
  set N := zpowers (xH ^ 2) with hN
  set f := QuotientGroup.mk' N with hf
  set x₁ := f xH with hx₁def
  have hx₁ : orderOf x₁ = 2 := orderOf_mk_eq_two hxH hx2A hxnA
  have hH₁K : SectionRank.IsKGroupCat (↥H ⧸ N) := hKH.quotient N
  obtain ⟨hM₁, ⟨eM⟩, hpull⟩ := map_facts_of_component hxA hx2A hxH hM
  set M₁ := (M.subgroupOf H).map f with hM₁def
  have hxH2 : IsPGroup 2 (zpowers xH) := by
    intro g
    have hg : ((g : ↥H) : G) ∈ zpowers x := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
      rw [← hk]
      exact zpow_mem (mem_zpowers x) k
    obtain ⟨k, hk⟩ := hx ⟨_, hg⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨hLBp, -, -, -⟩ := layerAt_facts hKq hB2 hBQ
  have hLBsup := le_sSup_moved_twoComponents hstarB hLBp
  have hCBe : CB = Y ⊓ centralizer ({x} : Set G) := centralizer_sup_zpowers A x
  have hCBY : CB ≤ Y := by rw [hCBe]; exact inf_le_left
  have hCBx : CB ≤ centralizer ({x} : Set G) := by rw [hCBe]; exact inf_le_right
  have hHn : H ≤ normalizer (Y : Set G) :=
    sup_le le_normalizer (zpowers_le.mpr (Sol76.le_normalizer_centralizer hzA (mem_zpowers x)))
  have hCBH : twoLayerIn CB ≤ twoLayerIn H :=
    (twoLayerIn_centralizer_mono hB2 le_sup_left hBA).trans
      (GrSLit.pLayer_map_le_of_isSubnormal hYH
        (Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hYH).mpr hHn)))
  have hTH : ∀ T : Subgroup G, IsTwoComponentIn T CB →
      T.subgroupOf H ≤ centralizer ({xH} : Set ↥H) ∧
        IsPComponent 2 ((T.subgroupOf H).subgroupOf (centralizer ({xH} : Set ↥H))) ∧
        T.subgroupOf H ≤ pLayer ↥H 2 := by
    intro T hT
    have hTCB := hT.1
    have hTx : T ≤ centralizer ({x} : Set G) := hTCB.trans hCBx
    have hCBle : CB ≤ centralizer ({x} : Set G) ⊓ H := le_inf hCBx (hCBY.trans hYH)
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTx (mem_subgroupOf.mp ht)))
    · rw [centralizer_mk_eq hxH, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
        inf_le_right 2 Nat.prime_two]
      have hsub : (CB.subgroupOf (centralizer ({x} : Set G) ⊓ H)).IsSubnormal := by
        refine Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hCBle).mpr ?_)
        intro g hg
        rw [hCBe]
        exact Sol76.mem_normalizer_inf (hHn (mem_inf.mp hg).2)
          (le_normalizer (mem_inf.mp hg).1)
      exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hTCB hCBle hsub).mpr
        hT.2
    · intro t ht
      obtain ⟨z, hz, hzt⟩ := hCBH (le_twoLayerIn_of_isTwoComponentIn hT (mem_subgroupOf.mp ht))
      rwa [← Subtype.ext hzt]
  have hover : ∃ T : Subgroup G, IsTwoComponentIn T CB ∧
      ¬ twoLayerIn (K ⊓ CB) ≤ coreActionKernel T ∧
      (T.subgroupOf H).map f ≤ M₁ ⊔ conjugate M₁ x₁ ∧
      IsPComponent 2 (((T.subgroupOf H).map f).subgroupOf
        ((M₁ ⊔ conjugate M₁ x₁) ⊓ centralizer ({x₁} : Set (↥H ⧸ N)))) := by
    by_contra hcon
    push Not at hcon
    apply hmoveB
    refine hLBsup.trans (sSup_le fun T hT => ?_)
    obtain ⟨hTC, hTpc, hTE⟩ := hTH T hT.1
    obtain ⟨hT₁C, hT₁pc, hT₁E, -, -⟩ := map_facts_of_centralizer hxH2 hNc hTC hTpc hTE
    obtain ⟨M'', hM'', hTM'', hTM''pc⟩ :=
      two_layer_fixed_component_orbit_location hx₁ hT₁C hT₁pc hT₁E
    have hx₁x₁ : x₁ * x₁ = 1 := by rw [← pow_two, ← hx₁, pow_orderOf_eq_one]
    have hconj2 : ∀ L : Subgroup (↥H ⧸ N), conjugate (conjugate L x₁) x₁ = L := by
      intro L
      rw [Sol78.conjugate_conjugate, hx₁x₁, conjugate_one]
    have hne1 : M'' ≠ M₁ := by
      rintro rfl
      exact absurd hTM''pc (hcon T hT.1 hT.2 hTM'')
    have hne2 : M'' ≠ conjugate M₁ x₁ := by
      rintro rfl
      rw [hconj2, sup_comm] at hTM'' hTM''pc
      exact absurd hTM''pc (hcon T hT.1 hT.2 hTM'')
    have hne3 : conjugate M'' x₁ ≠ M₁ := by
      intro h
      apply hne2
      rw [← h, hconj2]
    have h1 : M'' ≤ coreActionKernel M₁ :=
      le_coreActionKernel_of_isPComponent_ne hM₁ hM'' (Ne.symm hne1)
    have h2 : conjugate M'' x₁ ≤ coreActionKernel M₁ :=
      le_coreActionKernel_of_isPComponent_ne hM₁ (isPComponent_conjugate hM'' x₁)
        (Ne.symm hne3)
    intro t ht
    have htH : t ∈ H := (hT.1.1.trans hCBY).trans hYH ht
    have htN : t ∈ normalizer (M : Set G) :=
      ((le_twoLayerIn_of_isTwoComponentIn hT.1).trans
        ((twoLayerIn_centralizer_mono hB2 le_sup_left hBA).trans
          (twoLayerIn_le_normalizer hM.1 hM.2))) ht
    refine hpull t htH htN ?_
    exact sup_le h1 h2 (hTM'' (mem_map_of_mem f (show (⟨t, htH⟩ : ↥H) ∈ T.subgroupOf H from ht)))
  obtain ⟨T, hT, hTmove, hTM, hTMpc⟩ := hover
  obtain ⟨m₁, hm₁o, hm₁n, ⟨eT⟩⟩ := haltB T hT hTmove
  have hTex := hexact T hT m₁ hm₁o (by omega) ⟨eT⟩
  obtain ⟨hTC, hTpc, hTE⟩ := hTH T hT
  obtain ⟨hT₁C, hT₁pc, -, ⟨eT₁⟩, hT₁ex⟩ := map_facts_of_centralizer hxH2 hNc hTC hTpc hTE
  set T₁ := (T.subgroupOf H).map f with hT₁def
  have hTH' : T ≤ H := (hT.1.trans hCBY).trans hYH
  have eTT : ↥T ⧸ Open.fusionZStar ↥T ≃* ↥T₁ ⧸ Open.fusionZStar ↥T₁ :=
    (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hTH')).symm.trans eT₁
  by_cases hMx : conjugate M₁ x₁ = M₁
  ·
    have hT₁M : T₁ ≤ M₁ := by
      have := hTM
      rwa [hMx, sup_idem] at this
    have hex₁ := hT₁ex ((Sol78.fusionZStar_eq_iff _).mpr (by
      have h1 := Sol78.map_center_eq_of_mulEquiv
        (Sol78.coreQuotCongr (subgroupOfEquivOfLe hTH'))
      rw [(Sol78.fusionZStar_eq_iff _).mp hTex] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).mp h1))
    have hZ : (Open.fusionZStar ↥T₁).map T₁.subtype ≤
        (pPrimeCore 2 ↥T₁).map T₁.subtype ⊔ (Open.fusionZStar ↥M₁).map M₁.subtype := by
      rw [hex₁]
      exact le_sup_left
    rcases hPump (↥H ⧸ N) hH₁K M₁ hM₁ x₁ hx₁ (mem_normalizer_of_conjugate_eq' hMx) T₁ hT₁M
        hT₁C hT₁pc hZ m₁ hm₁o (by omega) ⟨eTT.symm.trans eT⟩ with ⟨m', hm'o, hm', ⟨e'⟩⟩ | ⟨h7, -⟩
    · exact ⟨m', hm'o, by omega, ⟨eM.trans e'⟩⟩
    · omega
  ·
    obtain ⟨e⟩ := CatLeaf.swap_case_type hx₁ M₁ hM₁ (Ne.symm hMx) T₁
      (le_inf hTM hT₁C) hTMpc
    exact ⟨m₁, hm₁o, hm₁n, ⟨eM.trans (e.symm.trans (eTT.symm.trans eT))⟩⟩

end CFSG.ComponentClassification.SolMax
