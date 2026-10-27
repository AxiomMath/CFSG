module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCoverSwap
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxMain

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem pump_step (hSchur : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) {A R : Subgroup G} {x y : G} {m : ℕ}
    (hA2 : IsPGroup 2 A) (hx : IsPGroup 2 (zpowers x)) (hxA : x ∈ normalizer (A : Set G))
    (hx2A : x ^ 2 ∈ A) (hxnA : x ∉ A)
    (hKH : SectionRank.IsKGroupCat ↥(centralizer (A : Set G) ⊔ zpowers x))
    (hR : IsTwoComponentIn R (centralizer ((A ⊔ zpowers x : Subgroup G) : Set G)))
    (hm : Odd m) (hm9 : 9 ≤ m)
    (eR : Nonempty (↥R ⧸ Open.fusionZStar ↥R ≃* alternatingGroup (Fin m)))
    (hZR : Nat.card (center (↥R ⧸ pPrimeCore 2 ↥R)) ≤ 2) (hy : orderOf y = 2) (hyA : y ∈ A)
    (hyR : y ∈ R) :
    ∃ M : Subgroup G, IsTwoComponentIn M (centralizer (A : Set G)) ∧
      Open.fusionZStar ↥M ≠ pPrimeCore 2 ↥M ∧
      (∃ m' : ℕ, Odd m' ∧ m ≤ m' ∧
        Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m'))) ∧
      (y ∈ M ∨ (y ∉ zpowers (x ^ 2) → ∀ Q : Subgroup G, IsPGroup 2 Q →
        Q ≤ centralizer ((A ⊔ zpowers x : Subgroup G) : Set G) ⊓ coreActionKernel R →
        ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ centralizer (A : Set G) ⊓ coreActionKernel M ∧
          Nat.card Q < Nat.card P)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eRalt⟩ := eR
  set B := A ⊔ zpowers x with hB
  set Y := centralizer (A : Set G) with hY
  set CB := centralizer (B : Set G) with hCB
  have hzA : zpowers x ≤ normalizer (A : Set G) := zpowers_le.mpr hxA
  have hB2 : IsPGroup 2 B := by
    have := IsPGroup.to_sup_of_normal_right' hx hA2 hzA
    rwa [sup_comm] at this
  have hBA : B ≤ normalizer (A : Set G) := sup_le le_normalizer hzA
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
  have hfk : f.ker = N := QuotientGroup.ker_mk' N
  have hfc : f.ker ≤ center ↥H := by rw [hfk]; exact hNc
  have hfc' : ∀ L : Subgroup ↥H, L ≤ centralizer (f.ker : Set ↥H) := fun L l _ =>
    mem_centralizer_iff.mpr fun k hk => (mem_center_iff.mp (hfc hk) l).symm
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
  have hCBe : CB = Y ⊓ centralizer ({x} : Set G) := centralizer_sup_zpowers A x
  have hCBY : CB ≤ Y := by rw [hCBe]; exact inf_le_left
  have hCBx : CB ≤ centralizer ({x} : Set G) := by rw [hCBe]; exact inf_le_right
  have hxY : x ∈ normalizer (Y : Set G) := Sol76.le_normalizer_centralizer hzA (mem_zpowers x)
  have hHn : H ≤ normalizer (Y : Set G) := sup_le le_normalizer (zpowers_le.mpr hxY)
  have hYn : (Y.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hYH).mpr hHn
  have hCBH : twoLayerIn CB ≤ twoLayerIn H :=
    (twoLayerIn_centralizer_mono hB2 le_sup_left hBA).trans
      (GrSLit.pLayer_map_le_of_isSubnormal hYH hYn.isSubnormal)
  have hRH : R ≤ H := (hR.1.trans hCBY).trans hYH
  have hRC : R.subgroupOf H ≤ centralizer ({xH} : Set ↥H) := by
    intro t ht
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hCBx (hR.1 (mem_subgroupOf.mp ht))))
  have hRpc : IsPComponent 2 ((R.subgroupOf H).subgroupOf (centralizer ({xH} : Set ↥H))) := by
    have hCBle : CB ≤ centralizer ({x} : Set G) ⊓ H := le_inf hCBx (hCBY.trans hYH)
    rw [centralizer_mk_eq hxH, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      inf_le_right 2 Nat.prime_two]
    have hsub : (CB.subgroupOf (centralizer ({x} : Set G) ⊓ H)).IsSubnormal := by
      refine Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hCBle).mpr ?_)
      intro g hg
      rw [hCBe]
      exact Sol76.mem_normalizer_inf (hHn (mem_inf.mp hg).2) (le_normalizer (mem_inf.mp hg).1)
    exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hR.1 hCBle hsub).mpr hR.2
  have hRE : R.subgroupOf H ≤ pLayer ↥H 2 := by
    intro t ht
    obtain ⟨z, hz, hzt⟩ := hCBH (le_twoLayerIn_of_isTwoComponentIn hR (mem_subgroupOf.mp ht))
    rwa [← Subtype.ext hzt]
  obtain ⟨hR₁C, hR₁pc, hR₁E, ⟨eR₁⟩, -⟩ := map_facts_of_centralizer hxH2 hNc hRC hRpc hRE
  set R₁ := (R.subgroupOf H).map f with hR₁def
  obtain ⟨M'', hM'', hRM'', hRM''pc⟩ :=
    two_layer_fixed_component_orbit_location hx₁ hR₁C hR₁pc hR₁E
  have hRY : R ≤ twoLayerIn Y := (le_twoLayerIn_of_isTwoComponentIn hR).trans
    (twoLayerIn_centralizer_mono hB2 le_sup_left hBA)
  have hRp : ⁅R, R⁆ = R := UnbalancedCorr.commutator_eq_of_isPComponent hR.1 hR.2
  have hRq : IsQuasisimple (↥R ⧸ pPrimeCore 2 ↥R) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 R _ hR.1).mp hR.2).2.2
  obtain ⟨M, hM, hRM⟩ : ∃ M : Subgroup G, IsTwoComponentIn M Y ∧ ¬ R ≤ coreActionKernel M := by
    by_contra hcon
    push Not at hcon
    apply ne_bot_of_isQuasisimple_coreQuot hRq
    rw [eq_bot_iff]
    refine (le_sSup_moved_twoComponents hRY hRp).trans (sSup_le fun T hT => ?_)
    exact absurd (hcon T hT.1) hT.2
  obtain ⟨hM₁, ⟨eM⟩, hpull⟩ := map_facts_of_component hxA hx2A hxH hM
  set M₁ := (M.subgroupOf H).map f with hM₁def
  have hx₁x₁ : x₁ * x₁ = 1 := by rw [← pow_two, ← hx₁, pow_orderOf_eq_one]
  have hconj2 : ∀ L : Subgroup (↥H ⧸ N), conjugate (conjugate L x₁) x₁ = L := by
    intro L
    rw [Sol78.conjugate_conjugate, hx₁x₁, conjugate_one]
  have hMM'' : M'' ⊔ conjugate M'' x₁ = M₁ ⊔ conjugate M₁ x₁ := by
    by_contra hne
    apply hRM
    have hne1 : M'' ≠ M₁ := fun h => hne (by rw [h])
    have hne2 : M'' ≠ conjugate M₁ x₁ := fun h => hne (by rw [h, hconj2, sup_comm])
    have hne3 : conjugate M'' x₁ ≠ M₁ := fun h => hne2 (by rw [← h, hconj2])
    have h1 : M'' ≤ coreActionKernel M₁ :=
      le_coreActionKernel_of_isPComponent_ne hM₁ hM'' (Ne.symm hne1)
    have h2 : conjugate M'' x₁ ≤ coreActionKernel M₁ :=
      le_coreActionKernel_of_isPComponent_ne hM₁ (isPComponent_conjugate hM'' x₁)
        (Ne.symm hne3)
    intro r hr
    have hrH : r ∈ H := hRH hr
    have hrN : r ∈ normalizer (M : Set G) :=
      (hRY.trans (twoLayerIn_le_normalizer hM.1 hM.2)) hr
    exact hpull r hrH hrN (sup_le h1 h2 (hRM'' (mem_map_of_mem f
      (show (⟨r, hrH⟩ : ↥H) ∈ R.subgroupOf H from hr))))
  rw [hMM''] at hRM'' hRM''pc
  set eRR : ↥R ⧸ Open.fusionZStar ↥R ≃* ↥R₁ ⧸ Open.fusionZStar ↥R₁ :=
    (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hRH)).symm.trans eR₁ with heRR
  have hRHp : ⁅R.subgroupOf H, R.subgroupOf H⁆ = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hRH, hRp]
  have hyc : ∀ g ∈ Y, g * y = y * g := fun g hg => ((mem_centralizer_iff.mp hg) y hyA).symm
  have hyY : y ∈ Y := hCBY (hR.1 hyR)
  have hyH : y ∈ H := hRH hyR
  have hMH : M ≤ H := hM.1.trans hYH
  have hMy : M ≤ centralizer ({y} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (hyc g (hM.1 hg))
  have hHy : H ≤ centralizer ({y} : Set G) := by
    refine sup_le (fun g hg => mem_centralizer_singleton_iff.mpr (hyc g hg)) (zpowers_le.mpr ?_)
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp (hCBx (hR.1 hyR))).symm
  have hyZH : (⟨y, hyH⟩ : ↥H) ∈ center ↥H := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hHy g.2))
  have hy₁Z : f ⟨y, hyH⟩ ∈ center (↥H ⧸ N) :=
    GSThmB.TwoQuot.map_mem_center f (QuotientGroup.mk'_surjective N) hyZH
  by_cases hMx : conjugate M₁ x₁ = M₁
  ·
    have hR₁M₁ : R₁ ≤ M₁ := by
      have := hRM''
      rwa [hMx, sup_idem] at this
    have hRMH : R.subgroupOf H ≤ M.subgroupOf H := le_of_map_le_of_perfect f hfc hRHp hR₁M₁
    have hyM : y ∈ M := hRMH (show (⟨y, hyH⟩ : ↥H) ∈ R.subgroupOf H from hyR)
    have hMne := Sol78.fusionZStar_ne_of_central_involution hy hyM hMy
    have hZ : (Open.fusionZStar ↥R₁).map R₁.subtype ≤
        (pPrimeCore 2 ↥R₁).map R₁.subtype ⊔ (Open.fusionZStar ↥M₁).map M₁.subtype := by
      have hRHq : IsQuasisimple (↥(R.subgroupOf H) ⧸ pPrimeCore 2 ↥(R.subgroupOf H)) :=
        LocalCores.isQuasisimple_of_mulEquiv
          (Sol78.coreQuotCongr (subgroupOfEquivOfLe hRH)).symm hRq
      have hZRH : Nat.card (center (↥(R.subgroupOf H) ⧸ pPrimeCore 2 ↥(R.subgroupOf H))) ≤ 2 := by
        have h := hZR
        rw [← Sol78.map_center_eq_of_mulEquiv (Sol78.coreQuotCongr (subgroupOfEquivOfLe hRH)),
          Subgroup.card_map_of_injective
            (Sol78.coreQuotCongr (subgroupOfEquivOfLe hRH)).injective] at h
        exact h
      have hyRo : orderOf (⟨⟨y, hyH⟩, mem_subgroupOf.mpr hyR⟩ : ↥(R.subgroupOf H)) = 2 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hy]
      have hyRc : QuotientGroup.mk' (pPrimeCore 2 ↥(R.subgroupOf H))
          (⟨⟨y, hyH⟩, mem_subgroupOf.mpr hyR⟩ : ↥(R.subgroupOf H)) ∈
            center (↥(R.subgroupOf H) ⧸ pPrimeCore 2 ↥(R.subgroupOf H)) := by
        apply GSThmB.TwoQuot.map_mem_center _ (QuotientGroup.mk'_surjective _)
        rw [mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subtype.ext (hyc _ ((hR.1.trans hCBY) (mem_subgroupOf.mp g.2)))
      have hZ₁ := fusionZStar_le_sup_zpowers_map (f.subgroupMap (R.subgroupOf H))
        (f.subgroupMap_surjective _) (GSThmB.TwoQuot.ker_subgroupMap_le_center f (hfc' _))
        hRHq hZRH hyRo hyRc
      have hyM₁ : f ⟨y, hyH⟩ ∈ M₁ :=
        mem_map_of_mem f (show (⟨y, hyH⟩ : ↥H) ∈ M.subgroupOf H from hyM)
      have hyZ₁ : (⟨f ⟨y, hyH⟩, hyM₁⟩ : ↥M₁) ∈ Open.fusionZStar ↥M₁ := by
        rw [Sol78.fusionZStar_eq_comap, mem_comap]
        apply GSThmB.TwoQuot.map_mem_center _ (QuotientGroup.mk'_surjective _)
        rw [mem_center_iff]
        intro g
        exact Subtype.ext (mem_center_iff.mp hy₁Z g)
      have hmapZ := map_mono (f := ((R.subgroupOf H).map f).subtype) hZ₁
      rw [Subgroup.map_sup, MonoidHom.map_zpowers] at hmapZ
      refine hmapZ.trans (sup_le_sup_left ?_ _)
      rw [zpowers_le]
      exact ⟨⟨f ⟨y, hyH⟩, hyM₁⟩, hyZ₁, rfl⟩
    rcases hPump (↥H ⧸ N) hH₁K M₁ hM₁ x₁ hx₁ (mem_normalizer_of_conjugate_eq' hMx) R₁ hR₁M₁
        hR₁C hR₁pc hZ m hm (by omega) ⟨eRR.symm.trans eRalt⟩ with
      ⟨m', hm'o, hm', ⟨e'⟩⟩ | ⟨h7, -⟩
    · exact ⟨M, hM, hMne, ⟨m', hm'o, hm', ⟨eM.trans e'⟩⟩, Or.inl hyM⟩
    · omega
  ·
    obtain ⟨e⟩ := CatLeaf.swap_case_type hx₁ M₁ hM₁ (Ne.symm hMx) R₁ (le_inf hRM'' hR₁C)
      hRM''pc
    have htype : Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) :=
      ⟨eM.trans (e.symm.trans (eRR.symm.trans eRalt))⟩
    have hMxle : conjugate M x ≤ Y := by
      intro z hz
      rw [UnbalancedLayer.mem_conjugate_iff] at hz
      have h2 := (mem_normalizer_iff.mp (inv_mem hxY) _).mp (hM.1 hz)
      have e : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z := by group
      rwa [e] at h2
    have hMHc : IsPComponent 2 (M.subgroupOf H) := isPComponent_subgroupOf_of_normal hYH hYn hM
    have hMxH : IsPComponent 2 ((conjugate M x).subgroupOf H) :=
      UnbalancedCorr.isPComponent_conjugate_subgroupOf hxH hMHc
    have hMxY : IsTwoComponentIn (conjugate M x) Y :=
      ⟨hMxle, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hMxle hYH
        hYn.isSubnormal).mp hMxH⟩
    have hconjM : conjugate M₁ x₁ = ((conjugate M x).subgroupOf H).map f := by
      rw [hM₁def, hx₁def, ← GSThmB.map_conjugate, conjugate_subgroupOf_eq]
    have hMxX : conjugate M x ≠ M := by
      intro h
      apply hMx
      rw [hconjM, h]
    have hRMM : R ≤ M ⊔ conjugate M x := by
      have h1 : (R.subgroupOf H).map f ≤ ((M ⊔ conjugate M x).subgroupOf H).map f := by
        rw [subgroupOf_sup hMH (hMxle.trans hYH), Subgroup.map_sup, ← hconjM]
        exact hRM''
      have h2 := le_of_map_le_of_perfect f hfc hRHp h1
      intro r hr
      exact h2 (show (⟨r, hRH hr⟩ : ↥H) ∈ R.subgroupOf H from hr)
    have hMne : Open.fusionZStar ↥M ≠ pPrimeCore 2 ↥M := by
      rcases fusionZStar_ne_of_central_mem_sup hM hMxY (Ne.symm hMxX) hy hyY hyc (hRMM hyR)
        with h | h
      · exact h
      · have h' : Open.fusionZStar ↥(M.map (MulAut.conj x⁻¹).toMonoidHom) ≠
            pPrimeCore 2 ↥(M.map (MulAut.conj x⁻¹).toMonoidHom) := h
        rwa [Ne, ← fusionZStar_eq_iff_of_mulEquiv (M.equivMapOfInjective
          (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective)] at h'
    refine ⟨M, hM, hMne, ⟨m, hm, le_rfl, htype⟩, Or.inr fun hyN Q hQ hQD => ?_⟩
    have hy₁ : orderOf (f ⟨y, hyH⟩) = 2 := by
      apply orderOf_eq_prime
      · have hy2 : (⟨y, hyH⟩ : ↥H) ^ 2 = 1 := by
          have h1 : y ^ 2 = 1 := by rw [← hy, pow_orderOf_eq_one]
          exact Subtype.ext h1
        rw [← map_pow, hy2, map_one]
      · intro h
        rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
        apply hyN
        have h1 : ((⟨y, hyH⟩ : ↥H) : G) ∈ N.map H.subtype := mem_map_of_mem _ h
        rw [hN, MonoidHom.map_zpowers] at h1
        simpa using h1
    have hy₁R : f ⟨y, hyH⟩ ∈ R₁ :=
      mem_map_of_mem f (show (⟨y, hyH⟩ : ↥H) ∈ R.subgroupOf H from hyR)
    have hQH : Q ≤ H := fun q hq => hYH (hCBY (mem_inf.mp (hQD hq)).1)
    set QH := Q.subgroupOf H with hQHdef
    have hQx' : ∀ q ∈ QH, q * xH = xH * q := fun q hq => Subtype.ext
      (mem_centralizer_singleton_iff.mp (hCBx (mem_inf.mp (hQD (mem_subgroupOf.mp hq))).1))
    have hx₁c : x₁ ∈ centralizer ((QH.map f : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      rw [hx₁def, ← map_mul, ← map_mul, hQx' q hq]
    set Q' := QH.map f ⊔ zpowers x₁ with hQ'def
    have hQ'2 : IsPGroup 2 Q' := by
      have h1 : IsPGroup 2 (QH.map f) := (hQ.comap_subtype (K := H)).map f
      have h2 : IsPGroup 2 (zpowers x₁) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₁, pow_one])
      have h3 : zpowers x₁ ≤ normalizer ((QH.map f : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) :=
        zpowers_le.mpr (centralizer_le_normalizer' _ hx₁c)
      have := IsPGroup.to_sup_of_normal_right' h2 h1 h3
      rwa [sup_comm] at this
    have hQ'x : Q' ≤ centralizer ({x₁} : Set (↥H ⧸ N)) := by
      refine sup_le ?_ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      intro z hz
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp hx₁c z hz)
    have hQ'L : Q' ≤ coreActionKernel R₁ := by
      refine sup_le ?_ (zpowers_le.mpr (mem_coreActionKernel_of_forall_commute fun l hl =>
        mem_centralizer_singleton_iff.mp (hR₁C hl)))
      rintro _ ⟨q, hq, rfl⟩
      apply GSThmB.TwoQuot.map_mem_coreActionKernel f
      exact (mem_coreActionKernel_subgroupOf_iff hRH q).mpr
        (mem_inf.mp (hQD (mem_subgroupOf.mp hq))).2
    obtain ⟨P', hP'2, hP'K, hlt⟩ := exists_card_lt_of_swap hSchur hx₁ hy₁ hy₁Z hR₁C hR₁pc hy₁R
      hm (by omega) ⟨eRR.symm.trans eRalt⟩ hM₁ hMx hRM'' hRM''pc hQ'2 hQ'x hQ'L
    have hsupH : Y.subgroupOf H ⊔ zpowers xH = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_of_le_left hYH, MonoidHom.map_zpowers,
        ← MonoidHom.range_eq_map, range_subtype]
      rfl
    have hQHY : QH ≤ Y.subgroupOf H := fun q hq =>
      mem_subgroupOf.mpr (hCBY (mem_inf.mp (hQD (mem_subgroupOf.mp hq))).1)
    have hcard := card_lt_card_inf_comap hYn hsupH hQHY hlt
    set PH := Y.subgroupOf H ⊓ P'.comap f with hPH
    refine ⟨PH.map H.subtype, ?_, ?_, ?_⟩
    · have hN2 : IsPGroup 2 f.ker := by
        rw [hfk]
        exact hxH2.to_le (zpowers_le.mpr (pow_mem (mem_zpowers xH) 2))
      exact ((hP'2.comap_of_ker_isPGroup f hN2).to_le inf_le_right).map _
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨hpY, hpP⟩ := mem_inf.mp hp
      refine mem_inf.mpr ⟨mem_subgroupOf.mp hpY, ?_⟩
      have hfpK : f p ∈ coreActionKernel M₁ := hP'K (mem_comap.mp hpP)
      have hpN : (p : G) ∈ normalizer (M : Set G) := by
        have hc1 : IsPComponent 2 (conjugate (M.subgroupOf H) p) := isPComponent_conjugate hMHc p
        have hfpN : f p ∈ normalizer (M₁ : Set (↥H ⧸ N)) := (mem_coreActionKernel.mp hfpK).1
        have heq : (conjugate (M.subgroupOf H) p).map f = (M.subgroupOf H).map f := by
          rw [GSThmB.map_conjugate]
          exact mem_normalizer_iff_map_conj_eq.mp (inv_mem hfpN)
        have : Group.IsSolvable f.ker := Group.isSolvable_of_comm fun a b =>
          Subtype.ext (mem_center_iff.mp (hfc b.2) a)
        have : Group.IsPerfect ↥(conjugate (M.subgroupOf H) p) :=
          CatalogueBAlternating.pComponent_perfect hc1
        have : Group.IsPerfect ↥(M.subgroupOf H) := CatalogueBAlternating.pComponent_perfect hMHc
        have h := GSThmB.TwoQuot.eq_of_map_eq_of_le_centralizer f (hfc' _) (hfc' _) heq
        exact mem_normalizer_of_subgroupOf hMH (mem_normalizer_of_conjugate_eq' h)
      exact hpull (p : G) p.2 hpN hfpK
    · rw [Subgroup.card_map_of_injective H.subtype_injective]
      have h1 : Nat.card QH = Nat.card Q := Nat.card_congr (subgroupOfEquivOfLe hQH).toEquiv
      omega

end CFSG.ComponentClassification.SolMax
