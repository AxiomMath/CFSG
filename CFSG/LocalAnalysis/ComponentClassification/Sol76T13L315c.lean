module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L315a

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient}

omit [Finite G] in
theorem conjClosure_le_self {T L : Subgroup G} (hTL : T ≤ L) : conjClosure T L ≤ L := by
  rw [conjClosure_eq_iSup]
  refine iSup₂_le fun l hl => ?_
  have h1 : L.map (MulAut.conj l⁻¹).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem hl))
  calc conjugate T l = T.map (MulAut.conj l⁻¹).toMonoidHom := rfl
    _ ≤ L.map (MulAut.conj l⁻¹).toMonoidHom := map_mono hTL
    _ = L := h1

omit [Finite G] in
theorem isSubnormal_subgroupOf_of_le_normalizer {A B C : Subgroup G} (hAB : A ≤ B)
    (hBA : B ≤ normalizer (A : Set G)) (hB : (B.subgroupOf C).IsSubnormal) :
    (A.subgroupOf C).IsSubnormal := by
  refine Subgroup.IsSubnormal.step (A.subgroupOf C) (B.subgroupOf C) (fun g hg => hAB hg) hB ?_
  refine ⟨fun n hn g => ?_⟩
  have hnA : (((n : ↥(B.subgroupOf C)) : ↥C) : G) ∈ A := hn
  have hgB : (((g : ↥(B.subgroupOf C)) : ↥C) : G) ∈ B := g.2
  exact (mem_normalizer_iff.mp (hBA hgB) _).mp hnA

omit [Finite G] in
theorem le_of_le_normalizer_of_commutator_ne_bot {X Y : Subgroup G} (hYq : IsQuasisimple ↥Y)
    (hXY : X ≤ normalizer (Y : Set G)) (hYX : Y ≤ normalizer (X : Set G)) (hne : ⁅X, Y⁆ ≠ ⊥) :
    Y ≤ X := by
  set I := X ⊓ Y with hI
  have hIn : (I.subgroupOf Y).Normal := ⟨fun i hi y => by
    rw [mem_subgroupOf] at hi ⊢
    obtain ⟨hiX, hiY⟩ := mem_inf.mp hi
    refine mem_inf.mpr ⟨?_, ?_⟩
    · simpa using (mem_normalizer_iff.mp (hYX y.2) i).mp hiX
    · exact mul_mem (mul_mem y.2 hiY) (inv_mem y.2)⟩
  have hcomm : ⁅X, Y⁆ ≤ I := commutator_le_inf_of_le_normalizer hXY hYX
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hYq
      hIn.isSubnormal with htop | hcen
  · intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ I.subgroupOf Y := by rw [htop]; trivial
    exact (mem_inf.mp (mem_subgroupOf.mp this)).1
  · exfalso
    apply hne
    have hYperf : Group.IsPerfect ↥Y := hYq.1
    have h1 : ⁅X, Y⁆ ≤ centralizer (Y : Set G) := by
      intro c hc
      rw [mem_centralizer_iff]
      intro y hy
      have hcI : c ∈ I := hcomm hc
      have hcY : (⟨c, (mem_inf.mp hcI).2⟩ : ↥Y) ∈ center ↥Y := hcen (mem_subgroupOf.mpr hcI)
      exact (congrArg Subtype.val ((mem_center_iff.mp hcY) ⟨y, hy⟩))
    exact commutator_eq_bot_of_le_centralizer hYperf h1

theorem isTwoComponentIn_centralizer_of_le_centralizer (hm : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N) {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2)
    (hK'C : K' ≤ centralizer ({b} : Set G))
    (hcen : K' ≤ centralizer (oddCoreIn (centralizer ({b} : Set G)) : Set G)) :
    IsTwoComponentIn K' (centralizer ({b} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({b} : Set G) with hC
  set L := twoLayerIn C with hL
  set U := zpowers b with hU
  have hCU : centralizer (U : Set G) = C := by rw [hU, zpowers_eq_closure, centralizer_closure]
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hUne : U ≠ ⊥ := fun h => by
    rw [hU, zpowers_eq_bot] at h
    rw [h, orderOf_one] at hb2
    norm_num at hb2
  have hK'U : K' ⊓ centralizer (U : Set G) = K' := by rw [hCU]; exact inf_eq_left.mpr hK'C
  have hK'tl : twoLayerIn K' = K' := twoLayerIn_eq_self_of_isTwoComponentIn hK'.1
  have hUQ : U ≤ coreActionKernel K' := by
    rw [hU, zpowers_le]
    exact Sol78.mem_coreActionKernel_of_commute fun k hk =>
      mem_centralizer_singleton_iff.mp (hK'C hk)
  have h212 := lemma212Input G K' U hK'.2 hUne hU2 hUQ
  rw [hK'U, hK'tl, hCU] at h212
  have hK'L : K' ≤ L := h212.trans (solomonKStarOf_le_twoLayerIn C)
  have h32 := hm G hG N hN K hK K' hK' hne b hbK hb2
  rw [← hC, inf_eq_left.mpr hK'C, hK'tl] at h32
  set X := conjClosure K' L with hX
  have hK'X : K' ≤ X := le_conjClosure K' L
  have hXL : X ≤ L := conjClosure_le_self hK'L
  have hLX : L ≤ normalizer (X : Set G) := Sol78.le_normalizer_conjClosure K' L
  have hXK' : X ≤ normalizer (K' : Set G) := by
    refine h32.trans (sup_le ?_ le_normalizer)
    exact (oddCoreIn_twoLayerIn_le C).trans
      ((le_centralizer_iff.mp hcen).trans (centralizer_le_normalizer _))
  have hLC : (L.subgroupOf C).IsSubnormal :=
    (Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_twoLayerIn C)).isSubnormal
  have hXC : (X.subgroupOf C).IsSubnormal := isSubnormal_subgroupOf_of_le_normalizer hXL hLX hLC
  have hK'sub : (K'.subgroupOf C).IsSubnormal :=
    isSubnormal_subgroupOf_of_le_normalizer hK'X hXK' hXC
  obtain ⟨-, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K' N hK'.1.1).mp hK'.1.2
  exact ⟨hK'C, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K' C hK'C).mpr ⟨hK'sub, hres, hq⟩⟩

theorem oddCoreIn_le_centralizer_of_mem_centralizer (hm : Lemma32FullFor 𝒜)
    (hq : QuasisimpleTwoPartInput) (hKP : KStarKProper G) (hb : Lemma315bInputFor 𝒜) (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N)
    (hOD : oddCoreIn (solomonKStarOf N) ≤ centralizer (solomonKStarOf N : Set G))
    {K : Subgroup G} (hK : K ∈ kStarComponents N) {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2)
    {J : Subgroup G} (hJ : IsTwoComponentIn J (centralizer ({b} : Set G)))
    (hJs : J ∈ solomonKStar G) : oddCoreIn J ≤ centralizer (J : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cb := centralizer ({b} : Set G) with hCb
  obtain ⟨K', hK', hK'K⟩ := exists_mem_kStarComponents_ne hN K
  have hOK : ∀ {L : Subgroup G}, L ∈ kStarComponents N → oddCoreIn L ≤ centralizer (L : Set G) :=
    fun {L} hL => by
      have hLD : L ≤ solomonKStarOf N := le_iSup₂_of_le L hL le_rfl
      exact ((oddCoreIn_le_of_isTwoComponentIn
        (isTwoComponentIn_of_le hL.1 hLD (solomonKStarOf_le N))).trans hOD).trans
          (centralizer_le hLD)
  have hperf : ∀ {L : Subgroup G}, L ∈ kStarComponents N → Group.IsPerfect ↥L := fun {L} hL =>
    Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hL.1.1 hL.1.2)
  have hres : ∀ {L : Subgroup G}, L ∈ kStarComponents N → oddResidualIn L = L := fun {L} hL => by
    have hLq := isQuasisimple_quotient_of_isPComponent hL.1.1 hL.1.2
    obtain ⟨-, h, -, -⟩ := cover_facts hLq le_rfl (sup_eq_left.mpr (map_subtype_le _))
    rw [← h, twoLayerIn_eq_self_of_isTwoComponentIn hL.1]
  have hKK' : ⁅K, K'⁆ = ⊥ :=
    commutator_eq_bot_of_mem_kStarComponents_of_le hOD hK hK' (Ne.symm hK'K)
  obtain ⟨v, hvK', hv2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK'.2
  set Cv := centralizer ({v} : Set G) with hCv
  have hcK : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hKK' hx) y hy).symm
  have hK'Cb : K' ≤ Cb := fun y hy => mem_centralizer_singleton_iff.mpr (hcK b hbK y hy).symm
  have hKCv : K ≤ Cv := fun x hx => mem_centralizer_singleton_iff.mpr (hcK x hx v hvK')
  obtain ⟨B, hBK, hB, hB4, hbB⟩ :=
    exists_elemAbelian_of_involution (two_le_pRank_of_mem_solomonKStar hK.2) hbK hb2
  obtain ⟨B', hB'K', hB', hB'4, hvB'⟩ :=
    exists_elemAbelian_of_involution (two_le_pRank_of_mem_solomonKStar hK'.2) hvK' hv2
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb2; norm_num at hb2
  have hv1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hv2; norm_num at hv2
  have hb315 : ∀ {L L' : Subgroup G}, L ∈ kStarComponents N → L' ∈ kStarComponents N → L ≠ L' →
      ∀ {E : Subgroup G}, E ≤ L → CFSG.Open.IsElemAbelian 2 E → 4 ≤ Nat.card E →
      (∀ x ∈ L, ∀ y ∈ L', x * y = y * x) → ∀ {e : G}, e ∈ E → e ≠ 1 →
      ∀ u ∈ L', orderOf u = 2 →
        ⁅oddCoreIn (centralizer ({e} : Set G)), zpowers u⁆ = ⊥ ∧
          oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({u} : Set G)) = ⊥ := by
    intro L L' hL hL' hLL' E hEL hE hE4 hcomm e heE he1 u huL' hu2
    have hL'E : L' ⊓ centralizer (E : Set G) = L' :=
      inf_eq_left.mpr fun y hy => mem_centralizer_iff.mpr fun x hx => hcomm x (hEL hx) y hy
    have hV : zpowers u ≤ twoLayerIn (L' ⊓ centralizer (E : Set G)) := by
      rw [hL'E, twoLayerIn_eq_self_of_isTwoComponentIn hL'.1]
      exact zpowers_le.mpr huL'
    have hu2' : u ^ 2 = 1 := by rw [← hu2, pow_orderOf_eq_one]
    have hV1 : zpowers u ≠ ⊥ := fun h => by
      rw [zpowers_eq_bot] at h
      rw [h, orderOf_one] at hu2
      norm_num at hu2
    have h := hb G hG N hN L hL L' hL' hLL' E hEL hE hE4 (zpowers u) hV
      (isElemAbelian_zpowers hu2') hV1 e heE he1
    have hCu : centralizer ((zpowers u : Subgroup G) : Set G) = centralizer ({u} : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    exact ⟨h.1, hCu ▸ h.2⟩
  have hcen : ∀ {L L' : Subgroup G}, L ∈ kStarComponents N → L' ∈ kStarComponents N → L ≠ L' →
      ∀ {e : G}, e ∈ L → orderOf e = 2 → (∀ x ∈ L, ∀ y ∈ L', x * y = y * x) →
      L' ≤ centralizer (oddCoreIn (centralizer ({e} : Set G)) : Set G) := by
    intro L L' hL hL' hLL' e heL he2 hcomm
    obtain ⟨E, hEL, hE, hE4, heE⟩ :=
      exists_elemAbelian_of_involution (two_le_pRank_of_mem_solomonKStar hL.2) heL he2
    have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he2; norm_num at he2
    have hL'C : L' ≤ centralizer ({e} : Set G) := fun y hy =>
      mem_centralizer_singleton_iff.mpr (hcomm e heL y hy).symm
    have hL'q := isQuasisimple_quotient_of_isPComponent hL'.1.1 hL'.1.2
    refine le_of_forall_involution le_rfl (sup_eq_left.mpr (map_subtype_le _)) (hres hL') hL'q
      (exists_noncentral_involution_coreQuot hq hKP hL'.1 hL'.2)
      (le_normalizer_centralizer (hL'C.trans (le_normalizer_oddCoreIn _))) fun u huL' hu2 => ?_
    have h := (hb315 hL hL' hLL' hEL hE hE4 hcomm heE he1 u huL' hu2).1
    have h1 := commutator_eq_bot_iff_le_centralizer.mp h
    rw [← le_centralizer_iff] at h1
    exact h1 (mem_zpowers u)
  have hK'cen : K' ≤ centralizer (oddCoreIn Cb : Set G) :=
    hcen hK hK' (Ne.symm hK'K) hbK hb2 hcK
  have hKcen : K ≤ centralizer (oddCoreIn Cv : Set G) :=
    hcen hK' hK hK'K hvK' hv2 fun x hx y hy => (hcK y hy x hx).symm
  have hOcap : oddCoreIn Cb ⊓ oddCoreIn Cv = ⊥ :=
    (hb315 hK hK' (Ne.symm hK'K) hBK hB hB4 hcK hbB hb1 v hvK' hv2).2
  have hK'2 : IsTwoComponentIn K' Cb :=
    isTwoComponentIn_centralizer_of_le_centralizer hm hG hN hK hK' (Ne.symm hK'K) hbK hb2 hK'Cb
      hK'cen
  have hK2 : IsTwoComponentIn K Cv :=
    isTwoComponentIn_centralizer_of_le_centralizer hm hG hN hK' hK hK'K hvK' hv2 hKCv hKcen
  by_cases hJK' : J = K'
  · rw [hJK']
    exact hOK hK'
  have hJK'c : ⁅J, K'⁆ = ⊥ := by
    refine commutator_eq_bot_of_le_centralizer (hperf hK') ?_
    exact (FooteLit.commutator_le_oddCoreIn_of_ne hJ hK'2 hJK').trans
      (le_centralizer_iff.mp hK'cen)
  have hJCv : J ≤ Cv := fun j hj => mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hJK'c hj) v hvK')).symm
  set V := zpowers v with hV
  have hCV : centralizer (V : Set G) = Cv := by rw [hV, zpowers_eq_closure, centralizer_closure]
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hVne : V ≠ ⊥ := fun h => hv1 (zpowers_eq_bot.mp h)
  have hVQ : V ≤ coreActionKernel J := by
    rw [hV, zpowers_le]
    exact Sol78.mem_coreActionKernel_of_commute fun j hj =>
      mem_centralizer_singleton_iff.mp (hJCv hj)
  have h212 := lemma212Input G J V hJs hVne hV2 hVQ
  rw [hCV, inf_eq_left.mpr hJCv, twoLayerIn_eq_self_of_isTwoComponentIn hJ] at h212
  have hJLv : J ≤ twoLayerIn Cv := h212.trans (solomonKStarOf_le_twoLayerIn Cv)
  obtain ⟨M, ⟨hMC, hMs⟩, hJM⟩ :=
    exists_not_le_coreActionKernel hJ h212 (exists_orderOf_eq_two_of_mem_solomonKStar hJs)
  by_cases hMK : M = K
  ·
    rw [hMK] at hJM
    have hKq := isQuasisimple_of_mem_kStarComponents_of_le hOD hK
    have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
    have hequiv := solomonEquiv_of_not_le_coreActionKernel hv2 hJ hJs.1 hJCv hJLv hK2 hJM
    obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hequiv.2
    have hZK : Open.fusionZStar ↥K = center ↥K := by
      refine fusionZStar_eq_center_of_le' (Subgroup.isPerfect_iff.mpr hKperf).commutator_eq_top
        fun x hx => ?_
      have hx' : (x : G) ∈ oddCoreIn K := ⟨x, hx, rfl⟩
      rw [mem_center_iff]
      intro y
      exact Subtype.ext ((mem_centralizer_iff.mp (hOK hK hx')) y y.2)
    have hcard : Nat.card (↥K ⧸ center ↥K) ≤ Nat.card (↥J ⧸ Open.fusionZStar ↥J) := by
      rw [← hZK, Nat.card_congr e.toEquiv]
    have hJKC : J ≤ K ⊔ centralizer (K : Set G) :=
      hJLv.trans (twoLayerIn_le_sup_centralizer hK2 (hOK hK))
    have hJm : ¬ J ≤ centralizer (K : Set G) := fun h => hJM fun j hj =>
      Sol78.mem_coreActionKernel_of_commute fun k hk => (mem_centralizer_iff.mp (h hj)) k hk
    have hJq' : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
      isQuasisimple_quotient_of_isPComponent hJ.1 hJ.2
    have hJperf : Group.IsPerfect ↥J :=
      Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hJ.1 hJ.2)
    have hKb : K ≤ Cb :=
      le_centralizer_of_le_sup_centralizer hKperf hbK hJKC hJ.1 hJperf hJq' hJm hcard
    have hKL : K ≤ twoLayerIn Cb := by
      set Ub := zpowers b with hUb
      have hCUb : centralizer (Ub : Set G) = Cb := by
        rw [hUb, zpowers_eq_closure, centralizer_closure]
      have hUb2 : IsPGroup 2 Ub :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
      have hUbne : Ub ≠ ⊥ := fun h => hb1 (zpowers_eq_bot.mp h)
      have hUbQ : Ub ≤ coreActionKernel K := by
        rw [hUb, zpowers_le]
        exact Sol78.mem_coreActionKernel_of_commute fun k hk =>
          mem_centralizer_singleton_iff.mp (hKb hk)
      have h1 := lemma212Input G K Ub hK.2 hUbne hUb2 hUbQ
      rw [hCUb, inf_eq_left.mpr hKb, twoLayerIn_eq_self_of_isTwoComponentIn hK.1] at h1
      exact h1.trans (solomonKStarOf_le_twoLayerIn Cb)
    have hKNJ : K ≤ normalizer (J : Set G) :=
      hKL.trans (FooteLit.twoLayerIn_le_normalizer hJ.1 hJ.2)
    have hJNK : J ≤ normalizer (K : Set G) :=
      hJLv.trans (FooteLit.twoLayerIn_le_normalizer hK2.1 hK2.2)
    have hne : ⁅J, K⁆ ≠ ⊥ := fun h => hJm (commutator_eq_bot_iff_le_centralizer.mp h)
    have hKJ : K ≤ J := le_of_le_normalizer_of_commutator_ne_bot hKq hJNK hKNJ hne
    have hKsub : (K.subgroupOf Cb).IsSubnormal := by
      have hJsub : (J.subgroupOf Cb).IsSubnormal := by
        obtain ⟨h, -, -⟩ :=
          (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J Cb hJ.1).mp hJ.2
        exact h
      exact isSubnormal_subgroupOf_of_le_normalizer hKJ hJNK hJsub
    obtain ⟨-, hKres, hKq'⟩ :=
      (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K N hK.1.1).mp hK.1.2
    have hKCb : IsTwoComponentIn K Cb :=
      ⟨hKb, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K Cb hKb).mpr ⟨hKsub, hKres, hKq'⟩⟩
    have hJeq : J = K := by
      by_contra hne'
      exact hJM (GSThmB.B5a.le_coreActionKernel_of_ne hKCb.1 hJ.1 hKCb.2 hJ.2 (Ne.symm hne'))
    rw [hJeq]
    exact hOK hK
  ·
    have hKperf' := hperf hK
    have hMK' : ⁅M, K⁆ = ⊥ := by
      refine commutator_eq_bot_of_le_centralizer hKperf' ?_
      exact (FooteLit.commutator_le_oddCoreIn_of_ne hMC hK2 hMK).trans
        (le_centralizer_iff.mp hKcen)
    have hMCb : M ≤ Cb := fun m hm => mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hMK' hm) b hbK)).symm
    set Y := Cb ⊓ Cv with hY
    have hJY : IsTwoComponentIn J Y := ⟨le_inf hJ.1 hJCv,
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJ.1 hJCv) inf_le_left hJ.2⟩
    have hMY : IsTwoComponentIn M Y := ⟨le_inf hMCb hMC.1,
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hMCb hMC.1) inf_le_right hMC.2⟩
    have hJM' : J = M := by
      by_contra hne'
      exact hJM (GSThmB.B5a.le_coreActionKernel_of_ne hMY.1 hJY.1 hMY.2 hJY.2 (Ne.symm hne'))
    have h1 : oddCoreIn J ≤ oddCoreIn Cb := oddCoreIn_le_of_isTwoComponentIn hJ
    have h2 : oddCoreIn J ≤ oddCoreIn Cv := by
      rw [hJM']
      exact oddCoreIn_le_of_isTwoComponentIn hMC
    have h3 : oddCoreIn J ≤ ⊥ := by
      rw [← hOcap]
      exact le_inf h1 h2
    exact h3.trans bot_le

theorem lemma315cInputFor_of_315b (hm : Lemma32FullFor 𝒜) (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G)
    (hb : Lemma315bInputFor 𝒜) : Lemma315cInputFor 𝒜 := by
  intro G _ _ hG N hN K hK b hbK hb2
  set Cb := centralizer ({b} : Set G) with hCb
  set D := solomonKStarOf Cb with hD
  have hOD := lemma315aInputFor_of_315b hm hq h𝒜 hb G hG N hN
  rw [le_centralizer_iff]
  refine iSup₂_le fun J hJ => ?_
  have hJD : J ≤ D := le_iSup₂_of_le J hJ le_rfl
  have hOJ := oddCoreIn_le_centralizer_of_mem_centralizer hm hq (h𝒜 G hG) hb hG hN hOD hK hbK hb2
    hJ.1 hJ.2
  have hperf : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hJ.1.1 hJ.1.2)
  have hDJ : D ≤ normalizer (J : Set G) :=
    (solomonKStarOf_le_twoLayerIn Cb).trans (FooteLit.twoLayerIn_le_normalizer hJ.1.1 hJ.1.2)
  have hJO : J ≤ normalizer (oddCoreIn D : Set G) := hJD.trans (le_normalizer_oddCoreIn D)
  have hcomm : ⁅oddCoreIn D, J⁆ = ⊥ := by
    refine commutator_eq_bot_of_le_centralizer hperf ?_
    refine (commutator_le_inf_of_le_normalizer ((map_subtype_le _).trans hDJ) hJO).trans ?_
    exact (inf_le_oddCoreIn (coprime_card_oddCoreIn D) hJO).trans hOJ
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)

theorem lemma315aInputFor_simple_of_315b (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hb : Lemma315bInputFor simpleAmbient) :
    Lemma315aInputFor simpleAmbient :=
  lemma315aInputFor_of_315b (lemma32FullFor_simple_of_twoPart hq hR1) hq
    (fun _ _ _ hG => kStarKProper_of_simpleAmbient hG) hb

theorem lemma315cInputFor_simple_of_315b (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hb : Lemma315bInputFor simpleAmbient) :
    Lemma315cInputFor simpleAmbient :=
  lemma315cInputFor_of_315b (lemma32FullFor_simple_of_twoPart hq hR1) hq
    (fun _ _ _ hG => kStarKProper_of_simpleAmbient hG) hb

end CFSG.ComponentClassification.Sol76T13
