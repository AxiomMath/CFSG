module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CoverNotCaseTwoSites
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Families
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
public import CFSG.LocalAnalysis.AGLEmbedding.CoverNotCaseTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AGEVCoverStar
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M N T : Subgroup G}
  {Tbar : Sylow p (N ⧸ primeComplementCore (G := N) p)}

theorem D1Escape.core_map_le {N T : Subgroup G} (he : D1Escape p P M N T) :
    (primeComplementCore (G := N) p).map N.subtype ≤ M := by
  rintro _ ⟨o, ho, rfl⟩
  exact he.primeCore_le ((mk'_primeComplementCore_eq_one_iff p o).mp
    ((QuotientGroup.eq_one_iff o).mpr ho))

theorem factor_of_normalizer_inf_le (he : D1Escape p P M N T) {K' : Subgroup
    (N ⧸ primeComplementCore (G := N) p)} [hKn : K'.Normal] (hK' : IsComponentOf K' ⊤)
    (hN : Subgroup.normalizer (((Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊓ K' :
      Subgroup _) : Set (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N) :
    ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ k : N, QuotientGroup.mk' (primeComplementCore (G := N) p) k ∈ K' ∧
      x = m * k := by
  have : Fact p.Prime := ⟨he.prime⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := N) p) with hπ
  obtain ⟨T₁, hT₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Tbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK'.2.1
      Subgroup.IsSubnormal.top)
  have htop := Sylow.normalizer_sup_eq_top T₁
  rw [hT₁] at htop
  intro x hx
  have hmem : π ⟨x, hx⟩ ∈ Subgroup.normalizer
      (((Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊓ K' : Subgroup _) :
        Set (N ⧸ primeComplementCore (G := N) p)) ⊔ K' := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨ν, hν, k, hk, hνk⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  obtain ⟨m, hm, rfl⟩ := hN hν
  obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := N) p) k
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have h1 : π (m⁻¹ * ⟨x, hx⟩ * k'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, ← hνk, hπ]; group
  have hoM : ((m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : N) : G) ∈ M :=
    he.primeCore_le ((mk'_primeComplementCore_eq_one_iff p _).mp h1)
  refine ⟨(m : G) * ((m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : N) : G),
    ⟨N.mul_mem m.2 (m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : N).2, M.mul_mem hmM hoM⟩, k', hk, ?_⟩
  simp [mul_assoc]

theorem D1ComponentConfig3.component_facts (hcfg : D1ComponentConfig3 p P M N T Tbar)
    {K' : Subgroup (N ⧸ primeComplementCore (G := N) p)} (hK' : IsComponentOf K' ⊤)
    (hZ : Subgroup.center K' = ⊥) :
    IsSimpleGroup K' ∧ (∃ a b : K', a * b ≠ b * a) ∧ IsCatalogGroup K' := by
  let e : K' ≃* K' ⧸ Subgroup.center K' :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K' ⧸ Subgroup.center K') := hK'.2.2.2
  refine ⟨e.isSimpleGroup, ?_, IsCatalogGroup.of_mulEquiv e
    (hcfg.catalog.isCatalogGroup_center_quotient hK')⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K' hK'.2.2
  refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba

theorem D1ComponentConfig3.le_d1KBar_of_surjective (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hcfg : D1ComponentConfig3 p P M N T Tbar)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    {Jt Xt : Subgroup (N ⧸ primeComplementCore (G := N) p)}
    (φ : Jt →* S) (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hXR : Xt ≤ Tbar) (hncl : nclIn Jt Xt = Jt) (hXJ : Xt ≤ Jt) (hXnc : ¬ IsCyclic Xt) :
    Jt ≤ Hyp111.d1KBar p M N ∧ Hyp111.Hyp93At p M N := by
  have hp := hcfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have he := hcfg.ext.toD1Escape
  have hcore := D1Escape.core_map_le he
  by_cases hall : ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ →
      IsCyclic ((Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊓ L :
        Subgroup (N ⧸ primeComplementCore (G := N) p))
  · exact (hcfg.false_of_cyclic_of_surjective hSch hall hS hSnab φ hφ hcop hXR hncl hXJ
      hXnc).elim
  push Not at hall
  obtain ⟨K', hK', hnc'⟩ := hall
  rcases hcfg.red.rankOne_or_center hK' hnc' with
    ⟨z, hzR, hzK, hzp, hzc, -, hKX₀, -, hZ'⟩ | hcent
  ·
    obtain ⟨hKs, hKnab, hKcat⟩ := hcfg.component_facts hK' hZ'
    have hle := hcfg.red.le_of_rankOne_of_surjective hS hSnab φ hφ hcop hXR hncl hXJ hXnc hK' hZ'
      hnc' ⟨z, hzR, hzK, hzp, hzc⟩ (hSch K' hKs hKnab hKcat)
    have hKK : K' ≤ Hyp111.d1KBar p M N := Hyp111.le_d1KBar hK' hKX₀
    have hcc : D1CompCore p P M N T Tbar K' :=
      ⟨he, hcfg.rbar, hcfg.red, hK', hZ', hnc', ⟨z, hzR, hzK, hzp, hzc⟩⟩
    refine ⟨hle.trans hKK, ⟨fun x hx => ?_, hcore⟩⟩
    obtain ⟨m, hm, k, hk', rfl⟩ := Hyp111.factor_of_compCore hcc x hx
    exact ⟨m, hm, k, hKK hk', rfl⟩
  ·
    have huniq' : ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ →
        L = K' := fun L hL => hcfg.red.eq_of_forall_mem_center hK' hL hcent
    by_cases hKD' : HasKlingenData p Tbar
        (((N ⊓ M).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore p)))
    swap
    · exact (h3 p P M N T Tbar hcfg K' hK' huniq' hnc' hcent hKD').elim
    by_cases hsp' : IsKlingenComponent p K'
    swap
    · exact (hother p P M N T Tbar hcfg K' hK' huniq' hnc' hcent hKD' hsp').elim
    obtain ⟨d', hd'', ⟨e'⟩⟩ := hsp'
    have hp2 : p ≠ 2 := hcfg.loc.ne_two
    have hZ'c : Subgroup.center K' = ⊥ :=
      hmod.center K' p d' hp2 hd'' hK'.2.2 (hcfg.isPGroup_center hK') ⟨e'⟩
    have eK' : K' ≃* CatGroup d' :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ'c.symm)).trans
        e'
    have hC' := hcfg.centralizer_eq_bot hK' huniq' hcent hZ'c
    haveI hKn' : K'.Normal := normal_of_forall_isComponentOf_eq hK' huniq'
    have hOut' := hk.outer p hp2 d' hd'' K' ⟨eK'⟩
    have hRK'' : (Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ≤ K' := by
      have : Finite (MulAut K') := MulEquiv.finite_left
      intro x hx
      obtain ⟨n, hn⟩ := Tbar.isPGroup' ⟨x, hx⟩
      have hxn : x ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hmem := mem_sup_centralizer_of_pow hp hOut' hxn
      rwa [hC', sup_bot_eq] at hmem
    obtain ⟨hKs, hKnab, hKcat⟩ := hcfg.component_facts hK' hZ'c
    have hX : IsPGroup p Xt := Tbar.isPGroup'.to_le hXR
    have hJ : Group.IsPerfect Jt := isPerfect_of_nclIn_eq hS hSnab hX hncl φ hφ hcop
    have hJK : Jt ≤ K' := by
      have := le_sup_centralizer_of_isPerfect hJ (hSch K' hKs hKnab hKcat) (K := K')
      rwa [hC', sup_bot_eq] at this
    have hRK : (Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊓ K' = Tbar :=
      inf_eq_left.mpr hRK''
    have hK'X : ¬ K' ≤ d1X0 p M N := by
      refine not_le_of_weakCore_le hp Tbar hcfg.red.weakCore_le hcfg.red.ne_top ?_
      rw [hRK, hcfg.pRank_rbar_eq_three]
    have hKK : K' ≤ Hyp111.d1KBar p M N := Hyp111.le_d1KBar hK' hK'X
    have hNT : Subgroup.normalizer
        (((Tbar : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊓ K' : Subgroup _) :
          Set (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N := by
      rw [hRK]
      refine (normalizer_le_weakCore p le_rfl ?_ ?_).trans hcfg.red.weakCore_le
      · rw [hcfg.pRank_rbar_eq_three]; norm_num
      · rw [hcfg.pRank_rbar_eq_three.symm]
        exact pRank_mono p hp le_sup_left
    refine ⟨hJK.trans hKK, ⟨fun x hx => ?_, hcore⟩⟩
    obtain ⟨m, hm, k, hk', rfl⟩ := factor_of_normalizer_inf_le he hK' hNT x hx
    exact ⟨m, hm, k, hKK hk', rfl⟩

theorem exists_nclIn_eq_of_surjective [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {L : Type}
    [Group L] (hL : IsSimpleGroup L) {Jt Xt : Subgroup Y} (φ : Jt →* L)
    (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker)) (hX : IsPGroup p Xt)
    (hXJ : Xt ≤ Jt) (hXne : Xt ≠ ⊥) :
    ∃ (J : Subgroup Y) (hJ : J ≤ Jt), Xt ≤ J ∧
      Function.Surjective (φ.comp (Subgroup.inclusion hJ)) ∧ nclIn J Xt = J := by
  classical
  obtain ⟨J, ⟨hXJ', hJ, hJs⟩, hmin⟩ := Set.exists_min_image
    {J : Subgroup Y | Xt ≤ J ∧ ∃ h : J ≤ Jt, Function.Surjective (φ.comp (Subgroup.inclusion h))}
    (fun J => Nat.card J) (Set.toFinite _)
    ⟨Jt, hXJ, le_rfl, fun l => let ⟨j, hj⟩ := hφ l; ⟨j, hj⟩⟩
  set ψ := φ.comp (Subgroup.inclusion hJ)
  set Nc := nclIn J Xt
  have hNJ : Nc ≤ J := nclIn_le_self J Xt
  have hXN : Xt ≤ Nc := le_nclIn hXJ'
  have hrange : (φ.comp (Subgroup.inclusion (hNJ.trans hJ))).range = (Nc.subgroupOf J).map ψ := by
    ext l
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨Subgroup.inclusion hNJ n, Subgroup.mem_subgroupOf.mpr n.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, Subgroup.mem_subgroupOf.mp hj⟩, rfl⟩
  have hrn : (φ.comp (Subgroup.inclusion (hNJ.trans hJ))).range.Normal := by
    rw [hrange]
    haveI := nclIn_normal J Xt
    exact Subgroup.Normal.map inferInstance ψ hJs
  have hrne : (φ.comp (Subgroup.inclusion (hNJ.trans hJ))).range ≠ ⊥ := by
    intro hbot
    apply hXne
    rw [eq_bot_iff]
    intro x hx
    have hker : (⟨x, hXN hx⟩ : Nc) ∈ (φ.comp (Subgroup.inclusion (hNJ.trans hJ))).ker := by
      rw [MonoidHom.mem_ker]
      have : (φ.comp (Subgroup.inclusion (hNJ.trans hJ))) ⟨x, hXN hx⟩ ∈
          (φ.comp (Subgroup.inclusion (hNJ.trans hJ))).range := ⟨_, rfl⟩
      rw [hbot] at this
      exact this
    obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
    have hk' : (⟨x, hXN hx⟩ : Nc) ^ p ^ k = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    have hdvd1 : orderOf (⟨x, hXN hx⟩ : Nc) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hdvd2 : orderOf (⟨x, hXN hx⟩ : Nc) ∣
        Nat.card (φ.comp (Subgroup.inclusion (hNJ.trans hJ))).ker := by
      rw [← Subgroup.orderOf_mk _ hker]
      exact orderOf_dvd_natCard _
    have hc : (orderOf (⟨x, hXN hx⟩ : Nc)).Coprime (p ^ k) :=
      Nat.Coprime.pow_right k
        ((Hyp111.coprime_card_ker_comp_inclusion φ hcop (hNJ.trans hJ)).coprime_dvd_right
          hdvd2).symm
    have h1 := Nat.Coprime.eq_one_of_dvd hc hdvd1
    rw [orderOf_eq_one_iff] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hNs : Function.Surjective (φ.comp (Subgroup.inclusion (hNJ.trans hJ))) := by
    haveI := hrn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (φ.comp (Subgroup.inclusion (hNJ.trans hJ))).range with hb | ht
    · exact absurd hb hrne
    · exact MonoidHom.range_eq_top.mp ht
  exact ⟨J, hJ, hXJ', hJs, Subgroup.eq_of_le_of_card_ge hNJ (hmin Nc ⟨hXN, hNJ.trans hJ, hNs⟩)⟩

theorem D1ComponentConfig3.hyp917At_of_cover (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hcfg : D1ComponentConfig3 p P M N T Tbar) {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1)
    {W : Subgroup G} (hW : W ≤ H ⊓ N)
    (hWK : (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K)
    {X : Subgroup G} (hXW : X ≤ W) (hXT : X ≤ T)
    (hXnc : ¬ IsCyclic
      ((X.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))) :
    Hyp111.Hyp93At p M N ∧ Hyp111.Hyp917At p M H N K := by
  have hp := hcfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set πH := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set πN := QuotientGroup.mk' (primeComplementCore (G := N) p)
  have hWH : W ≤ H := hW.trans inf_le_left
  have hWN : W ≤ N := hW.trans inf_le_right
  set ρ : W →* N ⧸ primeComplementCore (G := N) p := πN.comp (Subgroup.inclusion hWN)
  have hψ₀ : ∀ w, πH.comp (Subgroup.inclusion hWH) w ∈ K := fun w =>
    hWK ▸ ⟨Subgroup.inclusion hWH w, Subgroup.mem_subgroupOf.mpr w.2, rfl⟩
  set ψ : W →* K := (πH.comp (Subgroup.inclusion hWH)).codRestrict K hψ₀
  have hψs : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    rw [← hWK] at hk
    obtain ⟨h, hh, rfl⟩ := hk
    exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  obtain ⟨x, hx1, kx, hxk⟩ := hKp
  haveI := hKs
  have hker : ρ.rangeRestrict.ker ≤ ψ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact le_ker_of_isSimpleGroup ψ hψs ρ.ker (fun n hn => coprime_of_mk_inclusion_eq_one3 hWN n hn)
      hx1 hxk
  obtain ⟨φ, hφρ, hφs, hφker⟩ := exists_surjective_comp_eq ρ.rangeRestrict
    ρ.rangeRestrict_surjective ψ hψs hker
  have hcopψ : p.Coprime (Nat.card ψ.ker) := by
    set g : ψ.ker →* primeComplementCore (G := H) p :=
      ((Subgroup.inclusion hWH).comp ψ.ker.subtype).codRestrict _ (fun w => by
        have h1 : ψ w = 1 := w.2
        have h2 : πH (Subgroup.inclusion hWH w) = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2)
    have hinj : Function.Injective g := by
      intro a b hab
      have := congrArg (fun x : primeComplementCore (G := H) p => ((x : H) : G)) hab
      exact Subtype.ext (Subtype.ext this)
    exact (primeComplementCore_coprime (G := H) p).coprime_dvd_right
      (Subgroup.card_dvd_of_injective g hinj)
  have hcopφ : p.Coprime (Nat.card φ.ker) := by
    rw [hφker]
    exact hcopψ.coprime_dvd_right (Subgroup.card_map_dvd _ _)
  set Xt := (X.subgroupOf N).map πN
  have hXρ : Xt ≤ ρ.range := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hXW (Subgroup.mem_subgroupOf.mp hy)⟩, rfl⟩
  have hXR : Xt ≤ Tbar := by
    rw [hcfg.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hXT)
  have hXp : IsPGroup p Xt := Tbar.isPGroup'.to_le hXR
  have hXne : Xt ≠ ⊥ := fun h => hXnc (h ▸ inferInstance)
  obtain ⟨J, hJ, hXJ, hJs, hncl⟩ := exists_nclIn_eq_of_surjective hKs φ hφs hcopφ hXp hXρ hXne
  obtain ⟨hJle, h93⟩ := hcfg.le_d1KBar_of_surjective h3 hother hSch hk hmod hKs hKnab
    (φ.comp (Subgroup.inclusion hJ)) hJs (Hyp111.coprime_card_ker_comp_inclusion φ hcopφ hJ) hXR
    hncl hXJ hXnc
  refine ⟨h93, (J.comap ρ).map W.subtype, ?_, ?_, Or.inl ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact hW w.2
  · ext k
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨w, -, hw⟩ := Subgroup.mem_subgroupOf.mp hh
      have hwH : (w : G) ∈ H := hWH w.2
      have : h = ⟨w, hwH⟩ := Subtype.ext hw.symm
      subst this
      exact hψ₀ w
    · intro hk
      obtain ⟨j, hj⟩ := hJs ⟨k, hk⟩
      obtain ⟨w, hw⟩ := hJ j.2
      have hwJ : ρ w ∈ J := by rw [hw]; exact j.2
      refine ⟨⟨w, hWH w.2⟩, Subgroup.mem_subgroupOf.mpr ⟨w, hwJ, rfl⟩, ?_⟩
      have h1 := hφρ w
      have h2 : ρ.rangeRestrict w = Subgroup.inclusion hJ j := Subtype.ext hw
      rw [h2] at h1
      have h3' : (φ (Subgroup.inclusion hJ j) : H ⧸ primeComplementCore (G := H) p) = k :=
        congrArg Subtype.val hj
      rw [h1] at h3'
      exact h3'
  · rintro _ ⟨n, hn, rfl⟩
    obtain ⟨w, hwJ, hw⟩ := Subgroup.mem_subgroupOf.mp hn
    have : n = Subgroup.inclusion hWN w := Subtype.ext hw.symm
    subst this
    exact hJle hwJ

end CFSG.LocalAnalysis.RankThreeTheoremC
