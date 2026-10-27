module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneSetup

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.smallData_of_component_iso (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) {Hs : Subgroup G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfig p P M Hs R Rbars)
    {Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)} (hLs : IsComponentOf Ls ⊤)
    (hzsC : d1StarElt p hCHs ∈ Subgroup.centralizer (Ls : Set _)) (eL : Ls ≃* K) :
    D1OneSmallData p P M Hs R Rbars Ls ∧ D1SmallCZElt p Hs R Ls z := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzp : orderOf z = p := hz.2.1
  set zs := d1StarElt p hCHs with hzs
  have hZL : Subgroup.center Ls = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eL hd.center
  have hzsp : orderOf zs = p := orderOf_mk_of_coprime hp _ (primeComplementCore_coprime p)
    (by rw [← Subgroup.orderOf_coe]; exact hzp)
  have hzsL : zs ∉ Ls := by
    intro hmem
    have hcen : (⟨zs, hmem⟩ : Ls) ∈ Subgroup.center Ls := Subgroup.mem_center_iff.mpr fun l =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzsC) l l.2)
    rw [hZL, Subgroup.mem_bot] at hcen
    have h1 : zs = 1 := congrArg Subtype.val hcen
    rw [h1, orderOf_one] at hzsp
    exact hp.one_lt.ne hzsp
  have hzsR : zs ∈ (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) := by
    rw [hcfg.rbar]
    exact ⟨⟨z, mem_of_centralizer_le hCHs⟩, hz.1, rfl⟩
  obtain ⟨T₁, -, -, -, -, hT₁nc, -, -⟩ := hd.exists_sylow
  have hnc : ¬ IsCyclic ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ Ls :
      Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) := by
    obtain ⟨Ts, hTs⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbars
      (ComponentClassification.Components.mathlib_subnormal_of_chain hLs.2.1
        Subgroup.IsSubnormal.top)
    have e0 : (Ts : Subgroup Ls) ≃* ((Rbars : Subgroup _) ⊓ Ls : Subgroup _) :=
      ((Ts : Subgroup Ls).equivMapOfInjective _ Ls.subtype_injective).trans
        (MulEquiv.subgroupCongr hTs)
    have e1 : (Ts : Subgroup Ls) ≃*
        ((Ts.mapSurjective (f := eL.toMonoidHom) eL.surjective : Sylow p K) : Subgroup K) :=
      ((Ts : Subgroup Ls).equivMapOfInjective _ eL.injective).trans
        (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)
    exact fun hcyc => hT₁nc ((MulEquiv.isCyclic ((e0.symm.trans e1).trans
      (Sylow.equiv _ T₁))).mp hcyc)
  have hsmall : Open.pRank p (⊤ : Subgroup (MulAut Ls)) ≤ 2 := by
    have h1 := pRank_map_of_injective p hp (MulAut.congr eL).toMonoidHom
      (MulAut.congr eL).injective (⊤ : Subgroup (MulAut Ls))
    rw [Subgroup.map_top_of_surjective _ (MulAut.congr eL).surjective] at h1
    rw [← h1]
    exact hd.small
  exact ⟨⟨hcfg, hLs, hZL, hnc, ⟨zs, hzsR, hzsL, hzsp, hzsC⟩, hsmall⟩,
    ⟨hz.1, hzp, mem_of_centralizer_le hCHs, hzsC⟩⟩

theorem D1OneSmallData.smallDataIa_of_normal_zpowers (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) (hIso : D1CzIso p z K) {Hs : Subgroup G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfig p P M Hs R Rbars)
    (hA : (Subgroup.zpowers (d1StarElt p hCHs)).Normal) :
    ∃ Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p),
      D1OneSmallData p P M Hs R Rbars Ls ∧ D1SmallCZElt p Hs R Ls z ∧ D1SmallIa p Hs Ls ∧
      Nonempty (Ls ≃* K) ∧
      GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ GLBPrimeCore p Hs := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzp : orderOf z = p := hz.2.1
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set φ := d1StarMap p hCHs with hφ
  obtain ⟨m, hm, T, hRT, hTP⟩ := hd.exists_sylow_centralizer hz
  obtain ⟨Pbar, -, hred⟩ := hd.exists_reducedNongeneration_three hz hm hRT hTP
  obtain ⟨KC, hKC, -, huniq, -, -⟩ := hd.exists_component_czQuot hz hred
  obtain ⟨eK⟩ := hIso KC hKC
  have hker : φ.ker = primeComplementCore (G := C) p :=
    le_antisymm (d1StarMap_ker_le p hCHs)
      (le_d1StarMap_ker hp hzp hCHs hcfg.red.core_eq_bot hA)
  set e := d1CzQuotEquivRange p hCHs hker with he
  obtain ⟨Ls, hLs⟩ := hcfg.exists_isComponentOf
  obtain ⟨hLA, hmap⟩ := d1StarMap_component hp hzp hCHs hker hA huniq hLs
  have eL : Ls ≃* K :=
    ((Subgroup.subgroupOfEquivOfLe hLA).symm.trans
      (((Ls.subgroupOf φ.range).equivMapOfInjective _ e.symm.injective).trans
        (MulEquiv.subgroupCongr hmap))).trans eK
  have hIa : D1SmallIa p Hs Ls := by
    intro L hL
    obtain ⟨hLA', hmap'⟩ := d1StarMap_component hp hzp hCHs hker hA huniq hL
    have h1 : L.subgroupOf φ.range = Ls.subgroupOf φ.range :=
      Subgroup.map_injective e.symm.injective (hmap'.trans hmap.symm)
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hLA', inf_of_le_left hLA] at h1
    exact h1
  have hzsC : d1StarElt p hCHs ∈ Subgroup.centralizer (Ls : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' := hLA hl
    rw [d1StarMap_range hp hzp hCHs, Subgroup.mem_centralizer_singleton_iff] at hl'
    exact hl'
  obtain ⟨hds, hzs⟩ := hd.smallData_of_component_iso hz hCHs hcfg hLs hzsC eL
  have hcore : GLBPrimeCore p C ≤ GLBPrimeCore p Hs := by
    rw [glbPrimeCore_eq_primeComplementCoreOf, glbPrimeCore_eq_primeComplementCoreOf]
    rintro _ ⟨c, hc, rfl⟩
    rw [← hker] at hc
    have h1 : QuotientGroup.mk' (primeComplementCore (G := Hs) p)
        (Subgroup.inclusion hCHs c) = 1 := hc
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨Subgroup.inclusion hCHs c, h1, rfl⟩
  exact ⟨Ls, hds, hzs, hIa, ⟨eL⟩, hcore⟩

theorem D1OneSmallData.zpowers_normal_of_ia_of_card (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z)
    (hcardR : Nat.card R ≤
      p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hIa : D1SmallIa p H K) (hzH : z ∈ H) :
    (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set zb : H ⧸ primeComplementCore (G := H) p :=
    QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ with hzb
  set D := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) with hD
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hd.comp hIa
  have hDn : D.Normal := Subgroup.normal_centralizer
  have hzD : zb ∈ D := by
    obtain ⟨-, -, hzH', hzc⟩ := hz
    exact hzc
  have hzbp : orderOf zb = p := orderOf_mk_of_coprime hp _ (primeComplementCore_coprime p)
    (by rw [← Subgroup.orderOf_coe]; exact hz.2.1)
  have hzR : zb ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.cfg.rbar]
    exact ⟨⟨z, hzH⟩, hz.1, rfl⟩
  have hKD : K ⊓ D = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    have hc : (⟨x, hx.1⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx.2) k k.2)
    rw [hd.center, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hRbar : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = Nat.card R := by
    rw [hd.cfg.rbar, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p)
      (T := R.subgroupOf H) hd.cfg.ext.isPGroup.comap_subtype]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hd.cfg.ext.le_H).toEquiv
  have hRD : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ D :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ p := by
    have hdisj : ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊓
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ D) = ⊥ := by
      rw [eq_bot_iff, ← hKD]
      exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have h1 := mul_card_le_of_inf_eq_bot inf_le_left inf_le_left hdisj
    rw [hRbar] at h1
    have hpos : 0 < Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    exact h1.trans (hcardR.trans_eq (mul_comm _ _))
  have hcoreD : primeComplementCore (G := D) p = ⊥ := by
    have h1 : GLBPrimeCore p D ≤
        primeComplementCore (G := H ⧸ primeComplementCore (G := H) p) p :=
      normal_coprime_le_primeComplementCore p _ (glbPrimeCore_normal_of_normal p hDn)
        (glbPrimeCore_coprime p D)
    rw [hd.cfg.red.core_eq_bot, glbPrimeCore_eq_primeComplementCoreOf] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp (le_bot_iff.mp h1)
  obtain ⟨-, -, -, hnab, -, -, -, -⟩ := hd.exists_sylow
  have hlayer : CFSG.layer D = ⊥ := by
    by_contra hne
    obtain ⟨L, hL⟩ := exists_isComponentOf_of_layer_ne_bot hne
    have hL' : IsComponentOf (L.map D.subtype) ⊤ := by
      refine ⟨le_top, ?_, ComponentClassification.Components.quasisimple_of_equiv
        (L.equivMapOfInjective _ D.subtype_injective).symm hL.2.2⟩
      have h1 : L.IsSubnormal :=
        CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
          Subgroup.IsSubnormal.top
      have h2 : ((L.map D.subtype).subgroupOf D).IsSubnormal := by
        have h3 : (L.map D.subtype).subgroupOf D = L :=
          Subgroup.comap_map_eq_self_of_injective D.subtype_injective L
        rw [h3]
        exact h1
      exact CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
        (Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le _) h2 hDn.isSubnormal)
    have hLK := hIa _ hL'
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : (a : H ⧸ primeComplementCore (G := H) p) ∈ D := by
      have : (a : H ⧸ primeComplementCore (G := H) p) ∈ L.map D.subtype := by
        rw [hLK]
        exact a.2
      exact Subgroup.map_subtype_le _ this
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp ha) b b.2).symm
  have hcp := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot D p hcoreD hlayer
  set Q := CFSG.pCore p D with hQdef
  have hQ : Q ≠ ⊥ := by
    intro hQ
    have hc : Subgroup.centralizer (Q : Set D) ≤ Q := hcp
    rw [hQ] at hc
    have h1 : (⟨zb, hzD⟩ : D) ∈ (⊥ : Subgroup D) := hc (by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      rw [hh, one_mul, mul_one])
    rw [Subgroup.mem_bot] at h1
    have h2 : zb = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hzbp
    exact hp.one_lt.ne hzbp
  set Qb := Q.map D.subtype with hQb
  have hQbn : Qb.Normal := ConjAct.normal_of_characteristic_of_normal
  have hQbp : IsPGroup p Qb := CFSG.pCore_isPGroup.map _
  have hQbR : Qb ≤ Rbar := hQbp.le_sylow_of_normal Rbar
  have hZ : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ D =
      Subgroup.zpowers zb := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hzR, hzD⟩) ?_
    rw [Nat.card_zpowers, hzbp]
    exact hRD
  have hQbz : Qb ≤ Subgroup.zpowers zb := hZ ▸ le_inf hQbR (Subgroup.map_subtype_le _)
  have hQbne : Qb ≠ ⊥ := fun h =>
    hQ ((Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp h)
  have hQbeq : Qb = Subgroup.zpowers zb := by
    refine Subgroup.eq_of_le_of_card_ge hQbz ?_
    have hdvd : Nat.card Qb ∣ p := by
      have h1 := Subgroup.card_dvd_of_le hQbz
      rwa [Nat.card_zpowers, hzbp] at h1
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hQbne
    · rw [h1, Nat.card_zpowers, hzbp]
  rw [← hQbeq]
  exact hQbn

theorem D1OneSmallData.zpowers_normal_of_ia (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) (hLa : D1SmallLa p M H Rbar K)
    (hIa : D1SmallIa p H K) (hzH : z ∈ H) :
    (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal :=
  hd.zpowers_normal_of_ia_of_card hz (hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 hLa).1 hIa hzH

end CFSG.AGLEmbedding
