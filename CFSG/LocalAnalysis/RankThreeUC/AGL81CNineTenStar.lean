module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineConseq
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFive

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

private theorem relPPrimeCore_eq_map' (hp : p.Prime) (C : Subgroup G) :
    relPPrimeCore p C = (primeComplementCore (G := ↥C) p).map C.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNC, hNn, hNc⟩ := hN
    have h1 : N.subgroupOf C ≤ primeComplementCore (G := ↥C) p := by
      refine le_sSup ⟨hNn, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
      exact hNc
    calc N = (N.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hNC).symm
      _ ≤ _ := Subgroup.map_mono h1
  · refine le_sSup ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · show (Subgroup.comap C.subtype ((primeComplementCore (G := ↥C) p).map C.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      infer_instance
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card

private theorem pRank_map_eq_of_coprime_ker (hp : p.Prime) {H H' : Type*} [Group H] [Finite H]
    [Group H'] [Finite H'] (f : H →* H') (A : Subgroup H)
    (hY : ¬ p ∣ Nat.card ↥(A ⊓ f.ker)) :
    CFSG.Open.pRank p (A.map f) = CFSG.Open.pRank p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  let g : A →* A.map f :=
    (f.comp A.subtype).codRestrict (A.map f) (fun x => Subgroup.mem_map_of_mem f x.2)
  have hgsurj : Function.Surjective g := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hgker : g.ker = (A ⊓ f.ker).subgroupOf A := by
    ext x
    constructor
    · intro hx
      refine Subgroup.mem_subgroupOf.mpr ⟨x.2, MonoidHom.mem_ker.mpr ?_⟩
      have h := congrArg Subtype.val hx
      simpa [g] using h
    · intro hx
      have hx' : (x : H) ∈ f.ker := (Subgroup.mem_subgroupOf.mp hx).2
      apply Subtype.ext
      simpa [g] using MonoidHom.mem_ker.mp hx'
  have hgcard : Nat.card g.ker = Nat.card ↥(A ⊓ f.ker) := by
    rw [hgker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hgcop : p.Coprime (Nat.card g.ker) := by
    rw [hgcard]
    exact (hp.coprime_iff_not_dvd).mpr hY
  calc CFSG.Open.pRank p (A.map f)
      = CFSG.Open.pRank p (⊤ : Subgroup (A.map f)) :=
        pRank_subgroup_eq_internal_top p hp.one_lt (A.map f)
    _ = CFSG.Open.pRank p (⊤ : Subgroup A) :=
        (pRank_top_eq_of_coprime_kernel p hp g hgsurj hgcop).symm
    _ = CFSG.Open.pRank p A :=
        (pRank_subgroup_eq_internal_top p hp.one_lt A).symm

private theorem frattini_le_sup_normalizer {q : ℕ} [Fact q.Prime] {H K S : Subgroup G}
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf q S K) :
    H ≤ K ⊔ (H ⊓ normalizer (S : Set G)) := by
  classical
  haveI : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
  obtain ⟨hSK, hSp, _⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hSH : S ≤ H := hSK.trans hKH
  have hS' : CFSG.ABGLocalTools.IsSylowOf q (S.subgroupOf H) (K.subgroupOf H) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨fun x hx => hSK hx, hSp.comap_subtype, ?_⟩
    rwa [Subgroup.relIndex_subgroupOf hKH]
  obtain ⟨S₀, hS₀⟩ := hS'
  have hF : Subgroup.normalizer (((S₀ : Subgroup ↥(K.subgroupOf H)).map
      (K.subgroupOf H).subtype : Subgroup ↥H) : Set ↥H) ⊔ K.subgroupOf H = ⊤ :=
    Sylow.normalizer_sup_eq_top S₀
  rw [hS₀] at hF
  intro h hh
  have hmem : (⟨h, hh⟩ : ↥H) ∈ Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔
      K.subgroupOf H := by
    rw [hF]
    trivial
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hnG : (n : G) ∈ normalizer (S : Set G) := by
    have hn' := hn
    rw [Subgroup.mem_normalizer_iff] at hn' ⊢
    intro x
    constructor
    · intro hx
      exact (hn' ⟨x, hSH hx⟩).1 hx
    · intro hx
      have hxH : x ∈ H := by
        have h1 : (n : G) * x * (n : G)⁻¹ ∈ H := hSH hx
        have := H.mul_mem (H.mul_mem (H.inv_mem n.2) h1) n.2
        simpa [mul_assoc] using this
      exact (hn' ⟨x, hxH⟩).2 hx
  have hh' : h = (n : G) * (k : G) := congrArg Subtype.val hnk.symm
  rw [hh']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨n.2, hnG⟩) (Subgroup.mem_sup_left hk)

private theorem pGroup_quotient_sylow_sup_normal {X : Type*} [Group X] [Finite X] (prime : ℕ)
    (hprime : prime.Prime) (normalGroup : Subgroup X) (hnormal : normalGroup.Normal)
    (hquotient : IsPGroup prime (X ⧸ normalGroup)) (sylowGroup : Sylow prime X) :
    (sylowGroup : Subgroup X) ⊔ normalGroup = ⊤ := by
  letI : Fact prime.Prime := ⟨hprime⟩
  letI : normalGroup.Normal := hnormal
  let quotientSylow := sylowGroup.mapSurjective (QuotientGroup.mk'_surjective normalGroup)
  have hquotientTop : (quotientSylow : Subgroup (X ⧸ normalGroup)) = ⊤ := by
    exact (quotientSylow.is_maximal' (hquotient.to_subgroup ⊤) le_top).symm
  have hmap : (sylowGroup : Subgroup X).map (QuotientGroup.mk' normalGroup) = ⊤ := by
    rw [← Sylow.coe_mapSurjective]
    exact hquotientTop
  have hcomap := congrArg (fun subgroup : Subgroup (X ⧸ normalGroup) =>
    subgroup.comap (QuotientGroup.mk' normalGroup)) hmap
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomap

theorem pRank_starImg_eq (hp : p.Prime) {H A : Subgroup G} (hAH : A ≤ H) :
    CFSG.Open.pRank p (starImg p H A) = CFSG.Open.pRank p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hOcop : ¬ p ∣ Nat.card (primeComplementCore (G := ↥H) p) :=
    (hp.coprime_iff_not_dvd).mp (primeComplementCore_coprime p)
  have hker : ¬ p ∣ Nat.card ↥((A.subgroupOf H) ⊓
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact fun hdvd => hOcop (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hquot : CFSG.Open.pRank p (starImg p H A) = CFSG.Open.pRank p (A.subgroupOf H) :=
    pRank_map_eq_of_coprime_ker (p := p) hp
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) (A.subgroupOf H) hker
  have hsub : CFSG.Open.pRank p A = CFSG.Open.pRank p (A.subgroupOf H) := by
    let e : ↥A ≃* ↥(A.subgroupOf H) :=
      ((Subgroup.equivMapOfInjective (A.subgroupOf H) H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subgroupOf_eq_of_le hAH))).symm
    calc CFSG.Open.pRank p A
        = CFSG.Open.pRank p (⊤ : Subgroup ↥A) :=
          pRank_subgroup_eq_internal_top p hp.one_lt A
      _ = CFSG.Open.pRank p (⊤ : Subgroup ↥(A.subgroupOf H)) :=
          pRank_top_eq_of_equiv p hp.one_lt e
      _ = CFSG.Open.pRank p (A.subgroupOf H) :=
          (pRank_subgroup_eq_internal_top p hp.one_lt (A.subgroupOf H)).symm
  rw [hquot]
  exact hsub.symm

private theorem le_sup_of_starImg_isPGroup {H U S : Subgroup G} (hp : p.Prime) (hUH : U ≤ H)
    (hOU : relPPrimeCore p H ≤ U) (hUp : IsPGroup p ↥(starImg p H U))
    (hS' : CFSG.ABGLocalTools.IsSylowOf p (S ⊓ U) U) :
    U ≤ relPPrimeCore p H ⊔ (S ⊓ U) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : ↥U →* StarGroup p H :=
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp (Subgroup.inclusion hUH)
  have hφker : φ.ker = (relPPrimeCore p H).subgroupOf U := by
    ext x
    constructor
    · intro hx
      have hx' : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
          (Subgroup.inclusion hUH x) = 1 := MonoidHom.mem_ker.mp hx
      have hxO : (Subgroup.inclusion hUH x) ∈ primeComplementCore (G := ↥H) p :=
        (QuotientGroup.eq_one_iff _).mp hx'
      have hx'' : (x : G) ∈ (primeComplementCore (G := ↥H) p).map H.subtype :=
        ⟨Subgroup.inclusion hUH x, hxO, rfl⟩
      rw [← relPPrimeCore_eq_map' hp H] at hx''
      exact hx''
    · intro hx
      rw [MonoidHom.mem_ker]
      have hx' : (x : G) ∈ relPPrimeCore p H := Subgroup.mem_subgroupOf.mp hx
      rw [relPPrimeCore_eq_map' hp H] at hx'
      rcases hx' with ⟨z, hz, hzx⟩
      have hincl : Subgroup.inclusion hUH x = z := by
        apply Subtype.ext
        rw [Subgroup.coe_inclusion]
        exact hzx.symm
      show (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
        (Subgroup.inclusion hUH x) = 1
      rw [hincl]
      exact (QuotientGroup.eq_one_iff z).mpr hz
  have hφrange : φ.range = starImg p H U := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
      refine ⟨⟨z.1, hz⟩, ?_⟩
      change (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
        (Subgroup.inclusion hUH ⟨z.1, hz⟩) = y
      rw [show Subgroup.inclusion hUH ⟨z.1, hz⟩ = z from Subtype.ext rfl]
      exact hzy
  obtain ⟨S₀, hS₀⟩ := hS'.exists_sylow_eq_subgroupOf
  have hquot : IsPGroup p (↥U ⧸ φ.ker) := by
    refine hUp.of_equiv ?_
    exact ((QuotientGroup.quotientKerEquivRange φ).trans
      (MulEquiv.subgroupCongr hφrange)).symm
  have hsup : (S₀ : Subgroup ↥U) ⊔ φ.ker = ⊤ :=
    pGroup_quotient_sylow_sup_normal p hp φ.ker inferInstance hquot S₀
  have hmap := congrArg (Subgroup.map U.subtype) hsup
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at hmap
  have hS₀map : ((S₀ : Subgroup ↥U).map U.subtype) = S ⊓ U := by
    rw [hS₀, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hkermap : φ.ker.map U.subtype = relPPrimeCore p H := by
    rw [hφker, Subgroup.map_subgroupOf_eq_of_le hOU]
  have hsum : (S ⊓ U) ⊔ relPPrimeCore p H = U := by
    rw [← hS₀map, ← hkermap, hmap]
  exact le_of_eq (hsum.symm.trans (sup_comm (S ⊓ U) (relPPrimeCore p H)))

namespace NineSetting

theorem exists_sylow_nineSetting (h : NineSetting G M p Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) (hU : NineNineOne M p) :
    ∃ P : Subgroup G, Q ≤ P ∧ NineSetting G M p P H E 2 ∧ H ∈ H2Fam M P ∧
      CFSG.ABGLocalTools.IsSylowOf p P H ∧ P ≤ M ∧ normalizer (P : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hQinf : Q ≤ H ⊓ M := le_inf h.Q_le_H h.Q_le_M
  have hQp : IsPGroup p (Q.subgroupOf (H ⊓ M)) :=
    (QSet.isPGroup_of_mem h.mem_Q).comap_subtype (K := H ⊓ M)
  obtain ⟨S, hQS⟩ := hQp.exists_le_sylow
  set P : Subgroup G := (S : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype with hPdef
  have hP : CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) := ⟨S, hPdef.symm⟩
  have hQP : Q ≤ P := by
    intro q hq
    rw [hPdef]
    exact ⟨⟨q, hQinf hq⟩, hQS (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  obtain ⟨hPH, hN⟩ := h.isSylowOf_of_NineNineOne hp hU hP
  have hPM : P ≤ M := hP.le.trans inf_le_right
  have hPmem : P ∈ QSet M p := QSet.of_le h.mem_Q hQP hPM hP.isPGroup
  have hHmem : H ∈ HFam M P := ⟨h.ne_top, hPH.le, h.not_le⟩
  have hstdE : IsStdE p 2 M P E := by
    obtain ⟨hk, hEQ, hE, hEc, hΓ⟩ := h.stdE
    exact ⟨hk, hEQ.trans hQP, hE, hEc, hΓ⟩
  have hH2P : H ∈ H2Fam M P := by
    obtain ⟨h1, h2, h3, h4⟩ := mem_H2Fam_iff.mp hH2
    exact mem_H2Fam_iff.mpr ⟨h1, hPH.le, h3, h4⟩
  exact ⟨P, hQP, ⟨h.setting, hPmem, hHmem, hstdE⟩, hH2P, hPH, hPM, hN⟩

theorem pRank_le_of_mem_H2Fam (h : NineSetting G M p Q H E k) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) :
    CFSG.Open.pRank p H ≤ 3 ∧ (5 < p → CFSG.Open.pRank p H ≤ 2) ∧
      CFSG.Open.pRank 3 H ≤ 3 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTne : CFSG.pCore 2 ↥H ≠ ⊥ := by
    intro hbot
    have hpcof : pCoreOf 2 H = ⊥ := by
      rw [pCoreOf, hbot, Subgroup.map_bot]
    have hcen : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr (bot_le : (⊥ : Subgroup G) ≤ Subgroup.center G)
    have hcl := hH2.2.2.2
    rw [hpcof, hcen, inf_top_eq] at hcl
    exact h.not_le (hcl.trans bot_le)
  have htop : IsTwoLocal (⊤ : Subgroup ↥H) := by
    refine ⟨CFSG.pCore 2 ↥H, hTne, CFSG.pCore_isPGroup, ?_⟩
    exact (show ⊤ = Subgroup.normalizer ((CFSG.pCore 2 ↥H : Subgroup ↥H) : Set ↥H) from by
      rw [Subgroup.normalizer_eq_top])
  have hle (q : ℕ) (hq : 1 < q) : CFSG.Open.pRank q H ≤ rankThreeLocalRank q H :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q) H).le.trans
      (local_pRank_le_localRank (G := ↥H) q hq (⊤ : Subgroup ↥H) htop)
  have h5 := h.nineFive hp
  refine ⟨(hle p h.prime.one_lt).trans h5.2.1.1, ?_, ?_⟩
  · intro hp5
    by_contra hnot
    have h3 : 3 ≤ CFSG.Open.pRank p H := by omega
    have h3' : 3 ≤ rankThreeLocalRank p H := h3.trans (hle p h.prime.one_lt)
    have heq : rankThreeLocalRank p H = 3 := by omega
    exact absurd (h5.2.1.2 heq) (by omega)
  · have h3H : rankThreeLocalRank 3 H ≤ 3 :=
      (twoLocalPrimeRank_subgroup_le (p := 3) Nat.prime_three H).trans
        ((rankThreeLocalRank_le_evenRank 3 Nat.prime_three (by norm_num)).trans
          (le_of_eq h.setting.standing.rank))
    exact (hle 3 (by norm_num)).trans h3H

theorem le_of_frattini (h : NineSetting G M p Q H E 2) (hU : NineNineOne M p)
    {B U S : Subgroup G} (hBH : B ≤ H) (hUB : U ≤ B) (hUn : (U.subgroupOf B).Normal)
    (hOU : relPPrimeCore p H ≤ U) (hUp : IsPGroup p ↥(starImg p H U))
    (hS : CFSG.ABGLocalTools.IsSylowOf p S B) (hSM : S ≤ M) (hES : E ≤ S) (hEU : E ≤ U) :
    B ≤ M := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hUH : U ≤ H := hUB.trans hBH
  have hBU : B ≤ normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hUn
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (S ⊓ U) U :=
    hS.inf_of_le_normalizer hUB hBU
  have hF : B ≤ U ⊔ (B ⊓ normalizer ((S ⊓ U) : Set G)) :=
    frattini_le_sup_normalizer (q := p) (H := B) (K := U) (S := S ⊓ U) hUB hBU hS'
  have hUS : U ≤ relPPrimeCore p H ⊔ (S ⊓ U) :=
    le_sup_of_starImg_isPGroup (H := H) (U := U) (S := S) h.prime hUH hOU hUp hS'
  have hEM : E ≤ M := h.stdE.2.1.trans h.Q_le_M
  have hSUM : S ⊓ U ≤ M := inf_le_left.trans hSM
  have hN : normalizer ((S ⊓ U) : Set G) ≤ M :=
    NineNineOne.normalizer_le h.setting.maxLocal hU hEM h.stdE.2.2.1 h.stdE.2.2.2.1
      (by simpa using h.stdE.2.2.2.2) (le_inf hES hEU) hSUM
  have hUM : U ≤ M := hUS.trans (sup_le h.relPPrimeCore_le hSUM)
  exact hF.trans (sup_le hUM (inf_le_right.trans hN))

theorem not_starImg_le_pCore (h : NineSetting G M p Q H E 2) (hp : p ∉ sigmaM G M)
    (hU : NineNineOne M p) : ¬ starImg p H E ≤ CFSG.pCore p (StarGroup p H) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  intro hle
  let R : Subgroup G := ((CFSG.pCore p (StarGroup p H)).comap
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))).map H.subtype
  have hRsub : R.subgroupOf H =
      (CFSG.pCore p (StarGroup p H)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
    dsimp [R]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hRH : R ≤ H := Subgroup.map_subtype_le _
  have hRnorm : (R.subgroupOf H).Normal := by
    rw [hRsub]
    infer_instance
  have hOleR : relPPrimeCore p H ≤ R := by
    rw [relPPrimeCore_eq_map' h.prime H]
    apply Subgroup.map_mono
    intro x hx
    refine Subgroup.mem_comap.mpr ?_
    have hxO : x ∈ primeComplementCore (G := ↥H) p := hx
    have hx' : x ∈ (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).ker := by
      rwa [QuotientGroup.ker_mk']
    rw [MonoidHom.mem_ker.mp hx']
    exact (CFSG.pCore p (StarGroup p H)).one_mem
  have hstarR : starImg p H R = CFSG.pCore p (StarGroup p H) := by
    change ((R.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))) = CFSG.pCore p (StarGroup p H)
    rw [hRsub, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hUpR : IsPGroup p ↥(starImg p H R) := by
    rw [hstarR]
    exact CFSG.pCore_isPGroup
  have hER : E ≤ R := by
    intro e he
    have heH : e ∈ H := h.stdE.2.1.trans h.Q_le_H he
    have hπ : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ⟨e, heH⟩ ∈
        CFSG.pCore p (StarGroup p H) :=
      hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr he))
    exact ⟨⟨e, heH⟩, Subgroup.mem_comap.mpr hπ, rfl⟩
  obtain ⟨P, hQP, hP⟩ : ∃ P : Subgroup G, Q ≤ P ∧
      CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) := by
    have hQinf : Q ≤ H ⊓ M := le_inf h.Q_le_H h.Q_le_M
    have hQp : IsPGroup p (Q.subgroupOf (H ⊓ M)) :=
      (QSet.isPGroup_of_mem h.mem_Q).comap_subtype (K := H ⊓ M)
    obtain ⟨T, hQT⟩ := hQp.exists_le_sylow
    refine ⟨(T : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype, ?_, ⟨T, rfl⟩⟩
    intro q hq
    exact ⟨⟨q, hQinf hq⟩, hQT (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  obtain ⟨hPH, hN⟩ := h.isSylowOf_of_NineNineOne hp hU hP
  have hPM : P ≤ M := hP.le.trans inf_le_right
  have hEP : E ≤ P := h.stdE.2.1.trans hQP
  exact h.not_le (le_of_frattini (B := H) (U := R) (S := P) h hU le_rfl hRH hRnorm hOleR
    hUpR hPH hPM hEP hER)

end NineSetting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
