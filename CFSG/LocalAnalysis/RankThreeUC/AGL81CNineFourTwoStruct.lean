module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenComp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple (relPPrimeCore_eq_map)

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p k : ℕ}

private theorem le_of_starImg_le (s : NineSettingGen G M p Q H E k) {A : Subgroup G} (hAH : A ≤ H)
    (hA : starImg p H A ≤ starImg p H M) : A ≤ M := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  have h1 : A.subgroupOf H ≤ M.subgroupOf H ⊔ CFSG.pPrimeCore p ↥H := by
    have h2 : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ≤
        (M.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := hA
    have h3 := Subgroup.map_le_iff_le_comap.mp h2
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h3
  calc A = (A.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hAH).symm
    _ ≤ (M.subgroupOf H ⊔ CFSG.pPrimeCore p ↥H).map H.subtype := Subgroup.map_mono h1
    _ = (M.subgroupOf H).map H.subtype ⊔ (CFSG.pPrimeCore p ↥H).map H.subtype := by
          rw [Subgroup.map_sup]
    _ ≤ M := by
          refine sup_le ?_ ?_
          · rw [Subgroup.subgroupOf_map_subtype]
            exact inf_le_left
          · change (CFSG.pPrimeCore p ↥H).map H.subtype ≤ M
            rw [← relPPrimeCore_eq_map s.prime H]
            exact s.relPPrimeCore_le

private theorem exists_le_starImg_eq {P : Subgroup G}
    (hPH : P ≤ H) (hPp : IsPGroup p P) {B : Subgroup (StarGroup p H)} (hB : B ≤ starImg p H P) :
    ∃ D : Subgroup G, D ≤ P ∧ IsPGroup p D ∧ starImg p H D = B := by
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let P_H : Subgroup ↥H := P.subgroupOf H
  let B_H : Subgroup ↥H := P_H ⊓ B.comap (QuotientGroup.mk' O)
  have hB_H_le : B_H ≤ P_H := inf_le_left
  have hB_H_p : IsPGroup p B_H := (hPp.comap_subtype (K := H)).to_le hB_H_le
  have hmap : B_H.map (QuotientGroup.mk' O) = B := by
    refine le_antisymm (fun x hx => ?_) (fun b hb => ?_)
    · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_comap.mp hy.2
    · obtain ⟨q, hqP, hqb⟩ := Subgroup.mem_map.mp (hB hb)
      exact Subgroup.mem_map.mpr ⟨q, ⟨hqP, Subgroup.mem_comap.mpr (by rw [hqb]; exact hb)⟩, hqb⟩
  refine ⟨B_H.map H.subtype, ?_, hB_H_p.map H.subtype, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hPH]
    exact Subgroup.map_mono hB_H_le
  · have hsub : (B_H.map H.subtype).subgroupOf H = B_H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective B_H
    unfold starImg
    rw [hsub]
    exact hmap

private theorem normalizer_starImg_le (s : NineSettingGen G M p Q H E k) {D : Subgroup G}
    (hDH : D ≤ H) (hD : IsPGroup p D) (hN : Subgroup.normalizer (D : Set G) ≤ M) :
    Subgroup.normalizer (starImg p H D : Set (StarGroup p H)) ≤ starImg p H M := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  haveI : Fact (IsPGroup p ↥(D.subgroupOf H)) := ⟨hD.comap_subtype (K := H)⟩
  have hcop : Nat.Coprime p (Nat.card O) := primeComplementCore_coprime p
  have hnorm := CFSG.normalizer_map_quotient_eq_map_normalizer (G := ↥H) (p := p)
    (D.subgroupOf H) O inferInstance hcop
  have hstar : starImg p H D = (D.subgroupOf H).map π := rfl
  rw [hstar, hnorm]
  have hNle : (Subgroup.normalizer (D.subgroupOf H)).map H.subtype ≤ M := by
    rw [← Subgroup.subgroupOf_normalizer_eq hDH]
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left.trans hN
  have hsub : ((Subgroup.normalizer (D.subgroupOf H)).map H.subtype).subgroupOf H =
      Subgroup.normalizer (D.subgroupOf H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  calc (Subgroup.normalizer (D.subgroupOf H)).map π
      = starImg p H ((Subgroup.normalizer (D.subgroupOf H)).map H.subtype) := by
        unfold starImg
        rw [hsub]
    _ ≤ starImg p H M := Subgroup.map_mono (Subgroup.comap_mono hNle)

private theorem centralizer_starImg_le (s : NineSettingGen G M p Q H E k) {D : Subgroup G}
    (hDH : D ≤ H) (hD : IsPGroup p D) (hC : Subgroup.centralizer (D : Set G) ≤ M) :
    Subgroup.centralizer (starImg p H D : Set (StarGroup p H)) ≤ starImg p H M := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  haveI : Fact (IsPGroup p ↥(D.subgroupOf H)) := ⟨hD.comap_subtype (K := H)⟩
  have hcop : Nat.Coprime p (Nat.card O) := primeComplementCore_coprime p
  have hcent := CFSG.centralizer_map_quotient_eq_map_centralizer (G := ↥H) (p := p)
    (D.subgroupOf H) O inferInstance hcop
  have hstar : starImg p H D = (D.subgroupOf H).map π := rfl
  rw [hstar, hcent]
  have hCle : (Subgroup.centralizer (D.subgroupOf H)).map H.subtype ≤ M := by
    have hsub : (Subgroup.centralizer (D.subgroupOf H)).map H.subtype ≤
        Subgroup.centralizer (D : Set G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro d hd
      exact congrArg Subtype.val (hy ⟨d, hDH hd⟩ (Subgroup.mem_subgroupOf.mpr hd))
    exact hsub.trans hC
  have hsub : ((Subgroup.centralizer (D.subgroupOf H)).map H.subtype).subgroupOf H =
      Subgroup.centralizer (D.subgroupOf H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  calc (Subgroup.centralizer (D.subgroupOf H)).map π
      = starImg p H ((Subgroup.centralizer (D.subgroupOf H)).map H.subtype) := by
        unfold starImg
        rw [hsub]
    _ ≤ starImg p H M := Subgroup.map_mono (Subgroup.comap_mono hCle)

private theorem starImg_M_ne_top (s : NineSettingGen G M p Q H E k) :
    starImg p H M ≠ ⊤ := by
  intro htop
  have hHH : starImg p H H ≤ starImg p H M := by
    rw [starImg_self]
    exact le_of_eq htop.symm
  exact s.not_le (le_of_starImg_le s le_rfl hHH)

private theorem starImg_P_ne_bot (s : NineSettingGen G M p Q H E k) (hp : p ∈ sigmaM G M)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M)) :
    starImg p H P ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  have hPH : CFSG.ABGLocalTools.IsSylowOf p P H :=
    (s.isSylowOf_of_isSylowOf_inf hp hP).1
  have hPp : IsPGroup p P := hPH.isPGroup
  have hPHle : P ≤ H := hPH.le
  have hQne : Q ≠ ⊥ := by
    intro hbot
    obtain ⟨F, hFQ, -, hFcard⟩ := CFSG.SectionRank.exists_pRank s.prime.one_lt Q
    have hbig : 1 < Nat.card F := by
      rw [hFcard]
      exact Nat.one_lt_pow (by have := QSet.two_le_pRank_of_mem s.mem_Q; omega) s.prime.one_lt
    have hle : F ≤ ⊥ := hbot ▸ hFQ
    rw [le_bot_iff.mp hle, Subgroup.card_bot] at hbig
    exact lt_irrefl 1 hbig
  have hpdvdH : p ∣ Nat.card H := by
    have hd : p ∣ Nat.card Q :=
      (QSet.isPGroup_of_mem s.mem_Q).card_eq_or_dvd.resolve_left
        fun h => hQne (Subgroup.card_eq_one.mp h)
    exact hd.trans (Subgroup.card_dvd_of_le s.Q_le_H)
  have hPne : P ≠ ⊥ := by
    have hcard : Nat.card P = p ^ (Nat.card H).factorization p := hPH.card_eq
    have hfact : 0 < (Nat.card H).factorization p :=
      s.prime.factorization_pos_of_dvd Nat.card_pos.ne' hpdvdH
    have hdvd : p ∣ Nat.card P := by
      rw [hcard]
      exact dvd_pow_self p hfact.ne'
    intro hbot
    rw [hbot, Subgroup.card_bot] at hdvd
    exact s.prime.ne_one (Nat.dvd_one.mp hdvd)
  intro hbot
  have hle : P.subgroupOf H ≤ primeComplementCore (G := ↥H) p := by
    intro x hx
    have hx' : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) x ∈ starImg p H P :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hx'
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hx')
  have hP_Hp : IsPGroup p (P.subgroupOf H) := hPp.comap_subtype (K := H)
  have hcnt : p ∣ Nat.card (P.subgroupOf H) := by
    rcases hP_Hp.card_eq_or_dvd with h | h
    · refine absurd (Subgroup.card_eq_one.mp h) ?_
      intro hb
      apply hPne
      have := congrArg (Subgroup.map H.subtype) hb
      rwa [Subgroup.map_subgroupOf_eq_of_le hPHle, Subgroup.map_bot] at this
    · exact h
  exact (s.prime.coprime_iff_not_dvd).mp (primeComplementCore_coprime p)
    (hcnt.trans (Subgroup.card_dvd_of_le hle))

private theorem centralizer_starImg_singleton_le (s : NineSettingGen G M p Q H E k)
    (hΓ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M))
    {x : StarGroup p H} (hxP : x ∈ starImg p H P) (hxord : orderOf x = p) :
    Subgroup.centralizer ({x} : Set (StarGroup p H)) ≤ starImg p H M := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  have hPHle : P ≤ H := hP.le.trans inf_le_left
  have hPp : IsPGroup p P := hP.isPGroup
  have hB : Subgroup.zpowers x ≤ starImg p H P := Subgroup.zpowers_le.mpr hxP
  obtain ⟨D, hDP, hDp, hDstar⟩ := exists_le_starImg_eq hPHle hPp hB
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hBbot : Subgroup.zpowers x = ⊥ := by
      rw [← hDstar, hbot]
      simp [starImg]
    have hx1 : x = 1 := Subgroup.zpowers_eq_bot.mp hBbot
    rw [hx1, orderOf_one] at hxord
    exact s.prime.one_lt.ne hxord
  have hrank : 1 ≤ CFSG.Open.pRank p D :=
    CFSG.AGLEmbedding.one_le_pRank_of_isPGroup_of_ne_bot s.prime hDp hDne
  have hND : Subgroup.normalizer (D : Set G) ≤ M :=
    (gamma_le_iff 1 p P M).mp (hΓ P hP) D hDP hrank
  have hCD : Subgroup.centralizer (D : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer (D : Set G)).trans hND
  have hCH : Subgroup.centralizer (starImg p H D : Set (StarGroup p H)) ≤ starImg p H M :=
    centralizer_starImg_le s (hDP.trans hPHle) hDp hCD
  rw [hDstar, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hCH
  exact hCH

private theorem isStronglyPEmbedded_starImg (s : NineSettingGen G M p Q H E k)
    (hp : p ∈ sigmaM G M)
    (hΓ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M)) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p (starImg p H M) := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  obtain ⟨hPH, hPQ⟩ := s.isSylowOf_of_isSylowOf_inf hp hP
  have hPp : IsPGroup p P := hPH.isPGroup
  have hPM : P ≤ M := hP.le.trans inf_le_right
  have hPY : starImg p H P ≤ starImg p H M := Subgroup.map_mono (Subgroup.comap_mono hPM)
  have hPstar : CFSG.ABGLocalTools.IsSylowOf p (starImg p H P) ⊤ := by
    simpa only [starImg_self] using isSylowOf_starImg s.prime (le_refl H) hPH
  refine CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le
    (s := p) (M := starImg p H M) (S := starImg p H P) (starImg_M_ne_top s) ?_
    (starImg_P_ne_bot s hp hP) ?_ ?_
  · refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPY, hPstar.isPGroup, ?_⟩
    have hnotdvd : ¬ p ∣ (starImg p H P).index := by
      have := (CFSG.ABGLocalTools.isSylowOf_iff.mp hPstar).2.2
      rwa [Subgroup.relIndex_top_right] at this
    exact fun h => hnotdvd (h.trans (Subgroup.relIndex_dvd_index_of_le hPY))
  · have hrank : 1 ≤ CFSG.Open.pRank p P := by
      have h2 := QSet.two_le_pRank_of_mem hPQ
      omega
    exact normalizer_starImg_le s hPH.le hPp ((gamma_le_iff 1 p P M).mp (hΓ P hP) P le_rfl hrank)
  · exact fun x hx hxord => centralizer_starImg_singleton_le s hΓ hP hx hxord

private theorem component_starImg (s : NineSettingGen G M p Q H E k)
    (hL : ¬ pLayerIn p H ≤ M) (hp : p ∈ sigmaM G M)
    (hΓ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M) :
    ∃ C : Subgroup (StarGroup p H), CFSG.IsComponent C ∧ C.Normal ∧
      CFSG.layer (StarGroup p H) = C ∧ CFSG.generalizedFitting (StarGroup p H) = C ∧
      IsSimpleGroup ↥C ∧ Subgroup.centralizer (C : Set (StarGroup p H)) = ⊥ ∧
      (∀ C' : Subgroup (StarGroup p H), CFSG.IsComponent C' → C' = C) := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (H ⊓ M)
  have hO : CFSG.pPrimeCore p (StarGroup p H) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) p
  have hY : CFSG.RankThree.PartOne.IsStronglyPEmbedded p (starImg p H M) :=
    isStronglyPEmbedded_starImg s hp hΓ hP
  have hF := CFSG.RankThree.PartOne.Sec1511.spe_fstar s.prime hO hY
  have hpcore : CFSG.pCore p (StarGroup p H) = ⊥ :=
    CFSG.RankThree.PartOne.Sec1511.pCore_eq_bot_of_spe s.prime hY
  have hfitting : CFSG.fittingSubgroup (StarGroup p H) = ⊥ := by
    rw [CFSG.Fitting_eq_pcore (StarGroup p H) p hO]
    exact hpcore
  have hF_eq : CFSG.generalizedFitting (StarGroup p H) = CFSG.layer (StarGroup p H) := by
    rw [CFSG.generalizedFitting.eq_sup, hfitting, bot_sup_eq]
  have hlayer_ne : CFSG.layer (StarGroup p H) ≠ ⊥ := by
    intro hbot
    exact hL (by
      rw [show pLayerIn p H = ⊥ from (pLayerIn_eq_bot_iff s.prime H).mpr hbot]
      exact bot_le)
  obtain ⟨C, hC⟩ : ∃ C : Subgroup (StarGroup p H), CFSG.IsComponent C := by
    by_contra h
    exact hlayer_ne (CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => h ⟨K, hK⟩)
  have hCuniq : ∀ C' : Subgroup (StarGroup p H), CFSG.IsComponent C' → C' = C :=
    fun C' hC' => CFSG.RankThree.PartOne.Sec1511.components_unique s.prime hO hY hC' hC
  have hlayer_eq : CFSG.layer (StarGroup p H) = C := by
    rw [CFSG.layer.eq_sSup]
    have hset : {K : Subgroup (StarGroup p H) | CFSG.IsComponent K} = {C} := by
      ext K
      constructor
      · intro hK
        exact hCuniq K hK
      · intro hK
        rw [Set.mem_singleton_iff.mp hK]
        exact hC
    rw [hset, sSup_singleton]
  have hCsimple : IsSimpleGroup ↥C := by
    have h := hF.1
    rwa [hF_eq, hlayer_eq] at h
  have hCcent : Subgroup.centralizer (C : Set (StarGroup p H)) = ⊥ := by
    have h := hF.2.2.2
    rwa [hF_eq, hlayer_eq] at h
  have hNormalC : C.Normal := by
    have h := hF.2.2.1
    rwa [hF_eq, hlayer_eq] at h
  have hF_C : CFSG.generalizedFitting (StarGroup p H) = C := by
    rw [hF_eq, hlayer_eq]
  exact ⟨C, hC, hNormalC, hlayer_eq, hF_C, hCsimple, hCcent, hCuniq⟩

private theorem exists_unique_pComponent (s : NineSettingGen G M p Q H E k)
    (hL : ¬ pLayerIn p H ≤ M) (hp : p ∈ sigmaM G M)
    (hΓ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M) :
    ∃ L : Subgroup G, IsPComponentIn p L H ∧ ¬ L ≤ M ∧
      (∀ L' : Subgroup G, IsPComponentIn p L' H → L' = L) ∧
      kSub p M H = L ∧ kStar p M H = CFSG.generalizedFitting (StarGroup p H) ∧
      IsSimpleGroup ↥(kStar p M H) ∧
      Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) = ⊥ := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  obtain ⟨C, hC, hNormalC, hlayer_eq, hF_C, hCsimple, hCcent, hCuniq⟩ :=
    component_starImg s hL hp hΓ
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (H ⊓ M)
  have hO : CFSG.pPrimeCore p (StarGroup p H) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) p
  have hY : CFSG.RankThree.PartOne.IsStronglyPEmbedded p (starImg p H M) :=
    isStronglyPEmbedded_starImg s hp hΓ hP
  obtain ⟨L, hLcomp, hLstar⟩ := exists_isPComponentIn_starImg_eq (p := p) (H := H) s.prime hC
  have hLuniq : ∀ L' : Subgroup G, IsPComponentIn p L' H → L' = L := by
    intro L' hL'
    exact eq_of_starImg_eq s.prime hL' hLcomp (by
      rw [hCuniq (starImg p H L') (isComponent_starImg hL'), hLstar])
  have hLM : ¬ L ≤ M := by
    intro hLM
    have hle : C ≤ starImg p H M := by
      rw [← hLstar]
      exact Subgroup.map_mono (Subgroup.comap_mono hLM)
    haveI : C.Normal := hNormalC
    exact (CFSG.RankThree.PartOne.IsStronglyPEmbedded.not_dvd_card_of_normal_le hY hle)
      (CFSG.RankThree.PartOne.Sec1511.p_dvd_card_component hO hC)
  have hkSub : kSub p M H = L := by
    unfold kSub
    rw [if_neg hL]
    have hset : {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M} = {L} := by
      ext Y
      constructor
      · rintro ⟨hY, -⟩
        exact hLuniq Y hY
      · rintro rfl
        exact ⟨hLcomp, hLM⟩
    rw [hset, sSup_singleton]
  have hkStar : kStar p M H = CFSG.generalizedFitting (StarGroup p H) := by
    rw [kStar_eq_starImg, hkSub, hF_C, hLstar]
  have hkStarSimple : IsSimpleGroup ↥(kStar p M H) := by
    rw [hkStar, hF_C]
    exact hCsimple
  have hkStarCent : Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) = ⊥ := by
    rw [hkStar, hF_C]
    exact hCcent
  exact ⟨L, hLcomp, hLM, hLuniq, hkSub, hkStar, hkStarSimple, hkStarCent⟩

private theorem xSub_eq_primeComplementCore (hcent :
    Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) = ⊥) :
    xSub p M H = (primeComplementCore (G := ↥H) p).map H.subtype := by
  unfold xSub
  unfold CFSG.AGLEmbedding.d1PlusCore
  rw [hcent]
  congr 1
  ext z
  exact QuotientGroup.eq_one_iff z

theorem nineFourTwo_structure {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}
    (s : NineSettingGen G M p Q H E 2) (hp : p ∈ sigmaM G M) (hL : ¬ pLayerIn p H ≤ M)
    (hΓ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M) :
    (∃ L : Subgroup G, IsPComponentIn p L H ∧ ¬ L ≤ M ∧ kSub p M H = L ∧
        ∀ L' : Subgroup G, IsPComponentIn p L' H → L' = L) ∧
      ((kSub p M H).subgroupOf H).Normal ∧ xSub p M H ≤ M ∧
      Nat.Coprime p (Nat.card (xSub p M H)) ∧ IsSimpleGroup ↥(kStar p M H) ∧
      Subgroup.centralizer (kStar p M H : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  obtain ⟨L, hLcomp, hLM, hLuniq, hkSub, hkStar, hkStarSimple, hkStarCent⟩ :=
    exists_unique_pComponent s hL hp hΓ
  have hkNormal : ((kSub p M H).subgroupOf H).Normal := by
    rw [hkSub]
    have huniq' : ∀ y ∈ H, L.map (MulAut.conj y).toMonoidHom = L := fun y hy =>
      hLuniq _ (isPComponentIn_conj hLcomp hy)
    rw [Subgroup.normal_subgroupOf_iff hLcomp.1]
    intro x k hx hk
    have hmap : L.map (MulAut.conj k).toMonoidHom = L := huniq' k hk
    have hmem : k * x * k⁻¹ ∈ L.map (MulAut.conj k).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hmap] at hmem
  have hxSub_eq := xSub_eq_primeComplementCore (M := M) (H := H) (p := p) hkStarCent
  have hxSubM : xSub p M H ≤ M := by
    rw [hxSub_eq]
    change (CFSG.pPrimeCore p ↥H).map H.subtype ≤ M
    rw [← relPPrimeCore_eq_map s.prime H]
    exact s.relPPrimeCore_le
  have hxSubCop : Nat.Coprime p (Nat.card (xSub p M H)) := by
    rw [hxSub_eq, Subgroup.card_map_of_injective H.subtype_injective]
    exact primeComplementCore_coprime p
  exact ⟨⟨L, hLcomp, hLM, hkSub, hLuniq⟩, hkNormal, hxSubM, hxSubCop, hkStarSimple, hkStarCent⟩

theorem nineFourTwo_star {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}
    (s : NineSettingGen G M p Q H E 2) (hp : p ∈ sigmaM G M) (hL : ¬ pLayerIn p H ≤ M)
    (hΓ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p (starImg p H M) ∧
      CFSG.generalizedFitting (H ⧸ primeComplementCore (G := H) p) = kStar p M H ∧
      ¬ kStar p M H ≤ starImg p H M ∧
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) p)) ∧
      primeComplementCore (G := ↥H) p ≤ M.subgroupOf H := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (H ⊓ M)
  obtain ⟨hPH, hPQ⟩ := s.isSylowOf_of_isSylowOf_inf hp hP
  obtain ⟨L, hLcomp, hLM, -, hkSub, hkStar, -, -⟩ := exists_unique_pComponent s hL hp hΓ
  refine ⟨isStronglyPEmbedded_starImg s hp hΓ hP, hkStar.symm, ?_, ?_, ?_⟩
  · intro hle
    apply hLM
    apply le_of_starImg_le s hLcomp.1
    have hk : kStar p M H = starImg p H L := by rw [kStar_eq_starImg, hkSub]
    exact hk ▸ hle
  · have h2 : 2 ≤ CFSG.Open.pRank p P := QSet.two_le_pRank_of_mem hPQ
    have hEq : CFSG.Open.pRank p (starImg p H P) = CFSG.Open.pRank p P :=
      pRank_starImg_eq s.prime hPH.le
    calc 2 ≤ CFSG.Open.pRank p (starImg p H P) := by rw [hEq]; exact h2
      _ ≤ CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
          CFSG.SectionRank.pRank_mono s.prime.one_lt le_top
  · have h : (primeComplementCore (G := ↥H) p).map H.subtype ≤ M := by
      change (CFSG.pPrimeCore p ↥H).map H.subtype ≤ M
      rw [← relPPrimeCore_eq_map s.prime H]
      exact s.relPPrimeCore_le
    exact (Subgroup.map_le_iff_le_comap).mp h

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
