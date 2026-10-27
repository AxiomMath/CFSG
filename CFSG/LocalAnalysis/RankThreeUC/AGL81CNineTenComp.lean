module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInner
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenThree
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenCF
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListNormal

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem isSylowOf_starImg (hp : p.Prime) {S B : Subgroup G} (hBH : B ≤ H)
    (hS : CFSG.ABGLocalTools.IsSylowOf p S B) :
    CFSG.ABGLocalTools.IsSylowOf p (starImg p H S) (starImg p H B) := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  obtain ⟨Q, hQ⟩ := hS
  let ι : ↥B →* ↥H := Subgroup.inclusion hBH
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let φ' : ↥B →* ↥(starImg p H B) :=
    (π.comp ι).codRestrict (starImg p H B) (fun b => by
      rw [starImg]
      exact Subgroup.mem_map.mpr ⟨ι b,
        Subgroup.mem_subgroupOf.mpr b.2, rfl⟩)
  have hφ'surj : Function.Surjective φ' := by
    intro y
    obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp y.2
    have hhB : (h : G) ∈ B := Subgroup.mem_subgroupOf.mp hh
    refine ⟨⟨(h : G), hhB⟩, ?_⟩
    apply Subtype.ext
    change π (ι ⟨(h : G), hhB⟩) = (y : StarGroup p H)
    have hι : ι ⟨(h : G), hhB⟩ = h := Subtype.ext rfl
    rw [hι]
    exact hhy
  refine ⟨Q.mapSurjective hφ'surj, ?_⟩
  rw [Sylow.coe_mapSurjective]
  have hQι : Q.map ι = S.subgroupOf H := by
    have hSH' : S ≤ H := by
      rw [← hQ]
      exact (Subgroup.map_subtype_le Q).trans hBH
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_map Q H.subtype ι, Subgroup.subtype_comp_inclusion hBH, hQ,
      Subgroup.subgroupOf_map_subtype S H, inf_eq_left.mpr hSH']
  have hcomp : (starImg p H B).subtype.comp φ' = π.comp ι := by
    ext b
    rfl
  calc (Q.map φ' : Subgroup ↥(starImg p H B)).map (starImg p H B).subtype
      = Q.map ((starImg p H B).subtype.comp φ') :=
        Subgroup.map_map Q (starImg p H B).subtype φ'
    _ = Q.map (π.comp ι) := by rw [hcomp]
    _ = (Q.map ι).map π := (Subgroup.map_map Q π ι).symm
    _ = (S.subgroupOf H).map π := by rw [hQι]
    _ = starImg p H S := rfl

namespace NineSetting

theorem isKGroup_star (h : NineSetting G M p Q H E k) : CFSG.Open.IsKGroup (StarGroup p H) := by
  change CFSG.Open.IsKGroup (↥H ⧸ CFSG.pPrimeCore p ↥H)
  exact h.isKGroup_quotient p

theorem isPClosedMod_component (h713 : SevenOneThree) (h5 : NineTenFivePClosed)
    (h : NineSetting G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C) :
    IsPClosedMod p ((C ⊔ centralizer (C : Set (StarGroup p H))).subgroupOf
      (normalizer (C : Set (StarGroup p H)))) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hp3le : 3 ≤ p := by
    have h2 : 2 ≤ p := h.prime.two_le
    exact lt_of_le_of_ne h2 (Ne.symm h.ne_two)
  rcases eq_or_lt_of_le hp3le with hp3eq | hp3lt
  · subst p
    let N : Subgroup (StarGroup 3 H) := normalizer (C : Set (StarGroup 3 H))
    have hKN : CFSG.Open.IsKGroup ↥N := h.isKGroup_star.subgroup N
    have hcomp : CFSG.IsComponent (C.subgroupOf N) :=
      CFSG.LocalCores.component_overgroup hC Subgroup.le_normalizer
    have hnorm : (C.subgroupOf N).Normal := Subgroup.normal_in_normalizer
    have hrank : CFSG.Open.pRank 3 (C.subgroupOf N) = 1 ∨
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) ≤ 2 ∨
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) ≤ 3 :=
      Or.inr (Or.inr ((CFSG.SectionRank.pRank_top_le_of_injective h.prime.one_lt N.subtype
        N.subtype_injective).trans (h.pRank_star_le_three hH2 hp)))
    have hres := h713 ↥N hKN 3 h.prime h.ne_two (C.subgroupOf N) hcomp hnorm hrank
    have heq : (C.subgroupOf N) ⊔ centralizer (C.subgroupOf N : Set ↥N) =
        (C ⊔ centralizer (C : Set (StarGroup 3 H))).subgroupOf N := by
      rw [CFSG.centralizer_subgroupOf_eq C N Subgroup.le_normalizer]
      rw [Subgroup.subgroupOf_sup Subgroup.le_normalizer
        (Subgroup.centralizer_le_normalizer (C : Set (StarGroup 3 H)))]
    rw [heq] at hres
    exact hres
  · have hp5le : 5 ≤ p := by
      have hp4 : p ≠ 4 := by
        rintro rfl
        exact (by decide : ¬ Nat.Prime 4) h.prime
      omega
    rcases eq_or_lt_of_le hp5le with hp5eq | hp5lt
    · subst p
      exact h5 G M Q H E h.toGen hH2 hp C hC
    · let N : Subgroup (StarGroup p H) := normalizer (C : Set (StarGroup p H))
      have hKN : CFSG.Open.IsKGroup ↥N := h.isKGroup_star.subgroup N
      have hcomp : CFSG.IsComponent (C.subgroupOf N) :=
        CFSG.LocalCores.component_overgroup hC Subgroup.le_normalizer
      have hnorm : (C.subgroupOf N).Normal := Subgroup.normal_in_normalizer
      have hrank : CFSG.Open.pRank p (C.subgroupOf N) = 1 ∨
          CFSG.Open.pRank p (⊤ : Subgroup ↥N) ≤ 2 ∨
          CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) ≤ 3 := by
        refine Or.inr (Or.inl ?_)
        refine (CFSG.SectionRank.pRank_top_le_of_injective h.prime.one_lt N.subtype
          N.subtype_injective).trans ?_
        rw [← starImg_self p H, pRank_starImg_eq h.prime le_rfl]
        exact (h.pRank_le_of_mem_H2Fam hH2 hp).2.1 hp5lt
      have hres := h713 ↥N hKN p h.prime h.ne_two (C.subgroupOf N) hcomp hnorm hrank
      have heq : (C.subgroupOf N) ⊔ centralizer (C.subgroupOf N : Set ↥N) =
          (C ⊔ centralizer (C : Set (StarGroup p H))).subgroupOf N := by
        rw [CFSG.centralizer_subgroupOf_eq C N Subgroup.le_normalizer]
        rw [Subgroup.subgroupOf_sup Subgroup.le_normalizer
          (Subgroup.centralizer_le_normalizer (C : Set (StarGroup p H)))]
      rw [heq] at hres
      exact hres

theorem isPClosedMod_layer_sup_centralizer (h713 : SevenOneThree) (h5 : NineTenFivePClosed)
    (h : NineSetting G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hN : ¬ p ∣ (compNormalizer (StarGroup p H)).index) :
    IsPClosedMod p (CFSG.layer (StarGroup p H) ⊔
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.isPClosedMod_layer_sup_centralizer
    (fun C hC => h.isPClosedMod_component h713 h5 hH2 hp hC) hN

theorem isSylowOf_starImg_top (h : NineSetting G M p Q H E k)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    CFSG.ABGLocalTools.IsSylowOf p (starImg p H Q) ⊤ := by
  simpa only [starImg_self] using isSylowOf_starImg h.prime le_rfl hQ

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
    · show (Subgroup.comap C.subtype
          ((primeComplementCore (G := ↥C) p).map C.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      infer_instance
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card

theorem normalizer_starImg_le (h : NineSetting G M p Q H E k) {S : Subgroup G} (hSH : S ≤ H)
    (hS : IsPGroup p S) (hN : normalizer (S : Set G) ≤ M) :
    normalizer (starImg p H S : Set (StarGroup p H)) ≤ starImg p H M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  let S' : Subgroup ↥H := S.subgroupOf H
  let T : Subgroup ↥H := S' ⊔ O
  have hS'p : IsPGroup p S' := hS.comap_subtype (K := H)
  have hOcop : ¬ p ∣ Nat.card O :=
    (h.prime.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥H))
  have hS'botO : S' ⊓ O = ⊥ := by
    have hinfp : IsPGroup p ↥(S' ⊓ O) := hS'p.to_le (H := S' ⊓ O) inf_le_left
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hinfp
    have hdvd : p ^ n ∣ Nat.card O := hn ▸ Subgroup.card_dvd_of_le inf_le_right
    have hn0 : n = 0 := by
      by_contra hne
      exact hOcop ((dvd_pow_self p hne).trans hdvd)
    rw [← Subgroup.card_eq_one, hn, hn0, pow_zero]
  have hrel : S'.relIndex T = Nat.card O := by
    change S'.relIndex (S' ⊔ O) = Nat.card O
    rw [sup_comm, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal O S']
    change (S'.subgroupOf O).index = Nat.card O
    have hbot : S'.subgroupOf O = ⊥ := by
      rw [← Subgroup.inf_subgroupOf_right S' O, hS'botO, Subgroup.bot_subgroupOf]
    rw [hbot, Subgroup.index_bot]
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p S' T := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_sup_left, hS'p, by rw [hrel]; exact hOcop⟩
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
  have hT_eq : T = (starImg p H S).comap π := by
    change S' ⊔ O = ((S.subgroupOf H).map π).comap π
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hxT : x ∈ normalizer (T : Set ↥H) := by
    rw [hT_eq, ← Subgroup.comap_normalizer_eq_of_surjective (starImg p H S)
      (QuotientGroup.mk'_surjective O)]
    exact hy
  have hxT' : T.map (MulAut.conj x).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxT
  have hSyl' : CFSG.ABGLocalTools.IsSylowOf p
      (S'.map (MulAut.conj x).toMonoidHom) T := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨?_, hS'p.map _, ?_⟩
    · calc S'.map (MulAut.conj x).toMonoidHom ≤ T.map (MulAut.conj x).toMonoidHom :=
            Subgroup.map_mono le_sup_left
        _ = T := hxT'
    · rw [← hxT', Subgroup.relIndex_map_map_of_injective S' T (MulAut.conj x).injective, hrel]
      exact hOcop
  obtain ⟨k, hkT, hconj⟩ := hSyl.exists_mem_conj hSyl'
  have hkeq : S'.map (MulAut.conj x).toMonoidHom =
      S'.map (MulAut.conj k).toMonoidHom := by
    apply SetLike.ext
    intro z
    rw [hconj z]
    constructor
    · intro hz
      exact Subgroup.mem_map.mpr ⟨k⁻¹ * z * k, hz, by simp [MulAut.conj_apply, mul_assoc]⟩
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      rw [← hwz]
      simpa [MulAut.conj_apply, mul_assoc] using hw
  have hkT' : k ∈ O ⊔ S' := by simpa only [T, sup_comm] using hkT
  obtain ⟨o, hoO, s, hsS', hos⟩ := Subgroup.mem_sup_of_normal_left.mp hkT'
  have hk_eq : k = o * s := hos.symm
  have hs_conj : S'.map (MulAut.conj s).toMonoidHom = S' :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hsS')
  have hconj_mul : (MulAut.conj (o * s)).toMonoidHom =
      (MulAut.conj o).toMonoidHom.comp (MulAut.conj s).toMonoidHom := by
    ext w
    simp [MulAut.conj_apply, mul_assoc]
  have ho_eq : S'.map (MulAut.conj x).toMonoidHom =
      S'.map (MulAut.conj o).toMonoidHom := by
    calc S'.map (MulAut.conj x).toMonoidHom
        = S'.map (MulAut.conj k).toMonoidHom := hkeq
      _ = S'.map (MulAut.conj (o * s)).toMonoidHom := by rw [hk_eq]
      _ = S'.map ((MulAut.conj o).toMonoidHom.comp (MulAut.conj s).toMonoidHom) := by
            rw [hconj_mul]
      _ = (S'.map (MulAut.conj s).toMonoidHom).map (MulAut.conj o).toMonoidHom :=
            (Subgroup.map_map S' (MulAut.conj o).toMonoidHom
              (MulAut.conj s).toMonoidHom).symm
      _ = S'.map (MulAut.conj o).toMonoidHom := by rw [hs_conj]
  have hconj_mul' : (MulAut.conj (o⁻¹ * x)).toMonoidHom =
      (MulAut.conj o⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
    ext w
    simp [MulAut.conj_apply, mul_assoc]
  have hcancel : (MulAut.conj o⁻¹).toMonoidHom.comp (MulAut.conj o).toMonoidHom =
      MonoidHom.id ↥H := by
    ext w
    simp [MulAut.conj_apply, mul_assoc]
  have hzN : o⁻¹ * x ∈ normalizer (S' : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc S'.map (MulAut.conj (o⁻¹ * x)).toMonoidHom
        = S'.map ((MulAut.conj o⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom) := by
            rw [hconj_mul']
      _ = (S'.map (MulAut.conj x).toMonoidHom).map (MulAut.conj o⁻¹).toMonoidHom :=
            (Subgroup.map_map S' (MulAut.conj o⁻¹).toMonoidHom
              (MulAut.conj x).toMonoidHom).symm
      _ = (S'.map (MulAut.conj o).toMonoidHom).map (MulAut.conj o⁻¹).toMonoidHom := by
            rw [ho_eq]
      _ = S'.map ((MulAut.conj o⁻¹).toMonoidHom.comp (MulAut.conj o).toMonoidHom) :=
            Subgroup.map_map S' (MulAut.conj o⁻¹).toMonoidHom (MulAut.conj o).toMonoidHom
      _ = S'.map (MonoidHom.id ↥H) := by rw [hcancel]
      _ = S' := Subgroup.map_id S'
  have hOl : O ≤ M.subgroupOf H := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    have hzR : (z : G) ∈ relPPrimeCore p H := by
      rw [relPPrimeCore_eq_map' h.prime H]
      exact ⟨z, hz, rfl⟩
    exact h.relPPrimeCore_le hzR
  have hzM : o⁻¹ * x ∈ M.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    have hmap : ((o⁻¹ * x : ↥H) : G) ∈ normalizer (S : Set G) := by
      have hzN' := hzN
      rw [← Subgroup.subgroupOf_normalizer_eq hSH] at hzN'
      exact Subgroup.mem_subgroupOf.mp hzN'
    exact hN hmap
  have hxM : x ∈ M.subgroupOf H := by
    have hmem := (M.subgroupOf H).mul_mem (hOl hoO) hzM
    rwa [mul_inv_cancel_left] at hmem
  exact Subgroup.mem_map.mpr ⟨x, hxM, rfl⟩

theorem normalizer_starImg_le_of_le (h : NineSetting G M p Q H E 2) (hU : NineNineOne M p)
    {S : Subgroup G} (hSH : S ≤ H) (hSM : S ≤ M) (hS : IsPGroup p S) (hES : E ≤ S) :
    normalizer (starImg p H S : Set (StarGroup p H)) ≤ starImg p H M :=
  h.normalizer_starImg_le hSH hS
    (NineNineOne.normalizer_le h.setting.maxLocal hU (h.stdE.2.1.trans h.Q_le_M)
      h.stdE.2.2.1 h.stdE.2.2.2.1 (by simpa using h.stdE.2.2.2.2) hES hSM)

theorem not_dvd_index_compNormalizer (h : NineSetting G M p Q H E k)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hQN : starImg p H Q ≤ compNormalizer (StarGroup p H)) :
    ¬ p ∣ (compNormalizer (StarGroup p H)).index := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact not_dvd_index_of_isSylowOf_le (h.isSylowOf_starImg_top hQ) hQN

theorem le_inf_sup_starImg (h713 : SevenOneThree) (h5 : NineTenFivePClosed)
    (h : NineSetting G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hN : ¬ p ∣ (compNormalizer (StarGroup p H)).index) {B S : Subgroup (StarGroup p H)}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S B)
    (hSM : normalizer (S : Set (StarGroup p H)) ≤ starImg p H M) :
    B ≤ (B ⊓ (CFSG.layer (StarGroup p H) ⊔
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)))) ⊔ starImg p H M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  set U : Subgroup (StarGroup p H) := CFSG.layer (StarGroup p H) ⊔
    centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) with hUdef
  have hpc : IsPClosedMod p U := by
    rw [hUdef]
    exact h.isPClosedMod_layer_sup_centralizer h713 h5 hH2 hp hN
  haveI hLc : (CFSG.layer (StarGroup p H)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  haveI hLn : (CFSG.layer (StarGroup p H)).Normal := inferInstance
  haveI hCn : (centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))).Normal :=
    inferInstance
  haveI hUn : U.Normal := by rw [hUdef]; infer_instance
  have hU' : IsPClosedMod p ((B ⊓ U).subgroupOf B) := by
    rw [Subgroup.inf_subgroupOf_left]
    exact IsPClosedMod.comap hpc B.subtype
  have hle := IsPClosedMod.le_sup_normalizer (B := B) (U := B ⊓ U) (P := S)
    inf_le_left (by rw [Subgroup.inf_subgroupOf_left]; infer_instance) hU' hS
  exact hle.trans (sup_le le_sup_left ((inf_le_right.trans hSM).trans le_sup_right))

theorem le_inf_sup_starImg_of_le (h713 : SevenOneThree) (h5 : NineTenFivePClosed)
    (h : NineSetting G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    {B S : Subgroup (StarGroup p H)} (hB : B ≤ compNormalizer (StarGroup p H))
    (hS : CFSG.ABGLocalTools.IsSylowOf p S B)
    (hSM : normalizer (S : Set (StarGroup p H)) ≤ starImg p H M) :
    B ≤ (B ⊓ (CFSG.layer (StarGroup p H) ⊔
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)))) ⊔ starImg p H M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  set U : Subgroup (StarGroup p H) := CFSG.layer (StarGroup p H) ⊔
    centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) with hUdef
  have hU'N : IsPClosedMod p (U.subgroupOf (compNormalizer (StarGroup p H))) := by
    rw [hUdef]
    exact isPClosedMod_layer_sup_centralizer_subgroupOf
      (fun C hC => h.isPClosedMod_component h713 h5 hH2 hp hC)
  haveI hLc : (CFSG.layer (StarGroup p H)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  haveI hLn : (CFSG.layer (StarGroup p H)).Normal := inferInstance
  haveI hCn : (centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))).Normal :=
    inferInstance
  haveI hUn : U.Normal := by rw [hUdef]; infer_instance
  have hU' : IsPClosedMod p ((B ⊓ U).subgroupOf B) := by
    rw [Subgroup.inf_subgroupOf_left,
      ← Subgroup.comap_inclusion_subgroupOf hB U]
    exact IsPClosedMod.comap hU'N (Subgroup.inclusion hB)
  have hle := IsPClosedMod.le_sup_normalizer (B := B) (U := B ⊓ U) (P := S)
    inf_le_left (by rw [Subgroup.inf_subgroupOf_left]; infer_instance) hU' hS
  exact hle.trans (sup_le le_sup_left ((inf_le_right.trans hSM).trans le_sup_right))

theorem top_le_layer_sup_centralizer_sup (h713 : SevenOneThree) (h5 : NineTenFivePClosed)
    (h : NineSetting G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) (hNQ : normalizer (Q : Set G) ≤ M)
    (hQN : starImg p H Q ≤ compNormalizer (StarGroup p H)) :
    (⊤ : Subgroup (StarGroup p H)) ≤ (CFSG.layer (StarGroup p H) ⊔
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))) ⊔ starImg p H M := by
  have h := le_inf_sup_starImg h713 h5 h hH2 hp
    (h.not_dvd_index_compNormalizer hQ hQN) (B := ⊤) (S := starImg p H Q)
    (h.isSylowOf_starImg_top hQ)
    (h.normalizer_starImg_le h.Q_le_H hQ.isPGroup hNQ)
  simpa using h

end NineSetting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
