module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Cover
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Facts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

theorem a7f_map_conj_mul {X : Type*} [Group X] (K : Subgroup X) (a b : X) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem a7f_le_range_conj {X : Type*} [Group X] {ι : X →* Perm (Fin 7)}
    (hA7 : alternatingGroup (Fin 7) ≤ ι.range) (σ : Perm (Fin 7)) :
    alternatingGroup (Fin 7) ≤ ((MulAut.conj σ).toMonoidHom.comp ι).range := by
  intro a ha
  have hna : σ⁻¹ * a * σ ∈ alternatingGroup (Fin 7) := by
    change Perm.sign _ = 1
    have : Perm.sign a = 1 := ha
    simp [this]
  obtain ⟨x, hx⟩ := hA7 hna
  refine ⟨x, ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    MulAut.conj_apply, hx]
  group

theorem a7f_exists_conj {X : Type} [Group X] [Finite X] {ι : X →* Perm (Fin 7)}
    (hι : Function.Injective ι) (hA7 : alternatingGroup (Fin 7) ≤ ι.range) {D V : Subgroup X}
    (hD : Nat.card D = 9) (hV : rankTwoMaximalInvariantTwoSubgroup D V) :
    ∃ σ : Perm (Fin 7), (D.map ι).map (MulAut.conj σ).toMonoidHom = eNine ∧
      (V.map ι).map (MulAut.conj σ).toMonoidHom = vOne := by
  classical
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS7 : (Nat.card (Perm (Fin 7))).factorization 3 = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide +kernel
  have hDι : Nat.card (D.map ι) = 9 := by rw [Subgroup.card_map_of_injective hι, hD]
  have hsylD : CFSG.ABGLocalTools.IsSylowOf 3 (D.map ι) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by rw [hDι, Subgroup.card_top, hS7]; norm_num)
  have hsylE : CFSG.ABGLocalTools.IsSylowOf 3 eNine ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top
      (by rw [card_eNine, Subgroup.card_top, hS7]; norm_num)
  obtain ⟨k, -, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hsylD hsylE
  have hDe : (D.map ι).map (MulAut.conj k).toMonoidHom = eNine := by
    ext x
    rw [mem_map_conj_iff_implicit]
    exact (hk x).symm
  set W : Subgroup (Perm (Fin 7)) := (V.map ι).map (MulAut.conj k).toMonoidHom with hW
  have hW4 : Nat.card W = 4 := by
    rw [hW, Subgroup.card_map_of_injective (MulAut.conj k).injective,
      Subgroup.card_map_of_injective hι, (a7_structure_of_embedding hι hA7 hD hV).1]
  have hEN : eNine ≤ normalizer (W : Set (Perm (Fin 7))) := by
    rw [← hDe]
    exact (Subgroup.map_mono ((Subgroup.map_mono hV.2.1).trans
      (Subgroup.le_normalizer_map ι))).trans (Subgroup.le_normalizer_map _)
  have hW3 : ¬ 3 ∣ Nat.card W := by
    rw [hW4]
    norm_num
  rcases le_vOne_or_le_vTwo hW3 (hEN cOne_mem_eNine) (hEN cTwo_mem_eNine) with h | h
  · exact ⟨k, hDe, Subgroup.eq_of_le_of_card_ge h (by rw [card_vOne, hW4])⟩
  · have hWv : W = vTwo := Subgroup.eq_of_le_of_card_ge h (by rw [card_vTwo, hW4])
    refine ⟨rFour⁻¹ * k, ?_, ?_⟩
    · rw [a7f_map_conj_mul, hDe]
      exact mem_normalizer_iff_map_conj_eq.mp (inv_mem rFour_mem_normalizer_eNine)
    · rw [a7f_map_conj_mul, ← hW, hWv, ← map_conj_rFour_vOne]
      exact map_conj_map_conj_inv vOne rFour

theorem a7f_exists_hom {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    (hK : (3 : ℕ).Coprime (Nat.card K))
    (hKmax : ∀ N : Subgroup Y, N.Normal → (3 : ℕ).Coprime (Nat.card N) → N ≤ K)
    (h3 : CFSG.pCore 3 (Y ⧸ K) = ⊥)
    (hrk : ∀ E : Subgroup Y, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)
    {J : Subgroup (Y ⧸ K)} (hJ : CFSG.IsComponent J)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7))
    {D V : Subgroup Y} (hD9 : Nat.card D = 9) (hD3 : IsPGroup 3 D)
    (hV : rankTwoMaximalInvariantTwoSubgroup D V) :
    ∃ ι : Y →* Perm (Fin 7), ι.ker = K ∧ alternatingGroup (Fin 7) ≤ ι.range ∧
      D.map ι = eNine ∧ V.map ι = vOne := by
  classical
  have hfact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : Y →* Y ⧸ K := QuotientGroup.mk' K with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hker : π.ker = K := QuotientGroup.ker_mk' K
  have hkerc : (3 : ℕ).Coprime (Nat.card π.ker) := by rw [hker]; exact hK
  have h3' : CFSG.pPrimeCore 3 (Y ⧸ K) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro N hN hNc
    have hNt : (N.comap π).Normal := hN.comap π
    have hcop : (3 : ℕ).Coprime (Nat.card (N.comap π)) := by
      rw [card_comap_eq_card_ker_mul π hπs N]
      exact hkerc.mul_right hNc
    have hle : N.comap π ≤ K := hKmax _ hNt hcop
    rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective hπs N]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff x).mpr (hle hx)
  have hrk' : ∀ E : Subgroup (Y ⧸ K), CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hE
    obtain ⟨E', hE', hcard⟩ := exists_isElemAbelian_card_eq_of_map Nat.prime_three π hπs hkerc hE
    rw [← hcard]
    exact hrk E' hE'
  obtain ⟨ι₀, hι₀, hA7⟩ := exists_injective_hom_perm_seven h3 h3' hrk' hJ e
  have hinfD : D ⊓ π.ker = ⊥ := inf_eq_bot_of_isPGroup_of_coprime Nat.prime_three hD3 hkerc
  have hDbar9 : Nat.card (D.map π) = 9 := by
    have := card_eq_card_map_mul_card_inf_ker π D
    rw [hinfD, Subgroup.card_bot, mul_one, hD9] at this
    exact this.symm
  have hVbar := rankTwoMaximalInvariantTwoSubgroup_map_of_ker Nat.prime_three (by norm_num) π hπs
    hkerc hD3 hV
  obtain ⟨σ, hσD, hσV⟩ := a7f_exists_conj hι₀ hA7 hDbar9 hVbar
  refine ⟨(MulAut.conj σ).toMonoidHom.comp (ι₀.comp π), ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj σ).injective, ← MonoidHom.comap_ker,
      ι₀.ker_eq_bot hι₀, MonoidHom.comap_bot, hker]
  · intro a ha
    obtain ⟨x, hx⟩ := a7f_le_range_conj hA7 σ ha
    obtain ⟨y, rfl⟩ := hπs x
    exact ⟨y, hx⟩
  · rw [← Subgroup.map_map, ← Subgroup.map_map]
    exact hσD
  · rw [← Subgroup.map_map, ← Subgroup.map_map]
    exact hσV

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a7f_map_conj_le {H V N : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hVH : V ≤ H)
    (hV : (V.subgroupOf H).map ι ≤ alternatingGroup (Fin 7))
    (hN : alternatingGroup (Fin 7) ≤ (N.subgroupOf H).map ι) {n : G} (hn : n ∈ H) :
    V.map (MulAut.conj n).toMonoidHom ≤ N ⊔ ι.ker.map H.subtype := by
  rintro _ ⟨v, hv, rfl⟩
  set x : ↥H := ⟨n, hn⟩ * ⟨v, hVH hv⟩ * (⟨n, hn⟩ : ↥H)⁻¹ with hx
  have hxv : (x : G) = (MulAut.conj n).toMonoidHom v := by
    simp [hx, MulAut.conj_apply]
  have hιv : ι ⟨v, hVH hv⟩ ∈ alternatingGroup (Fin 7) :=
    hV ⟨⟨v, hVH hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  have hιx : ι x ∈ alternatingGroup (Fin 7) := by
    rw [hx, map_mul, map_mul, map_inv]
    exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem _ hιv _
  obtain ⟨y, hyN, hyx⟩ := hN hιx
  have hk : y⁻¹ * x ∈ ι.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  rw [← hxv, show (x : G) = (y : G) * ((y⁻¹ * x : ↥H) : G) by simp]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hyN) ⟨y⁻¹ * x, hk, rfl⟩

omit [Finite G] in
theorem a7f_isKGroup {H X : Subgroup G} (hK : CFSG.Open.IsKProper G) (hH : H ≠ ⊤)
    (hXH : X ≤ H) : CFSG.Open.IsKGroup ↥X := by
  intro K L _ _ hsimple hnab
  exact CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hK X (ne_top_of_le_ne_top hH hXH) K
    (L.subgroupOf K) inferInstance hsimple hnab

theorem a7f_card_le_nine {H : Subgroup G} (hH : CFSG.Open.pRank 3 H = 2) (E : Subgroup ↥H)
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, by
    have := hE.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hcardG : Nat.card (E.map H.subtype) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hk]
  have hk2 : k ≤ 2 := by
    have := le_pRank_of_isElemAbelian' Nat.prime_three.one_lt (Subgroup.map_subtype_le E)
      (isElemAbelian_map H.subtype hE) hcardG
    rwa [hH] at this
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem IsOptimalRelPair.exists_a7Frame {p : ℕ} {P : Sylow p G} {M D R T H V : Subgroup G}
    (hS : Setting G) (hd : MaximalRelativePair p P M D R T)
    (hopt : IsOptimalRelPair p M D R T H V)
    (hfacts : OptimalRelPairFacts p M D H V) (hp3 : p = 3)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7))
    (hcard : Nat.card V = 4 * Nat.card (pCoreOf 2 H))
    (hn : ∃ n ∈ H, n ∈ normalizer (D : Set G) ∧
      p ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup G)) :
    ∃ ι : ↥H →* Perm (Fin 7), A7Frame D H V ι := by
  subst hp3
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  have hVH : V ≤ H := hfacts.maximal.1
  have hDp : IsPGroup 3 D := P.isPGroup'.to_le hd.ext.obstruction.2.1
  have hDcard : Nat.card D = 9 := by
    have := (hd.ext.isElemAbelian_of_isMulCommutative Nat.prime_three hd.abelian).2
    simpa using this
  obtain ⟨ι, hker, hA7, hDι, hVι⟩ := a7f_exists_hom (primeComplementCore_coprime 3)
    (fun N hN hc => normal_coprime_le_primeComplementCore 3 N hN hc)
    (by exact hfacts.pCore_quotient)
    (a7f_card_le_nine hfacts.pRank_eq) ((CFSG.isComponent_iff_open L).mpr hL) e
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv).trans hDcard)
    (hDp.of_equiv (Subgroup.subgroupOfEquivOfLe hDH).symm)
    (invariantTwoMaximalWithin_internal_global D H V hDH hfacts.maximal)
  have hH : H ≠ ⊤ := by
    have := hS.simple
    exact twoLocal_ne_top hS.nonab H hopt.pair.cand.twoLocal
  refine ⟨ι,
    { D_le := hDH, V_le := hVH, S_le := hfacts.pCore_le, V_two := hfacts.maximal.2.1
      D_norm := hfacts.maximal.2.2.1, D_three := hDp, D_card := hDcard
      H_norm := hfacts.normalizer_pCore, charTwo := hS.charTwo H hopt.pair.cand.twoLocal
      sylow := hfacts.sylow, K_coprime := ?_, card_V := hcard, ker_eq := hker, A7_le := hA7
      D_img := hDι, V_img := hVι, kGroup := fun X hXH => a7f_isKGroup hS.kProper hH hXH
      noCover := ?_, exists_n := hn }⟩
  · rw [a7K, Subgroup.card_map_of_injective H.subtype_injective]
    exact primeComplementCore_coprime 3
  · intro Y hYV hY1 hY hcov
    obtain ⟨n, hnH, hnD, hjoin⟩ := hn
    have hle := a7f_map_conj_le hVH (hVι.le.trans vOne_le_alternatingGroup) hcov hnH
    rw [hker] at hle
    exact hopt.not_map_conj_le_of_normalizer hd hfacts rfl hYV hY1 hY hnH hnD hjoin hle

end CFSG.LocalAnalysis.RankThreeTheoremC
