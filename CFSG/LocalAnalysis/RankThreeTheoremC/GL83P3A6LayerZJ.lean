module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3ZJAny
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Img
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_PComp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux1
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Plumb

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Img
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem le_pCore_of {X : Type} [Group X] {p : ℕ} (K : Subgroup X) (hK : K.Normal)
    (hp : IsPGroup p K) : K ≤ CFSG.pCore p X := by
  unfold CFSG.pCore
  exact le_sSup ⟨hK, hp⟩

theorem le_pPrimeCore_of {X : Type} [Group X] {p : ℕ} (K : Subgroup X) (hK : K.Normal)
    (hc : Nat.Coprime p (Nat.card K)) : K ≤ CFSG.pPrimeCore p X := by
  unfold CFSG.pPrimeCore
  exact le_sSup ⟨hK, hc⟩

variable {G : Type} [Group G] [Finite G]

theorem chev_or_alt (hZJ : KFactZJFactorizationAny) (hS : Setting G) {M : Subgroup G}
    (hM2 : IsTwoLocal M) (hMtop : M ≠ ⊤) [((GLBPrimeCore 3 M).subgroupOf M).Normal]
    {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hYO : IsSylowOf 2 (Y ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M))
    (hbig : ∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
      CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M) < 3)
    {E : Subgroup G} (hEM : E ≤ M) (hEel : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    {L : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)} (hLn : L.Normal)
    (hLs : IsSimpleGroup ↥L) (hLnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hLc : centralizer (L : Set (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) = ⊥)
    (hcore : ∀ N : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M), N.Normal →
      Nat.Coprime 3 (Nat.card N) → N = ⊥)
    (hEL : img M (GLBPrimeCore 3 M) E ≤ L) :
    IsChevTwo ↥L ∨ ∃ n : ℕ, Nonempty (↥L ≃* alternatingGroup (Fin n)) := by
  classical
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := GLBPrimeCore 3 M with hOdef
  set R : Subgroup G := Y ⊓ O with hRdef
  set H : Subgroup G := normalizer (R : Set G) ⊓ M with hHdef
  have hOM : O ≤ M := glbPrimeCore_le 3 M
  have hMO : M ≤ normalizer (O : Set G) := le_normalizer_glbPrimeCore 3 M
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
  have hHM : H ≤ M := inf_le_right
  have hRO : R ≤ O := inf_le_right
  have hYR : Y ≤ normalizer (R : Set G) := by
    intro y hy
    refine mem_normalizer_iff.mpr fun z => ?_
    have h1 := mem_normalizer_iff.mp (Subgroup.le_normalizer hy) z
    have h2 := mem_normalizer_iff.mp (hMO (hYM hy)) z
    rw [hRdef, mem_inf, mem_inf, ← h1, ← h2]
  have hYH : Y ≤ H := le_inf hYR hYM
  have hRH : R ≤ H := inf_le_left.trans hYH
  set π := QuotientGroup.mk' (O.subgroupOf M) with hπ
  set θ : ↥H →* M ⧸ O.subgroupOf M := π.comp (Subgroup.inclusion hHM) with hθ
  have hθs : Function.Surjective θ := by
    intro z
    obtain ⟨γ, hγM, hγN, hγ⟩ := GL83P3A6Core.exists_lift hOM hMO hYO z
    exact ⟨⟨γ, hγN, hγM⟩, hγ⟩
  have hθker : θ.ker = O.subgroupOf H := by
    ext h
    simp only [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_inclusion]
  have hOH3 : Nat.Coprime 3 (Nat.card (O.subgroupOf H)) := by
    have : Nat.card (O.subgroupOf H) ∣ Nat.card O := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.coprime_dvd_right this (glbPrimeCore_coprime 3 M)
  have hcoreH : CFSG.pPrimeCore 3 ↥H = θ.ker := by
    apply le_antisymm
    · have hmap : (CFSG.pPrimeCore 3 ↥H).map θ = ⊥ := by
        haveI : (CFSG.pPrimeCore 3 ↥H).Normal := CFSG.pPrimeCore_normal
        refine hcore _ (Subgroup.Normal.map inferInstance θ hθs) ?_
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) CFSG.pPrimeCore_coprime_card
      rwa [Subgroup.map_eq_bot_iff] at hmap
    · rw [hθker]
      exact le_pPrimeCore_of _ (by rw [← hθker]; infer_instance) hOH3
  have hRn : (R.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mpr inf_le_left
  have hR2 : IsPGroup 2 R := hY2.to_le inf_le_left
  have hO2 : CFSG.pCore 2 ↥H = R.subgroupOf H := by
    apply le_antisymm
    · have hle : CFSG.pCore 2 ↥H ≤ O.subgroupOf H := by
        rw [← hθker, ← hcoreH]
        refine le_pPrimeCore_of _ CFSG.pCore_normal ?_
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
        rw [hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      set K₂ : Subgroup G := (CFSG.pCore 2 ↥H).map H.subtype with hK₂
      have hK₂2 : IsPGroup 2 K₂ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map _
      have hK₂O : K₂ ≤ O := by
        rintro _ ⟨k, hk, rfl⟩
        exact hle hk
      have hRK₂ : R ≤ K₂ := by
        intro r hr
        have : (⟨r, hRH hr⟩ : ↥H) ∈ CFSG.pCore 2 ↥H :=
          le_pCore_of _ hRn hR2.comap_subtype (mem_subgroupOf.mpr hr)
        exact ⟨_, this, rfl⟩
      have hK₂R : K₂ = R := hYO.eq_of_le hRK₂ hK₂O hK₂2
      intro h hh
      rw [mem_subgroupOf, ← hK₂R]
      exact ⟨h, hh, rfl⟩
    · exact le_pCore_of _ hRn hR2.comap_subtype
  have hHtop : H ≠ ⊤ := fun h => hMtop (top_le_iff.mp (h ▸ hHM))
  have hsec : CatalogSimpleSections ↥H := catalogSimpleSections_of_isKProper hS.kProper H hHtop
  have hO₂MR : pCoreOf 2 M ≤ R :=
    e9_le_of_normal (pCoreOf_le_glbPrimeCore Nat.prime_two (by norm_num) M)
      (hOM.trans (localGroup_le_normalizer_pCoreOf 2 M)) (pCoreOf_isPGroup 2 M) hYO
  have hcharTwo : centralizer (CFSG.pCore 2 ↥H : Set ↥H) ≤ CFSG.pCore 2 ↥H := by
    rw [hO2]
    intro c hc
    rw [mem_subgroupOf]
    have hcM : (c : G) ∈ M ⊓ centralizer (pCoreOf 2 M : Set G) := by
      refine mem_inf.mpr ⟨hHM c.2, mem_centralizer_iff.mpr fun r hr => ?_⟩
      have := mem_centralizer_iff.mp hc ⟨r, hRH (hO₂MR hr)⟩ (mem_subgroupOf.mpr (hO₂MR hr))
      exact congrArg Subtype.val this
    exact hO₂MR (hS.charTwo M hM2 hcM)
  have hsylow : IsSylowOf 2 (CFSG.pCore 2 ↥H) (CFSG.pPrimeCore 3 ↥H) := by
    rw [hO2, hcoreH, hθker]
    have h1 : IsSylowOf 2 R (H ⊓ O) := hYO.of_le (le_inf hRH hRO) inf_le_right
    have h2 : (R.subgroupOf H).map H.subtype = R := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRH]
    have h3 : (O.subgroupOf H).map H.subtype = H ⊓ O := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [← h2, ← h3] at h1
    exact (isSylowOf_map_subtype_iff H).mp h1
  set e₀ : (↥H ⧸ CFSG.pPrimeCore 3 ↥H) ≃* M ⧸ O.subgroupOf M :=
    (QuotientGroup.quotientMulEquivOfEq hcoreH).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθs) with he₀
  have he₀mk : ∀ h : ↥H, e₀ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) h) = θ h := fun h => rfl
  set LH : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H) := L.map e₀.symm.toMonoidHom with hLH
  set eL : ↥L ≃* ↥LH := e₀.symm.subgroupMap L with heL
  have hLHs : IsSimpleGroup ↥LH := eL.symm.isSimpleGroup
  have hLHnab : ∃ a b : ↥LH, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLnab
    exact ⟨eL a, eL b, fun h => hab (eL.injective (by rw [map_mul, map_mul, h]))⟩
  have hLHn : LH.Normal := hLn.map e₀.symm.toMonoidHom e₀.symm.surjective
  have hLHc : centralizer (LH : Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have : e₀ c ∈ centralizer (L : Set (M ⧸ O.subgroupOf M)) := by
      rw [mem_centralizer_iff]
      intro l hl
      have h1 := mem_centralizer_iff.mp hc (e₀.symm l) ⟨l, hl, rfl⟩
      have h2 := congrArg e₀ h1
      simpa using h2
    rw [hLc, mem_bot] at this
    rw [mem_bot]
    exact e₀.injective (this.trans (map_one e₀).symm)
  have hLHz : center ↥LH = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥LH) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hLHnab
      exact hab ((mem_center_iff.mp (h ▸ mem_top b)) a)
  have hLHcomp : CFSG.IsComponent LH :=
    ⟨zja_isQuasisimple_of_simple hLHnab, Subgroup.Normal.isSubnormal hLHn⟩
  have hELc : 27 ∣ Nat.card ↥L := by
    rw [← hE27, ← card_img_of_inf hEM (GL83P3A6Syl.inf_eq_bot_of_pGroup
      (elementary_isPGroup 3 E hEel) hO3)]
    exact Subgroup.card_dvd_of_le hEL
  have hpL : 3 ∣ Nat.card ↥LH := by
    rw [← Nat.card_congr eL.toEquiv]
    exact dvd_trans ⟨9, by norm_num⟩ hELc
  obtain ⟨J, hJn, hJc, hJL, hJp, -, hJcore⟩ :=
    exists_pComponent_normal Nat.prime_three hLHcomp hLHn hLHz hpL
  have hJ0 : ¬ 3 ∣ Nat.card (⁅J, (CFSG.pPrimeCore 3 ↥J).map J.subtype⁆ : Subgroup ↥H) := by
    haveI : ((CFSG.pPrimeCore 3 ↥J).map J.subtype).Normal := by
      rw [hJcore]; infer_instance
    have hle : ⁅J, (CFSG.pPrimeCore 3 ↥J).map J.subtype⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype :=
      Subgroup.commutator_le_right _ _
    have hcop : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3 ↥J).map J.subtype)) := by
      rw [Subgroup.card_map_of_injective J.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) hcop)
  set V : Subgroup ↥H := Y.subgroupOf H with hV
  have hV2 : IsPGroup 2 V := hY2.comap_subtype
  have hcoreV : CFSG.pCore 2 ↥H ≤ V := by
    rw [hO2]
    exact Subgroup.comap_mono inf_le_left
  have hnc : ∀ Z : Subgroup ↥H, Z ≤ V → Z ≠ ⊥ → (Z.subgroupOf V).Characteristic →
      ¬ J ≤ normalizer (Z : Set ↥H) ⊔ CFSG.pPrimeCore 3 ↥H := by
    intro Z hZV hZ1 hZc hcover
    set ZG : Subgroup G := Z.map H.subtype with hZG
    have hZGY : ZG ≤ Y := by
      rintro _ ⟨z, hz, rfl⟩
      exact mem_subgroupOf.mp (hZV hz)
    have hZG1 : ZG ≠ ⊥ := fun h =>
      hZ1 ((Subgroup.map_eq_bot_iff_of_injective Z H.subtype_injective).mp h)
    have hZGc : (ZG.subgroupOf Y).Characteristic := by
      let e : ↥V ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hYH
      have hchar := zja_characteristic_map e hZc
      have heq : (Z.subgroupOf V).map e.toMonoidHom = ZG.subgroupOf Y := by
        ext y
        constructor
        · rintro ⟨s, hs, rfl⟩
          exact ⟨s, hs, rfl⟩
        · intro hy
          obtain ⟨z, hz, hzy⟩ := hy
          exact ⟨⟨z, hZV hz⟩, hz, Subtype.ext hzy⟩
      rw [← heq]
      exact hchar
    have hsmall := hbig ZG hZGY hZG1 hZGc
    have hEsup : E ≤ (normalizer (ZG : Set G) ⊓ M) ⊔ O := by
      intro q hq
      have hqM := hEM hq
      have hqL : π ⟨q, hqM⟩ ∈ L := hEL (mk_mem_img hq hqM)
      have hqLH : e₀.symm (π ⟨q, hqM⟩) ∈ LH := ⟨_, hqL, rfl⟩
      rw [← hJL] at hqLH
      obtain ⟨j, hjJ, hj⟩ := hqLH
      have hjc := hcover hjJ
      haveI : (CFSG.pPrimeCore 3 ↥H).Normal := CFSG.pPrimeCore_normal
      obtain ⟨n, hn, o, ho, rfl⟩ := mem_sup_of_normal_right.mp hjc
      have hθo : θ o = 1 := by
        have : o ∈ θ.ker := hcoreH ▸ ho
        exact this
      have hθq : θ n = π ⟨q, hqM⟩ := by
        have h1 := congrArg e₀ hj
        rw [he₀mk, MulEquiv.apply_symm_apply, map_mul, hθo, mul_one] at h1
        exact h1
      have hnN : (n : G) ∈ normalizer (ZG : Set G) := thg_mem_normalizer_map hn
      have hnM : (n : G) ∈ M := hHM n.2
      have hqO : (n : G)⁻¹ * q ∈ O := by
        have h2 : (QuotientGroup.mk ⟨(n : G), hnM⟩ : M ⧸ O.subgroupOf M) =
            QuotientGroup.mk ⟨q, hqM⟩ := hθq
        exact (mk_eq_iff hnM hqM).mp h2
      have e : q = (n : G) * ((n : G)⁻¹ * q) := by group
      rw [e]
      exact mul_mem_sup (mem_inf.mpr ⟨hnN, hnM⟩) hqO
    have h3 := l43_three_le_pRank_of_le_sup (inf_le_right.trans hMO) hO3 hEel hE27
      hEsup
    exact absurd h3 (not_le.mpr hsmall)
  rcases zj_apply_any Nat.prime_three (by norm_num) hZJ hsec hcharTwo hsylow hJn hJc hLHs
      hLHnab hLHn hLHc hJL hJp hV2 hcoreV hJ0 hnc with hc | ⟨n, ⟨f⟩⟩
  · exact Or.inl (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.isChevTwo_of_mulEquiv
      eL.symm hc)
  · exact Or.inr ⟨n, ⟨eL.trans f⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
