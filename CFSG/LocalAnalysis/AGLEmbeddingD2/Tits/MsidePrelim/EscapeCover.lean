module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.L34Generation
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaCoreFree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NormalizerTransitive

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3)
open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem card_le_card_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup X} (hQ : IsPGroup p Q) (S : Sylow p X) :
    Nat.card Q ≤ Nat.card (S : Subgroup X) := by
  obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
  have h1 : Nat.card Q ≤ Nat.card (S' : Subgroup X) := Subgroup.card_le_of_le hS'
  rw [Sylow.card_eq_multiplicity S', ← Sylow.card_eq_multiplicity S] at h1
  exact h1

theorem normalizer_map_le_map_normalizer {H M T : Subgroup G} (hWM : GLBPrimeCore 3 H ≤ M)
    (hT : IsSylowTwoOf T (H ⊓ M)) :
    Subgroup.normalizer (((T.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3)) : Subgroup _) : Set _) ≤
      ((H ⊓ Subgroup.normalizer (T : Set G)).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set W := GLBPrimeCore 3 H with hWdef
  have hTH : T ≤ H := hT.1.trans inf_le_left
  have hWH : W ≤ H := glbPrimeCore_le 3 H
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := le_normalizer_glbPrimeCore 3 H
  have hLHM : T ⊔ W ≤ H ⊓ M := sup_le hT.1 (le_inf hWH hWM)
  intro xbar hxbar
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := H) 3) xbar
  have hconj : ∀ t ∈ T, (x : G) * t * (x : G)⁻¹ ∈ T ⊔ W := by
    intro t ht
    have hmem : π x * π ⟨t, hTH ht⟩ * (π x)⁻¹ ∈ (T.subgroupOf H).map π :=
      (Subgroup.mem_normalizer_iff.mp hxbar _).mp ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    obtain ⟨⟨t', ht'H⟩, ht', he⟩ := hmem
    have ht'T : t' ∈ T := Subgroup.mem_subgroupOf.mp ht'
    have h1 : π ((⟨t', ht'H⟩ : H)⁻¹ * (x * ⟨t, hTH ht⟩ * x⁻¹)) = 1 := by
      rw [map_mul, map_inv, he, map_mul, map_mul, map_inv, inv_mul_cancel]
    have hw := (mk'_primeComplementCore_eq_one_iff 3 _).mp h1
    have e : (x : G) * t * (x : G)⁻¹ = t' * (t'⁻¹ * ((x : G) * t * (x : G)⁻¹)) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ht'T) (Subgroup.mem_sup_right ?_)
    simpa using hw
  obtain ⟨n, hn⟩ := hT.2.1.exists_card_eq
  have hTL : T ≤ T ⊔ W := le_sup_left
  have hidxL : ¬ 2 ∣ T.relIndex (T ⊔ W) := by
    intro h
    apply hT.2.2
    have := Subgroup.relIndex_mul_relIndex T (T ⊔ W) (H ⊓ M) hTL hLHM
    exact h.trans ⟨_, this.symm⟩
  have hLc : Nat.card (T ⊔ W : Subgroup G) = 2 ^ n * T.relIndex (T ⊔ W) := by
    have h := Subgroup.relIndex_mul_card T (T ⊔ W)
    rw [inf_of_le_left hTL, hn] at h
    rw [← h]
    ring
  have hTxL : T.map (MulAut.conj (x : G)).toMonoidHom ≤ T ⊔ W := by
    rintro _ ⟨t, ht, rfl⟩
    exact hconj t ht
  obtain ⟨y, hyL, hy⟩ := exists_conj_map_eq_of_card (p := 2) hTL hTxL hn
    (by rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hn]) hLc hidxL
  have hyH : y ∈ H := (hLHM hyL).1
  have hnorm : y⁻¹ * (x : G) ∈ Subgroup.normalizer (T : Set G) := by
    apply mem_normalizer_of_map_conj_eq_self
    rw [map_conj_mul', ← hy, ← map_conj_mul', inv_mul_cancel]
    ext z
    simp
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right T W (hTH.trans hHW),
    Set.mem_mul] at hyL
  obtain ⟨t₀, ht₀, w₀, hw₀, rfl⟩ := hyL
  have hxe : x = (⟨t₀, hTH ht₀⟩ : H) * ⟨w₀, hWH hw₀⟩ *
      ⟨(t₀ * w₀)⁻¹ * (x : G), H.mul_mem (H.inv_mem hyH) x.2⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group
  have hw₀1 : π ⟨w₀, hWH hw₀⟩ = 1 := (mk'_primeComplementCore_eq_one_iff 3 _).mpr hw₀
  refine ⟨⟨t₀, hTH ht₀⟩ * ⟨(t₀ * w₀)⁻¹ * (x : G), H.mul_mem (H.inv_mem hyH) x.2⟩, ?_, ?_⟩
  · show _ ∈ (H ⊓ Subgroup.normalizer (T : Set G)).subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    refine ⟨H.mul_mem (hTH ht₀) (H.mul_mem (H.inv_mem hyH) x.2), ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ht₀) hnorm
  · rw [map_mul]
    conv_rhs => rw [hxe]
    rw [map_mul, map_mul, hw₀1, mul_one]

theorem isSylowTwoOf_map_range {X D : Type*} [Group X] [Group D] [Finite X] {H T : Subgroup X}
    (α : ↥H →* D) (hT : IsSylowTwoOf T H) : IsSylowTwoOf ((T.subgroupOf H).map α) α.range := by
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · have h2 : IsPGroup 2 (T.subgroupOf H) := by
      have : IsPGroup 2 ↥T := hT.2.1
      exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    exact h2.of_surjective (α.subgroupMap _) (α.subgroupMap_surjective _)
  · have heq : ((T.subgroupOf H).map α).subgroupOf α.range =
        (T.subgroupOf H).map α.rangeRestrict := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, Subtype.ext hty⟩
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, congrArg Subtype.val hty⟩
    rw [heq]
    intro hdvd
    exact hT.2.2 (hdvd.trans (Subgroup.index_map_dvd _ α.rangeRestrict_surjective))

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.isSylowTwoOf_map
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    IsSylowTwoOf ((T.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (Subgroup.normalizer (((A.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3)) : Subgroup _) : Set _)) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hX₀N : ((H ⊓ M).subgroupOf H).map π =
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) :=
    hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  set α : ↥(H ⊓ M) →* (H ⧸ primeComplementCore (G := H) 3) :=
    π.comp (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H)) with hα
  have hαr : α.range = ((H ⊓ M).subgroupOf H).map π := by
    ext z
    simp only [MonoidHom.mem_range, Subgroup.mem_map, hα, MonoidHom.comp_apply]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨Subgroup.inclusion inf_le_left u, Subgroup.mem_subgroupOf.mpr u.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hαT : (T.subgroupOf (H ⊓ M)).map α = (T.subgroupOf H).map π := by
    ext z
    simp only [Subgroup.mem_map, hα, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨Subgroup.inclusion inf_le_left u, hu, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hT.1 hh⟩, hh, rfl⟩
  have h := isSylowTwoOf_map_range α hT
  rw [hαT, hαr, hX₀N] at h
  exact h

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.map_eq_of_card_nine_of_nine
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    {B : Subgroup G} (hBHM : B ≤ H ⊓ M) (hBp : IsPGroup 3 B) (hB9 : Nat.card B = 9) :
    (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hX₀N : ((H ⊓ M).subgroupOf H).map π =
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) :=
    hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hAR : A = R := Subgroup.eq_of_le_of_card_ge hc.esc.A_le
    (by rw [hR9, hc.esc.card_A]; norm_num)
  have hAbar9 : Nat.card ((A.subgroupOf H).map π) = 9 := by
    have := hc.almostSimple.card_A
    rw [this]
    norm_num
  have hRbar9 : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) = 9 := by
    rw [hc.rbar, ← hAR]
    exact hAbar9
  have hBH : B ≤ H := hBHM.trans inf_le_left
  have hBbar9 : Nat.card ((B.subgroupOf H).map π) = 9 := by
    have hBp' : IsPGroup 3 (B.subgroupOf H) := hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBH).symm
    rw [card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hBp',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv, hB9]
  have hBbarN : (B.subgroupOf H).map π ≤
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) := by
    rw [← hX₀N]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hBHM (Subgroup.mem_subgroupOf.mp hx)))
  have hBbarp : IsPGroup 3 ((B.subgroupOf H).map π) :=
    IsPGroup.of_card (n := 2) (by rw [hBbar9]; norm_num)
  have hAbarp : IsPGroup 3 ((A.subgroupOf H).map π) :=
    IsPGroup.of_card (n := 2) (by rw [hAbar9]; norm_num)
  have hsupp := IsPGroup.to_sup_of_normal_right' hBbarp hAbarp hBbarN
  have hsup9 := card_le_card_sylow hsupp Rbar
  rw [hRbar9] at hsup9
  have h1 : (B.subgroupOf H).map π = (B.subgroupOf H).map π ⊔ (A.subgroupOf H).map π :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hBbar9]; exact hsup9)
  have h2 : (A.subgroupOf H).map π = (B.subgroupOf H).map π ⊔ (A.subgroupOf H).map π :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hAbar9]; exact hsup9)
  rw [h1, ← h2]

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.cover_of_isSylowTwoOf_of_nine
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    {T B Y : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) (hBHM : B ≤ H ⊓ M) (hBp : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) (hTY : T ≤ Y) (hBY : B ≤ Y)
    (hNTY : H ⊓ Subgroup.normalizer (T : Set G) ≤ Y) :
    ∀ k ∈ K, ∃ a ∈ Y, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hTbar := D2L34BetaConf3.isSylowTwoOf_map hc hT
  have hBA := D2L34BetaConf3.map_eq_of_card_nine_of_nine hc hR9 hBHM hBp hB9
  have hAbar9 : Nat.card ((A.subgroupOf H).map π) = 9 := by
    have := hc.almostSimple.card_A
    rw [this]
    norm_num
  have hNY : Subgroup.normalizer (((T.subgroupOf H).map π : Subgroup _) : Set _) ≤
      (Y.subgroupOf H).map π :=
    (normalizer_map_le_map_normalizer hc.esc.primeCore_le hT).trans
      (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
        (hNTY (Subgroup.mem_subgroupOf.mp hx))))
  have hKY := le_of_normalizer_sylowTwo_le hc.l34 hc.almostSimple.normal
    hc.almostSimple.centralizer_eq_bot hc.iso hc.le_K hc.almostSimple.elem hAbar9 hTbar
    (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hTY (Subgroup.mem_subgroupOf.mp hx))))
    (hBA ▸ Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hBY (Subgroup.mem_subgroupOf.mp hx))))
    hNY
  intro k hk
  obtain ⟨y, hy, rfl⟩ := hKY hk
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, y.2, rfl⟩

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.cover_of_isSylowTwoOf
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    {T B Y : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) (hBHM : B ≤ H ⊓ M) (hBp : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) (hTY : T ≤ Y) (hBY : B ≤ Y)
    (hNTY : H ⊓ Subgroup.normalizer (T : Set G) ≤ Y) :
    ∀ k ∈ K, ∃ a ∈ Y, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  D2L34BetaConf3.cover_of_isSylowTwoOf_of_nine hc (hc.card_R_eq_nine hstr) hT hBHM hBp hB9 hTY hBY
    hNTY

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
