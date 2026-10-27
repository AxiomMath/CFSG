module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.CharSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUp

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3 D2Amb3)

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.isSylowTwoOf_top_of_isSylowTwoOf
    [D2Amb3 G]
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {U : Subgroup G} (hU : IsSylowTwoOf U H) :
    IsSylowTwoOf U ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hCU, hC1, hchar, hcov⟩ := D2L34BetaConf3.exists_char_cover_of_isSylowTwoOf hFF hc hstr
    (D₀ := H) le_rfl (glbPrimeCore_le 3 H) hU
  have hNU : Subgroup.normalizer (U : Set G) ≤ H :=
    D2L34BetaConf3.normalizer_le_of_char_cover' hc hstr hOnly hU.2.1 hCU hC1 hchar hcov
  obtain ⟨S, hUS, hS⟩ := exists_isSylowTwoOf_of_le (le_top : U ≤ ⊤) hU.2.1
  have hSU : S ≤ U := by
    refine CFSG.AGLEmbeddingD2.le_of_normalizer_inf_le hS.2.1 ?_
    rw [inf_of_le_right hUS]
    have hle : S ⊓ Subgroup.normalizer (U : Set G) ≤ H :=
      inf_le_right.trans hNU
    exact (hU.eq_of_le (le_inf hUS Subgroup.le_normalizer) hle (hS.2.1.to_le inf_le_left)).le
  rwa [le_antisymm hSU hUS] at hS

theorem D2L34BetaConf.isSylowTwoOf_top_of_isSylowTwoOf
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {U : Subgroup G} (hU : IsSylowTwoOf U H) :
    IsSylowTwoOf U ⊤ := by
  have := hc.amb3
  exact D2L34BetaConf3.isSylowTwoOf_top_of_isSylowTwoOf hFF hc.toConf3 hstr hOnly hU

theorem card_eq_card_map_mul_card_inf_ker {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (Y : Subgroup A) : Nat.card Y = Nat.card (Y.map f) * Nat.card (Y ⊓ f.ker : Subgroup A) := by
  have h := Subgroup.card_ker_mul_card_range (f.domRestrict Y)
  have h1 : (f.domRestrict Y).ker = f.ker.subgroupOf Y := by
    ext x; simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h2 : (f.domRestrict Y).range = Y.map f := by
    ext x; simp [Subgroup.mem_map]
  have h3 : Nat.card (f.ker.subgroupOf Y) = Nat.card (Y ⊓ f.ker : Subgroup A) := by
    rw [← Subgroup.card_map_of_injective Y.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [h1, h2, h3] at h
  rw [← h, mul_comm]

theorem card_sylow_eq_eight_mul_of_l34
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {X : Type} [Group X] [Finite X] {K A T S : Subgroup X} (hKn : K.Normal)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hAK : A ≤ K) (hA9 : Nat.card A = 9)
    (hT : IsSylowTwoOf T (Subgroup.normalizer (A : Set X))) (hS : IsSylowTwoOf S ⊤) :
    Nat.card S = 8 * Nat.card T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : IsLinThreeFour ↥K := isLinThreeFour_of_l34Index hd he
  have hK20 : Nat.card K = 20160 := (kFactSmallThreeOrders ↥K).2.1 hL
  obtain ⟨NA, hNAdef⟩ : ∃ NA : Subgroup X, NA = Subgroup.normalizer (A : Set X) := ⟨_, rfl⟩
  rw [← hNAdef] at hT
  have hKN : ∀ x : X, x ∈ Subgroup.normalizer (K : Set X) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hKn.conj_mem k hk x, fun hk => by simpa [mul_assoc] using hKn.conj_mem _ hk x⁻¹⟩
  obtain ⟨-, hNK, -⟩ := normalizer_inf_eq_sup_of_l34 hd hKn he hAK hA9 (hNAdef ▸ hT)
  rw [← hNAdef] at hNK
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup ↥K, P = A.subgroupOf K := ⟨_, rfl⟩
  have hPc : Nat.card P = 9 := by
    rw [hPdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA9]
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hPc]; norm_num)
  have hPidx : ¬ 3 ∣ P.index := by
    have h := P.index_mul_card
    rw [hPc, hK20] at h
    have : P.index = 2240 := by omega
    rw [this]
    norm_num
  have hPS : ((hPp.toSylow hPidx : Sylow 3 ↥K) : Subgroup ↥K) = P := IsPGroup.toSylow_coe _ _
  have hfr : NA ⊔ K = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (N := K) (hPp.toSylow hPidx)
    have hmap : ((hPp.toSylow hPidx : Sylow 3 ↥K) : Subgroup ↥K).map K.subtype = A := by
      rw [hPS, hPdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK]
    rw [hmap, ← hNAdef] at h
    exact h
  have hc2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := K) (B := NA) (fun x _ => hKN x)
  rw [sup_comm, hfr, Subgroup.card_top, inf_comm, hNK, hK20] at hc2
  have hX : Nat.card X = 280 * Nat.card NA := by
    have hpos : 0 < Nat.card NA := Nat.card_pos
    have h' : Nat.card X * 72 = 280 * Nat.card NA * 72 := by
      rw [hc2]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 72) h'
  have hSc := (isSylowTwoOf_iff.mp hS).2.2
  have hTc := (isSylowTwoOf_iff.mp hT).2.2
  unfold twoPart at hSc hTc
  rw [Subgroup.card_top, hX] at hSc
  rw [hSc, hTc, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
    pow_add]
  have h280 : (280 : ℕ).factorization 2 = 3 := by
    have h : (280:ℕ) = 2^3 * 35 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [h280]
  ring

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.card_eq_eight_mul
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T U : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M))
    (hU : IsSylowTwoOf U H) : Nat.card U = 8 * Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := primeComplementCore (G := H) 3 with hW
  set π := QuotientGroup.mk' W with hπ
  set W₀ : Subgroup G := W.map H.subtype with hW₀
  have hW₀e : W₀ = GLBPrimeCore 3 H := by
    rw [glbPrimeCore_eq_primeComplementCoreOf]
    rfl
  have hW₀HM : W₀ ≤ H ⊓ M := hW₀e ▸ le_inf (glbPrimeCore_le 3 H) hc.esc.primeCore_le
  have hHW₀ : H ≤ Subgroup.normalizer (W₀ : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype H W
  have hUW : IsSylowTwoOf (U ⊓ W₀) W₀ :=
    A4.isSylowTwoOf_inf_normal hU (hW₀HM.trans inf_le_left) hHW₀
  have hTW : IsSylowTwoOf (T ⊓ W₀) W₀ :=
    A4.isSylowTwoOf_inf_normal hT hW₀HM (inf_le_left.trans hHW₀)
  have hs : Nat.card (U ⊓ W₀ : Subgroup G) = Nat.card (T ⊓ W₀ : Subgroup G) :=
    card_eq_of_isSylowTwoOf hUW hTW
  have hcard : ∀ Y : Subgroup G, Y ≤ H →
      Nat.card Y = Nat.card ((Y.subgroupOf H).map π) * Nat.card (Y ⊓ W₀ : Subgroup G) := by
    intro Y hYH
    have h1 := card_eq_card_map_mul_card_inf_ker π (Y.subgroupOf H)
    rw [hπ, QuotientGroup.ker_mk'] at h1
    have h2 : Nat.card ↥(Y.subgroupOf H ⊓ W) = Nat.card (Y ⊓ W₀ : Subgroup G) := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective,
        Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hYH]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv.symm, h1, h2]
  have hAbar9 : Nat.card ((A.subgroupOf H).map π) = 9 := by
    have := hc.almostSimple.card_A
    rw [this]
    norm_num
  have hTbar := D2L34BetaConf3.isSylowTwoOf_map hc hT
  have hUbar : IsSylowTwoOf ((U.subgroupOf H).map π) ⊤ := by
    have h := isSylowTwoOf_map_range π hU
    rwa [MonoidHom.range_eq_top_of_surjective π (QuotientGroup.mk'_surjective _)] at h
  have h8 := card_sylow_eq_eight_mul_of_l34 hc.l34 hc.almostSimple.normal hc.iso hc.le_K hAbar9
    hTbar hUbar
  rw [hcard U hU.1, hcard T (hT.1.trans inf_le_left), h8, hs]
  ring

theorem D2L34BetaConf.card_eq_eight_mul
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) {T U : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M))
    (hU : IsSylowTwoOf U H) : Nat.card U = 8 * Nat.card T :=
  D2L34BetaConf3.card_eq_eight_mul hc.toConf3 hT hU

theorem D2L34BetaConf.isSylowTwoOf_top_and_card
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {T U : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M))
    (hU : IsSylowTwoOf U H) (_hTU : T ≤ U) :
    IsSylowTwoOf U ⊤ ∧ Nat.card U = 8 * Nat.card T :=
  ⟨D2L34BetaConf.isSylowTwoOf_top_of_isSylowTwoOf hFF hc hstr hOnly hU,
    D2L34BetaConf.card_eq_eight_mul hc hT hU⟩

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
