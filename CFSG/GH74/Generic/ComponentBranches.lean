module

public import CFSG.GH74.Generic.ClassicalCerts
public import CFSG.GH74.Generic.NativeCerts
public import CFSG.GH74.Generic.ExceptionalRank
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Generic.AltCerts
public import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup
  CFSG.GH74.Filter.ClassicalOdd

structure Setup {G : Type} [Group G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop where
  quasisimple : IsQuasisimple ↥K
  center_eq : center ↥K = pCore 2 ↥K
  not_c2 : ¬ InC2 ↥K
  not_t2 : ¬ InT2 ↥K

variable {G : Type} [Group G]

theorem Setup.of_inG2 {x : G} {K : Subgroup (CentralizerBar x)} (h : InG2 ↥K) : Setup x K :=
  ⟨h.1.1, h.1.2.1, h.2.1, h.2.2⟩

theorem Setup.isPGroup_center {x : G} {K : Subgroup (CentralizerBar x)} (h : Setup x K) :
    IsPGroup 2 ↥(center ↥K) := by
  have := pCore_isPGroup (p := 2) (G := ↥K)
  rw [← h.center_eq] at this
  exact this

theorem Setup.isSimple {x : G} {K : Subgroup (CentralizerBar x)} (h : Setup x K) :
    IsSimpleGroup (↥K ⧸ center ↥K) :=
  h.quasisimple.2.1

section SimpleInC2

variable [Finite G]

theorem shape_of_simpleInC2 (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K)
    (hS : SimpleInC2 (↥K ⧸ center ↥K)) : GenericShape x K := by
  have hex : ExcludedFromC2 ↥K := by
    by_contra hnex
    exact hset.not_c2 ⟨hset.quasisimple, hset.center_eq, hS, hnex⟩
  rcases hex with h | h | ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩ | h
  ·
    obtain ⟨F, _, _, hFM, e⟩ := h
    exact absurd ⟨hset.quasisimple, Or.inr (Or.inl ⟨F, inferInstance, inferInstance,
      isFM9_odd hFM, e⟩)⟩ hset.not_t2
  · exact absurd ⟨hset.quasisimple, Or.inr (Or.inr (Or.inr (Or.inl ⟨8, by norm_num, by norm_num, h⟩)))⟩
      hset.not_t2
  ·
    have hK : IsSL4Model ↥K := Or.inl ⟨F, inferInstance, inferInstance, by rw [hF], ⟨e⟩⟩
    exact Or.inl ⟨hK, xbar_mem_of_isSL4Model hgen hx hK⟩
  ·
    exfalso
    have hc : RankCertified (StatedSU 4 3 F) 4 :=
      rankCertified_SU4_quotient (q := 3) (by rw [hF]; norm_num) (by norm_num) (MonoidHom.id _)
        (fun g hg => by rw [MonoidHom.mem_ker] at hg; left; rw [show g = 1 from hg]; rfl)
    have hKc : RankCertified ↥K 4 := hc.of_mulEquiv e.symm
    exact (hKc.of_subgroup).not_gen4 (le_refl 4) (gen4_centralizerBar hgen x)
  ·
    have hF2 : ringChar F ≠ 2 :=
      ringChar_ne_two_of_card_eq (p := 3) (f := 1) Nat.prime_three (by norm_num) (by simpa using hF)
    obtain ⟨φ, hφ, -⟩ := exists_q8q8_Sp4 hF2
    refine Or.inr (Or.inl ⟨⟨F, inferInstance, inferInstance, ?_, ⟨e⟩⟩, ?_⟩)
    · rw [hF]; exact ⟨1, rfl⟩
    · exact xbar_mem_of_q8q8 hgen hx (e.symm.toMonoidHom.comp φ) (e.symm.injective.comp hφ)
  ·
    exact absurd ⟨hset.quasisimple, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩ hset.not_t2


theorem simpleInC2_of_psl3_three {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : LieModel S .PSL 3 3 1) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inl h))⟩

theorem simpleInC2_of_psl4_three {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : LieModel S .PSL 4 3 1) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩

theorem simpleInC2_of_psu4_three {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : LieModel S .PSU 4 3 1) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩

theorem simpleInC2_of_g2_three {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : LieModel S .G2 0 3 1) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩

theorem simpleInC2_of_psu3_three {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : LieModel S .PSU 3 3 1) : SimpleInC2 S :=
  ⟨hs, Or.inl (Or.inr (Or.inr h))⟩

theorem simpleInC2_of_fm9 {S : Type} [Group S] (hs : IsSimpleGroup S) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hfm : IsFM9 (p ^ f)) (h : LieModel S .PSL 2 p f) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inl ⟨p, f, hp, hf, hfm, h⟩)⟩

theorem simpleInC2_of_even {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : LieModel S .PSL 2 2 3 ∨ LieModel S .PSL 2 2 4 ∨ LieModel S .PSL 3 2 2 ∨
      LieModel S .PSU 3 2 2 ∨ LieModel S .twistedB2 0 2 3) : SimpleInC2 S := by
  refine ⟨hs, Or.inl (Or.inl ?_)⟩
  rcases h with h | h | h | h | h
  · exact ⟨.PSL, 2, 3, (stated_of_lieModel_PSL h).1, h⟩
  · exact ⟨.PSL, 2, 4, (stated_of_lieModel_PSL h).1, h⟩
  · exact ⟨.PSL, 3, 2, (stated_of_lieModel_PSL h).1, h⟩
  · exact ⟨.PSU, 3, 2, (stated_of_lieModel_PSU h).1, h⟩
  · exact ⟨.twistedB2, 0, 3, ⟨Nat.prime_two, by norm_num, rfl, rfl, ⟨1, rfl⟩, le_rfl⟩, h⟩

theorem simpleInC2_of_M11 {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : NativeSporadic.IsSporadic S .M11) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))⟩

theorem simpleInC2_of_M12 {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : NativeSporadic.IsSporadic S .M12) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))⟩

theorem simpleInC2_of_M22 {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : NativeSporadic.IsSporadic S .M22) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))⟩

theorem simpleInC2_of_M23 {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : NativeSporadic.IsSporadic S .M23) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))⟩

theorem simpleInC2_of_J2 {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : NativeSporadic.IsSporadic S .J2) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl h)))))))))))⟩

theorem simpleInC2_of_J3 {S : Type} [Group S] (hs : IsSimpleGroup S)
    (h : NativeSporadic.IsSporadic S .J3) : SimpleInC2 S :=
  ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl h))))))))))))⟩


theorem shape_of_alt (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {n : ℕ} (hn7 : 7 ≤ n) (hn11 : n ≤ 11)
    (e : ↥K ⧸ center ↥K ≃* alternatingGroup (Fin n)) : GenericShape x K := by
  exfalso
  have hZ := hF.alt_cover n hn7 hn11 ↥K hset.quasisimple hset.isPGroup_center ⟨e⟩
  by_cases hbot : center ↥K = ⊥
  · obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot e
    by_cases h7 : n = 7
    · subst h7
      exact hset.not_t2 ⟨hset.quasisimple, Or.inr (Or.inr (Or.inl ⟨eK⟩))⟩
    · have h8 : 8 ≤ n := by omega
      exact not_rankCertified_three_of_xbar_not_mem hgen hx
        (xbar_not_mem_of_center_eq_bot hx hbot) ((rankCertified_alternating h8).of_mulEquiv eK.symm)
  · have hcard : Nat.card (center ↥K) = 2 := by
      have := (Subgroup.one_lt_card_iff_ne_bot (center ↥K)).2 hbot
      omega
    exact hset.not_t2 ⟨hset.quasisimple, Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, hn7, hn11, hset.quasisimple, hcard, ⟨e⟩⟩)))⟩

theorem odd_prime_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Odd (p ^ f) :=
  (hp.odd_of_ne_two hp2).pow

theorem three_le_prime_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have h2 := hp.two_le
  have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  omega

theorem shape_of_psl2 (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel (↥K ⧸ center ↥K) .PSL 2 p f) : GenericShape x K := by
  obtain ⟨-, hf, -⟩ := lieModel_psl_data hmodel
  by_cases hfm : IsFM9 (p ^ f)
  · exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_fm9 hset.isSimple hp hf hfm hmodel)
  · exfalso
    rcases hF.psl2_cover p f hp hp2 ↥K hset.quasisimple hset.isPGroup_center hmodel with
      hbot | ⟨F, _, _, hFc, ⟨e⟩⟩
    · obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
      exact hset.not_t2 ⟨hset.quasisimple, Or.inl ⟨p, f, hp, hf, ⟨odd_prime_pow hp hp2, hfm⟩,
        lieModel_of_mulEquiv eK.symm hmodel⟩⟩
    · exact hset.not_t2 ⟨hset.quasisimple, Or.inr (Or.inl ⟨F, inferInstance, inferInstance,
        by rw [hFc]; exact odd_prime_pow hp hp2, ⟨e⟩⟩)⟩

theorem shape_of_psl3 (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel (↥K ⧸ center ↥K) .PSL 3 p f) : GenericShape x K := by
  obtain ⟨-, hf, -⟩ := lieModel_psl_data hmodel
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three hp hf hq3
    exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_psl3_three hset.isSimple hmodel)
  · have h5 : 5 ≤ p ^ f := by
      have h3 := three_le_prime_pow hp hp2 hf
      obtain ⟨k, hk⟩ := odd_prime_pow (f := f) hp hp2
      omega
    have hbot := hF.noTwoCover_psl3 p f hp hp2 _ hmodel ↥K hset.quasisimple hset.isPGroup_center
      ⟨MulEquiv.refl _⟩
    obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
    exact Or.inr (Or.inr (Or.inl ⟨⟨p, f, hp, hp2, h5, Or.inl (lieModel_of_mulEquiv eK.symm hmodel)⟩,
      xbar_not_mem_of_center_eq_bot hx hbot⟩))

theorem shape_of_psu3 (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel (↥K ⧸ center ↥K) .PSU 3 p f) : GenericShape x K := by
  obtain ⟨-, hf, -⟩ := lieModel_psu_data hmodel
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three hp hf hq3
    exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_psu3_three hset.isSimple hmodel)
  · have h5 : 5 ≤ p ^ f := by
      have h3 := three_le_prime_pow hp hp2 hf
      obtain ⟨k, hk⟩ := odd_prime_pow (f := f) hp hp2
      omega
    have hbot := hF.noTwoCover_psu3 p f hp hp2 _ hmodel ↥K hset.quasisimple hset.isPGroup_center
      ⟨MulEquiv.refl _⟩
    obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
    exact Or.inr (Or.inr (Or.inl ⟨⟨p, f, hp, hp2, h5, Or.inr (lieModel_of_mulEquiv eK.symm hmodel)⟩,
      xbar_not_mem_of_center_eq_bot hx hbot⟩))


theorem shape_of_psp4 (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel (↥K ⧸ center ↥K) .PSp 2 p f) : GenericShape x K := by
  obtain ⟨-, -, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psp_data hmodel
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq hp hp2 hFc
  rcases hF.psp4_cover p f hp hp2 ↥K hset.quasisimple hset.isPGroup_center hmodel with
    hbot | ⟨F', _, _, hFc', ⟨e⟩⟩
  · exfalso
    obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
    exact not_rankCertified_three_of_xbar_not_mem hgen hx (xbar_not_mem_of_center_eq_bot hx hbot)
      ((rankCertified_PSp4 hF2).of_mulEquiv (eK.trans eS).symm)
  · have hF2' : ringChar F' ≠ 2 := ringChar_ne_two_of_card_eq hp hp2 hFc'
    obtain ⟨φ, hφ, -⟩ := exists_q8q8_Sp4 hF2'
    refine Or.inr (Or.inl ⟨⟨F', inferInstance, inferInstance, ?_, ⟨e⟩⟩, ?_⟩)
    · rw [hFc']; exact odd_prime_pow hp hp2
    · exact xbar_mem_of_q8q8 hgen hx (e.symm.toMonoidHom.comp φ) (e.symm.injective.comp hφ)

theorem false_of_center_bot_of_rank (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hbot : center ↥K = ⊥) {S : Type} [Group S] [Finite S]
    (e : ↥K ⧸ center ↥K ≃* S) (hS : ¬ SectionalTwoRankLE S 3) : False := by
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot e
  exact not_rankCertified_three_of_xbar_not_mem hgen hx (xbar_not_mem_of_center_eq_bot hx hbot)
    ((rankCertified_of_not_sectionalTwoRankLE hS).of_mulEquiv eK.symm)

theorem false_of_center_bot_of_cert (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hbot : center ↥K = ⊥) {S : Type} [Group S]
    (e : ↥K ⧸ center ↥K ≃* S) (hS : RankCertified S 3) : False := by
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot e
  exact not_rankCertified_three_of_xbar_not_mem hgen hx (xbar_not_mem_of_center_eq_bot hx hbot)
    (hS.of_mulEquiv eK.symm)

theorem shape_of_g2
    (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel (↥K ⧸ center ↥K) .G2 0 p f) (hf : 1 ≤ f) : GenericShape x K := by
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three hp hf hq3
    exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_g2_three hset.isSimple hmodel)
  · exfalso
    have hbot := hF.noTwoCover_g2 p f hp hp2 _ hmodel ↥K hset.quasisimple hset.isPGroup_center
      ⟨MulEquiv.refl _⟩
    exact false_of_center_bot_of_cert hgen hx hbot (MulEquiv.refl _)
      (rankCertified_of_lieModel_G2 hp hp2 hmodel)

theorem shape_of_3D4 (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel (↥K ⧸ center ↥K) .trialityD4 0 p f) : GenericShape x K := by
  exfalso
  have hbot := hF.noTwoCover_3D4 p f hp hp2 _ hmodel ↥K hset.quasisimple hset.isPGroup_center
    ⟨MulEquiv.refl _⟩
  exact false_of_center_bot_of_rank hgen hx hbot (MulEquiv.refl _)
    (hF.rank_3D4 p f hp hp2 _ hmodel)

theorem shape_of_McL
    (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K)
    (hmodel : NativeSporadic.IsSporadic (↥K ⧸ center ↥K) .McL) : GenericShape x K := by
  exfalso
  have hbot := hF.noTwoCover_McL _ hmodel ↥K hset.quasisimple hset.isPGroup_center
    (Gen4.subgroup K (gen4_centralizerBar hgen x)) ⟨MulEquiv.refl _⟩
  exact false_of_center_bot_of_cert hgen hx hbot (MulEquiv.refl _)
    (rankCertified_of_isSporadic_McL hmodel)

theorem shape_of_Ly
    (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K)
    (hmodel : NativeSporadic.IsSporadic (↥K ⧸ center ↥K) .Ly) : GenericShape x K := by
  exfalso
  have hbot := hF.noTwoCover_Ly _ hmodel ↥K hset.quasisimple hset.isPGroup_center
    (Gen4.subgroup K (gen4_centralizerBar hgen x)) ⟨MulEquiv.refl _⟩
  exact false_of_center_bot_of_cert hgen hx hbot (MulEquiv.refl _)
    (rankCertified_of_isSporadic_Ly hmodel)

theorem shape_of_psl4 (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel (↥K ⧸ center ↥K) .PSL 4 p f) : GenericShape x K := by
  obtain ⟨-, hf, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psl_data hmodel
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three hp hf hq3
    exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_psl4_three hset.isSimple hmodel)
  · have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq hp hp2 hFc
    by_cases hbot : center ↥K = ⊥
    · exfalso
      obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
      exact not_rankCertified_three_of_xbar_not_mem hgen hx (xbar_not_mem_of_center_eq_bot hx hbot)
        ((rankCertified_PSL4 hF2).of_mulEquiv (eK.trans eS).symm)
    · have hodd : Odd (Nat.card F) := by rw [hFc]; exact odd_prime_pow hp hp2
      obtain ⟨π, hπ, hcompat⟩ := hF.psl4_cover ↥K hset.quasisimple hset.isPGroup_center F hodd eS
      rcases cover_branch_SL4 hF2 eS π hπ hcompat hbot with ⟨hmod, ⟨e⟩⟩ | ⟨-, hc⟩
      · have hK : IsSL4Model ↥K := Or.inl ⟨F, inferInstance, inferInstance, hmod, ⟨e⟩⟩
        exact Or.inl ⟨hK, xbar_mem_of_isSL4Model hgen hx hK⟩
      · exact absurd (gen4_centralizerBar hgen x) (hc.of_subgroup.not_gen4 (le_refl 4))

theorem shape_of_psu4 (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel (↥K ⧸ center ↥K) .PSU 4 p f) : GenericShape x K := by
  obtain ⟨-, hf, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psu_data hmodel
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three hp hf hq3
    exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_psu4_three hset.isSimple hmodel)
  · have hqodd : Odd (p ^ f) := odd_prime_pow hp hp2
    by_cases hbot : center ↥K = ⊥
    · exfalso
      obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
      exact not_rankCertified_three_of_xbar_not_mem hgen hx (xbar_not_mem_of_center_eq_bot hx hbot)
        ((rankCertified_PSU4 hFc (Nat.odd_iff.1 hqodd)).of_mulEquiv (eK.trans eS).symm)
    · obtain ⟨π, hπ, hcompat⟩ := hF.psu4_cover ↥K hset.quasisimple hset.isPGroup_center F (p ^ f)
        hFc hqodd eS
      rcases cover_branch_SU4 hFc (Nat.odd_iff.1 hqodd) eS π hπ hcompat hbot with
        ⟨hmod, ⟨e⟩⟩ | ⟨-, hc⟩
      · have hK : IsSL4Model ↥K := Or.inr ⟨p ^ f, F, inferInstance, inferInstance, hFc, hmod, ⟨e⟩⟩
        exact Or.inl ⟨hK, xbar_mem_of_isSL4Model hgen hx hK⟩
      · exact absurd (gen4_centralizerBar hgen x) (hc.of_subgroup.not_gen4 (le_refl 4))

theorem prime_ne_two_of_pow_mod_four {p f : ℕ} (hf : 1 ≤ f) {r : ℕ} (hr : r = 1 ∨ r = 3)
    (h : p ^ f % 4 = r) : p ≠ 2 := by
  rintro rfl
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  rw [pow_succ] at h
  omega

theorem shape_of_psl5 (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime)
    (hq : p ^ f % 4 = 3) (hmodel : LieModel (↥K ⧸ center ↥K) .PSL 5 p f) : GenericShape x K := by
  exfalso
  obtain ⟨-, hf, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psl_data hmodel
  have hp2 : p ≠ 2 := prime_ne_two_of_pow_mod_four hf (Or.inr rfl) hq
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq hp hp2 hFc
  have hbot := hF.noTwoCover_psl5 p f hp hq _ hmodel ↥K hset.quasisimple hset.isPGroup_center
    ⟨MulEquiv.refl _⟩
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
  exact not_rankCertified_three_of_xbar_not_mem hgen hx (xbar_not_mem_of_center_eq_bot hx hbot)
    ((rankCertified_PSL5 hF2).of_mulEquiv (eK.trans eS).symm)

theorem shape_of_psu5 (hF : GenericKnownFacts) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {p f : ℕ} (hp : p.Prime)
    (hq : p ^ f % 4 = 1) (hmodel : LieModel (↥K ⧸ center ↥K) .PSU 5 p f) : GenericShape x K := by
  exfalso
  obtain ⟨-, hf, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psu_data hmodel
  have hp2 : p ≠ 2 := prime_ne_two_of_pow_mod_four hf (Or.inl rfl) hq
  have hqodd : p ^ f % 2 = 1 := Nat.odd_iff.1 (odd_prime_pow hp hp2)
  have hbot := hF.noTwoCover_psu5 p f hp hq _ hmodel ↥K hset.quasisimple hset.isPGroup_center
    ⟨MulEquiv.refl _⟩
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
  exact not_rankCertified_three_of_xbar_not_mem hgen hx (xbar_not_mem_of_center_eq_bot hx hbot)
    ((rankCertified_PSU5 hFc hqodd).of_mulEquiv (eK.trans eS).symm)

theorem shape_of_ree (hF : GenericKnownFacts) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K) {f : ℕ}
    (hmodel : LieModel (↥K ⧸ center ↥K) .twistedG2 0 3 f) : GenericShape x K := by
  have hbot := hF.noTwoCover_ree f _ hmodel ↥K hset.quasisimple hset.isPGroup_center
    ⟨MulEquiv.refl _⟩
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨f, lieModel_of_mulEquiv eK.symm hmodel⟩,
    xbar_not_mem_of_center_eq_bot hx hbot⟩)))

theorem shape_of_J1 (hF : GenericKnownFacts) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hset : Setup x K)
    (hmodel : NativeSporadic.IsSporadic (↥K ⧸ center ↥K) .J1) : GenericShape x K := by
  have hbot := hF.noTwoCover_J1 _ hmodel ↥K hset.quasisimple hset.isPGroup_center
    ⟨MulEquiv.refl _⟩
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_center_eq_bot hbot (MulEquiv.refl _)
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨isSporadic_of_mulEquiv eK.symm hmodel,
    xbar_not_mem_of_center_eq_bot hx hbot⟩)))

end SimpleInC2

end CFSG.GH74.Generic
