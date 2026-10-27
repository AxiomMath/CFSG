
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourBlocks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin

@[expose] def HasChi0Block {G : Type*} [Group G] (K : Subgroup G) : Prop :=
  ∃ B : Subgroup G, IsChi0Block K B

section Sup

variable {G : Type*} [Group G]

theorem exists_pow_mem_of_mem_sup {K S : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) {c : G} (hc : c ∈ K ⊔ S) :
    ∃ n : ℕ, c ^ 2 ^ n ∈ K := by
  have h : c ∈ (↑(K ⊔ S) : Set G) := hc
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K S hSK] at h
  obtain ⟨k, hk, s, hs, rfl⟩ := h
  obtain ⟨n, hn⟩ := hS ⟨s, hs⟩
  have hsn : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have key : ∀ m : ℕ, ∃ k' ∈ K, (k * s) ^ m = k' * s ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨k', hk', h'⟩ := ih
      refine ⟨k' * (s ^ m * k * (s ^ m)⁻¹), ?_, ?_⟩
      · refine K.mul_mem hk' ?_
        have : s ^ m ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ (hSK hs) m
        exact (Subgroup.mem_normalizer_iff.mp this k).mp hk
      · rw [pow_succ, h', pow_succ]
        group
  obtain ⟨k', hk', h'⟩ := key (2 ^ n)
  exact ⟨n, by rw [h', hsn, mul_one]; exact hk'⟩

theorem le_of_isShort2_of_le_sup {K S B : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hB : IsShort2 B) (hBX : B ≤ K ⊔ S) : B ≤ K := by
  have hXN : K ⊔ S ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hSK
  have hnorm : (K.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
    intro b hb
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hXN (hBX hb), Subgroup.le_normalizer hb⟩
  have hp : IsPGroup 2 (↥B ⧸ K.subgroupOf B) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨n, hn⟩ := exists_pow_mem_of_mem_sup hS hSK (hBX b.2)
      refine ⟨n, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hn
  exact Subgroup.subgroupOf_eq_top.mp (hB.1 (K.subgroupOf B) hp)

theorem isSubnormal_subgroupOf_of_le {X K B : Subgroup G} (hBK : B ≤ K) (hKX : K ≤ X)
    (h : (B.subgroupOf X).IsSubnormal) : (B.subgroupOf K).IsSubnormal := by
  have h1 : IsSubnormal (B.subgroupOf X) ⊤ := A3.subnormal_top_iff.mpr h
  have h2 := A3.subnormal_map X.subtype h1
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
    inf_eq_left.mpr (hBK.trans hKX)] at h2
  have h3 := A4.subnormal_of_le_of_le h2 hBK hKX
  have h4 := A3.subnormal_comap K.subtype h3
  rw [show K.comap K.subtype = ⊤ from Subgroup.subgroupOf_self K] at h4
  exact A3.subnormal_top_iff.mp h4

theorem isChi0Block_of_isChi0Block_sup {K S B : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hB : IsChi0Block (K ⊔ S) B) :
    IsChi0Block K B := by
  obtain ⟨⟨hsh, hBX, hsub⟩, htype⟩ := hB
  have hBK : B ≤ K := le_of_isShort2_of_le_sup hS hSK hsh hBX
  exact ⟨⟨hsh, hBK, isSubnormal_subgroupOf_of_le hBK le_sup_left hsub⟩, htype⟩

theorem charTwo_sup_of_le_normalizer {K S : Subgroup G} (hK : CharTwo K) (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) : CharTwo (K ⊔ S) := by
  have hXK : K ⊔ S ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hSK
  have hKQ : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ S) :=
    le_pCoreOf_of_le_normalizer ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K).trans
      le_sup_left)
      (hXK.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 K))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K)
  have hCp : IsPGroup 2
      (((K ⊔ S) ⊓ Subgroup.centralizer (pCoreOf 2 (K ⊔ S) : Set G) : Subgroup G)) := by
    rintro ⟨c, hcX, hcC⟩
    obtain ⟨n, hn⟩ := exists_pow_mem_of_mem_sup hS hSK hcX
    have hnC : c ^ 2 ^ n ∈ Subgroup.centralizer (pCoreOf 2 (K ⊔ S) : Set G) :=
      Subgroup.pow_mem _ hcC _
    have hnC' : c ^ 2 ^ n ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast hKQ) hnC
    have hnQ : c ^ 2 ^ n ∈ pCoreOf 2 K := hK ⟨hn, hnC'⟩
    obtain ⟨m, hm⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K ⟨_, hnQ⟩
    refine ⟨n + m, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hm
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hXQ : K ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (K ⊔ S)
  have hXC : K ⊔ S ≤ Subgroup.normalizer
      (((K ⊔ S) ⊓ Subgroup.centralizer (pCoreOf 2 (K ⊔ S) : Set G) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
      Subgroup.le_normalizer
      (hXQ.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer _))
  exact le_pCoreOf_of_normalizes inf_le_left hXC hCp

end Sup

section Dichotomy

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsGamma0.exists_of_charTwo_not_le (h : UniqueSetting G T M) {H S X : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hSX : S ≤ X) (hX : CharTwo X)
    (hXM : ¬ X ≤ M) : IsGamma0 M X ∧ IsSylowTwoOf S X ∧ IsSylowTwoOf S (X ⊓ M) := by
  obtain ⟨hSH, hSc, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  have hcoreX : pCoreOf 2 X ≠ ⊥ := by
    intro hbot
    have hXbot : X ≤ ⊥ := by
      intro x hx
      have hx' : x ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
        refine ⟨hx, ?_⟩
        rw [hbot]
        simp [Subgroup.mem_centralizer_iff]
      have := hX hx'
      rwa [hbot] at this
    exact hSc.2.1 (le_bot_iff.mp (hSX.trans hXbot))
  have hpair : IsWitnessPair M S X := ⟨hSc, hSX, hcoreX, hX, hXM⟩
  have hXΓ : IsGamma M X := hpair.isGamma_of_le le_rfl hcoreX
  have hH0 := hH
  rcases hH with hU | h2
  · have hXtop : IsGammaTop M X :=
      hpair.isGammaTop_of_le le_rfl hcoreX (fun V hV => hU.1.card_le_of_isSylowTwoOf hSH hV)
    obtain ⟨hX0, hSX', hSXM, -, -⟩ := IsGamma0.overgroup_of_sylow_le h hH0 hS hXΓ hSX
      (Or.inr ⟨hU, hXtop⟩)
    exact ⟨hX0, hSX', hSXM⟩
  · obtain ⟨hX0, hSX', hSXM, -, -⟩ := IsGamma0.overgroup_of_sylow_le h hH0 hS hXΓ hSX (Or.inl h2)
    exact ⟨hX0, hSX', hSXM⟩

theorem charTwo_le_or_hasChi0Block (h238 : Lemma2_3_8_4) (h : UniqueSetting G T M)
    {H S K : Subgroup G} (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M))
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hK : CharTwo K) : K ≤ M ∨ HasChi0Block K := by
  by_cases hXM : K ⊔ S ≤ M
  · exact Or.inl (le_sup_left.trans hXM)
  · right
    have hS2 : IsPGroup 2 S := hS.isPGroup
    have hX : CharTwo (K ⊔ S) := charTwo_sup_of_le_normalizer hK hS2 hSK
    obtain ⟨hX0, -, hSXM⟩ := IsGamma0.exists_of_charTwo_not_le h hH hS le_sup_right hX hXM
    obtain ⟨-, s, L, hs1, -, hL, -⟩ := h238 G T M (K ⊔ S) S h hX0 hX hSXM
    exact ⟨L ⟨0, hs1⟩, isChi0Block_of_isChi0Block_sup hS2 hSK (hL ⟨0, hs1⟩).1⟩

end Dichotomy

end CFSG.QuasithinUnique.Vol2Native.L239
