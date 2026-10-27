module

public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.Foundations.Basic

public section

namespace CFSG

open scoped Pointwise

theorem QuasithinUnique.charTwo_iff_isCharacteristicP {G : Type*} [Group G] {K : Subgroup G} :
    QuasithinUnique.CharTwo K ↔ IsCharacteristicP 2 K := by
  rw [QuasithinUnique.charTwo_iff_internal, IsCharacteristicP]

theorem Assembly.isTwoLocal_iff_isPLocal {G : Type*} [Group G] {H : Subgroup G} :
    Assembly.IsTwoLocal H ↔ IsPLocal 2 H :=
  Iff.rfl

theorem Assembly.isCharTwoType_iff_isCharacteristicPType {G : Type*} [Group G] :
    Assembly.IsCharTwoType G ↔ IsCharacteristicPType G 2 :=
  forall_congr' fun _ => imp_congr Iff.rfl QuasithinUnique.charTwo_iff_isCharacteristicP

theorem QuasithinUnique.CharTwo.of_pCoreOf_le {G : Type*} [Group G] {M X : Subgroup G}
    (hM : QuasithinUnique.CharTwo M) (hXM : X ≤ M) (hOX : Open.pCoreOf 2 M ≤ X) :
    QuasithinUnique.CharTwo X := by
  have hnorm : Open.pCoreOf 2 M ≤ Open.pCoreOf 2 X :=
    RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (Open.pCoreOf 2 M) X hOX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr
        (hXM.trans (RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)))
      (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  intro x hx
  exact hnorm (hM ⟨hXM hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hnorm) hx.2⟩)

private theorem exists_mul_pow_eq {G : Type*} [Group G] {K S : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) {k s : G} (hk : k ∈ K) (hs : s ∈ S) :
    ∀ m : ℕ, ∃ k' ∈ K, (k * s) ^ m = k' * s ^ m
  | 0 => ⟨1, K.one_mem, by simp⟩
  | m + 1 => by
    obtain ⟨k', hk', h⟩ := exists_mul_pow_eq hSK hk hs m
    refine ⟨k' * (s ^ m * k * (s ^ m)⁻¹), K.mul_mem hk'
      ((Subgroup.mem_normalizer_iff.mp (hSK (S.pow_mem hs m)) k).mp hk), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem QuasithinUnique.CharTwo.sup_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {K S : Subgroup G} (hK : QuasithinUnique.CharTwo K) (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) : QuasithinUnique.CharTwo (K ⊔ S) := by
  set X : Subgroup G := K ⊔ S with hXdef
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hSK
  have hOK : Open.pCoreOf 2 K ≤ X :=
    (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K).trans le_sup_left
  have hKQ : Open.pCoreOf 2 K ≤ Open.pCoreOf 2 X :=
    RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ X hOK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOK).mpr (hXK.trans
        (RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 K)))
      (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K)
  set D : Subgroup G := X ⊓ Subgroup.centralizer (Open.pCoreOf 2 X : Set G) with hDdef
  have hDp : IsPGroup 2 D := by
    rintro ⟨d, hdX, hdC⟩
    have hmul : ((K ⊔ S : Subgroup G) : Set G) = (K : Set G) * (S : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left K S hSK
    have hd' : d ∈ (K : Set G) * (S : Set G) := by rw [← hmul]; exact hdX
    obtain ⟨k, hk, s, hs, rfl⟩ := hd'
    obtain ⟨n, hn⟩ := hS ⟨s, hs⟩
    have hsn : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨k', hk', hpow⟩ := exists_mul_pow_eq hSK hk hs (2 ^ n)
    rw [hsn, mul_one] at hpow
    have hk'D : k' ∈ D := hpow ▸ D.pow_mem ⟨hdX, hdC⟩ _
    have hk'O : k' ∈ Open.pCoreOf 2 K :=
      hK ⟨hk', Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hKQ) hk'D.2⟩
    obtain ⟨m, hm⟩ := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K ⟨k', hk'O⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have hm' : k' ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, hpow, hm']
  have hDX : D ≤ X := inf_le_left
  have hXD : X ≤ Subgroup.normalizer (D : Set G) :=
    RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _ Subgroup.le_normalizer
      ((RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X).trans
        (RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer _))
  intro x hx
  exact RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 D X hDX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mpr hXD) hDp hx

end CFSG
