module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBlocks

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Pair

variable {G : Type} [Group G] [Finite G]

theorem false_of_mem_centralizer_of_small {M L T : Subgroup G} (hL : IsTwoPrimeComponent M L)
    {y : G} (hyL : y ∈ L) (hy3 : IsPGroup 3 (Subgroup.zpowers y))
    (hyl : ∃ l ∈ L, y * l * y⁻¹ * l⁻¹ ∉ pCoreOf 2 M) {a : G} (haM : a ∈ M)
    (ha3 : IsPGroup 3 (Subgroup.zpowers a)) (haC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (ha1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩ ≠ 1) (hTM : T ≤ M)
    (hQT : pCoreOf 2 M ≤ T) (hyT : y ∈ T) (haT : a ∈ T)
    (hT3 : ∀ B : Subgroup G, B ≤ T → IsPGroup 3 B → Nat.card B ≤ 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hyM : y ∈ M := hL.le hyL
  set yb := mk ⟨y, hyM⟩ with hyb
  set yb' := mk ⟨a, haM⟩ with hyb'
  have hybL : yb ∈ barM M L := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL)
  have hybC : yb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro hC
    obtain ⟨l, hl, hyl'⟩ := hyl
    apply hyl'
    have hlb : mk ⟨l, hL.le hl⟩ ∈ barM M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
    have h1 := Subgroup.mem_centralizer_iff.mp hC _ hlb
    have h2 : mk (⟨y, hyM⟩ * ⟨l, hL.le hl⟩ * ⟨y, hyM⟩⁻¹ * ⟨l, hL.le hl⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hyb, ← h1]
      group
    exact coe_mem_pCoreOf_two_of_mk_eq_one _ h2
  have hcy : yb * yb' = yb' * yb := Subgroup.mem_centralizer_iff.mp haC yb hybL
  obtain ⟨e, he⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
  have hye : y ^ 3 ^ e = 1 := by simpa using congrArg Subtype.val he
  have hybe : yb ^ 3 ^ e = 1 := by
    rw [hyb, ← map_pow]
    have : (⟨y, hyM⟩ : M) ^ 3 ^ e = 1 := Subtype.ext (by simpa using hye)
    rw [this, map_one]
  obtain ⟨e', he'⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hae : a ^ 3 ^ e' = 1 := by simpa using congrArg Subtype.val he'
  have hyb'e : yb' ^ 3 ^ e' = 1 := by
    rw [hyb', ← map_pow]
    have : (⟨a, haM⟩ : M) ^ 3 ^ e' = 1 := Subtype.ext (by simpa using hae)
    rw [this, map_one]
  set A := Subgroup.zpowers yb ⊔ Subgroup.zpowers yb' with hA
  have hA3 : IsPGroup 3 A := by
    refine IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_prime_pow_eq_one hybe)
      (isPGroup_zpowers_of_pow_prime_pow_eq_one hyb'e) ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer
      (s := (Subgroup.zpowers yb : Set (↥M ⧸ CFSG.pCore 2 ↥M))))
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left hcy n).eq
  have hle' : Subgroup.zpowers yb' ≤ A := le_sup_right
  have hybA : yb ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers yb)
  have hybn : yb ∉ Subgroup.zpowers yb' := fun h' =>
    hybC ((Subgroup.zpowers_le.mpr haC) h')
  obtain ⟨a', ha'⟩ := (isPGroup_zpowers_of_pow_prime_pow_eq_one hyb'e).exists_card_eq
  obtain ⟨b, hb⟩ := hA3.exists_card_eq
  have ha'1 : a' ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at ha'
    exact ha1 (Subgroup.zpowers_eq_bot.mp ha')
  have hab : a' < b := by
    have hdvd := Subgroup.card_dvd_of_le hle'
    rw [ha', hb] at hdvd
    have hab' := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd
    rcases hab'.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      apply hybn
      have heq := Subgroup.eq_of_le_of_card_ge hle' (by rw [ha', hb, h'])
      exact heq ▸ hybA
  have hA9 : 9 ≤ Nat.card A := by
    rw [hb]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAT : A ≤ barM M T := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyT)
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haT)
  obtain ⟨B, hBT, hB3, hBc⟩ := exists_isPGroup_le_of_le_barM hTM hQT (by norm_num) hA3 hAT
  have := hT3 B hBT hB3
  omega

end Pair

end CFSG.AGLEmbedding
