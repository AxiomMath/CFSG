module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_2Main
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ExpAux2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped Pointwise

section G

variable {G : Type} [Group G] [Finite G]

theorem MaximalRelativePair.normalizerExponent (hS : Setting G) (hD1 : TheoremD1 G)
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D R T : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) : NormalizerExponent p D := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hd.ext.transitivity_data hS hD1 hp hd.not_le_normalizer hR h13
  obtain ⟨hDe, hDc⟩ := hd.ext.isElemAbelian_of_isMulCommutative hprime hDab
  have hsyl := hd.ext.isSylowOf_centralizer hS hD1 hp hd.not_le_normalizer hDab hzD hz1 hzc hN₀M
  obtain ⟨n, hnP, hnD, hnC⟩ := hd.ext.exists_mem_normalizer_not_mem_centralizer hS hD1 hp
    hd.not_le_normalizer hDab hCD
  have hn : ∃ k : ℕ, n ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hnz : n * z = z * n := mem_centralizer_iff.mp hzc n hnP
  obtain ⟨g₁, hg₁N, hg₁M⟩ := IsConcreteLE.not_le_iff_exists.mp hd.ext.obstruction.2.2.2
  have hg₁z : g₁ * z * g₁⁻¹ ∉ zpowers z := by
    intro hmem
    apply hg₁M
    have hz₂p : (g₁ * z * g₁⁻¹) ^ p = 1 := by rw [conj_pow, hzp, mul_one, mul_inv_cancel]
    have hz₂1 : g₁ * z * g₁⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have : z = g₁⁻¹ * (g₁ * z * g₁⁻¹) * g₁ := by group
      rw [this, h]
      group
    have heq : zpowers (g₁ * z * g₁⁻¹) = zpowers z := Subgroup.eq_of_le_of_card_ge
      (zpowers_le.mpr hmem) (by rw [Nat.card_zpowers, Nat.card_zpowers,
        orderOf_eq_prime hzp hz1, orderOf_eq_prime hz₂p hz₂1])
    refine hN₀M ?_
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    exact heq
  obtain ⟨g, hgN, hg⟩ := zje_exists_inv hDe hDc hzD hz1 hn hnD hnz hnC hg₁N hg₁z
  exact zje_exp_of_inverting hodd hDe hDc
    (fun _ hy hyk => zje_mem_of_isSylowOf_centralizer hsyl hy hyk) hgN hg

end G

theorem NormalizerExponent.subgroupOf {p : ℕ} {G : Type*} [Group G] {D H : Subgroup G}
    (hDH : D ≤ H) (h : NormalizerExponent p D) : NormalizerExponent p (D.subgroupOf H) := by
  intro x hx hxk
  obtain ⟨k, hk⟩ := hxk
  have hxG : (x : G) ∈ normalizer (D : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact (mem_normalizer_iff.1 hx ⟨y, hDH hy⟩).1 hy
    · intro hy
      have hyH : y ∈ H := by
        have : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x := by group
        rw [this]
        exact H.mul_mem (H.mul_mem (H.inv_mem x.2) (hDH hy)) x.2
      exact (mem_normalizer_iff.1 hx ⟨y, hyH⟩).2 hy
  have hxp := h x hxG ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact Subtype.ext (by simpa using hxp)

theorem zje_isSylowOf_sup {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {K D : Subgroup Y} [K.Normal] (hK : p.Coprime (Nat.card K)) (hD : IsPGroup p D) :
    IsSylowOf p D (K ⊔ D) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [isSylowOf_iff]
  refine ⟨le_sup_right, hD, ?_⟩
  rw [relIndex_sup_eq_relIndex_of_normal]
  have hdvd : D.relIndex K ∣ Nat.card K := Dvd.intro _ (Subgroup.relIndex_mul_card D K)
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_right hdvd hK)

theorem zje_exists_mem_normalizer_of_map {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {K D : Subgroup Y} [K.Normal] (hK : p.Coprime (Nat.card K)) (hD : IsPGroup p D) {n₀ : Y}
    (hn₀ : QuotientGroup.mk' K n₀ ∈ normalizer ((D.map (QuotientGroup.mk' K) : Subgroup (Y ⧸ K))
      : Set (Y ⧸ K))) : ∃ k ∈ K, k⁻¹ * n₀ ∈ normalizer (D : Set Y) := by
  have : Fact p.Prime := ⟨hp⟩
  have hL : IsSylowOf p D (K ⊔ D) := zje_isSylowOf_sup hp hK hD
  have hLmem : ∀ u : Y, u ∈ K ⊔ D ↔ QuotientGroup.mk' K u ∈ D.map (QuotientGroup.mk' K) := by
    intro u
    have := Subgroup.comap_map_eq (QuotientGroup.mk' K) D
    rw [QuotientGroup.ker_mk', sup_comm] at this
    rw [← Subgroup.mem_comap, this]
  have hnL : ∀ u : Y, u ∈ K ⊔ D ↔ n₀ * u * n₀⁻¹ ∈ K ⊔ D := by
    intro u
    rw [hLmem, hLmem, map_mul, map_mul, map_inv]
    exact mem_normalizer_iff.1 hn₀ _
  have hD'le : D.map (MulAut.conj n₀).toMonoidHom ≤ K ⊔ D := by
    rintro _ ⟨d, hd, rfl⟩
    exact (hnL d).1 (Subgroup.mem_sup_right hd)
  have hD' : IsSylowOf p (D.map (MulAut.conj n₀).toMonoidHom) (K ⊔ D) := by
    refine isSylowOf_of_card hD'le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj n₀).injective, hL.card_eq]
  have hD'mem : ∀ v : Y, v ∈ D.map (MulAut.conj n₀).toMonoidHom ↔ n₀⁻¹ * v * n₀ ∈ D := by
    intro v
    constructor
    · rintro ⟨d, hd, rfl⟩
      have : n₀⁻¹ * (MulAut.conj n₀).toMonoidHom d * n₀ = d := by
        simp [MulAut.conj_apply]
        group
      rw [this]
      exact hd
    · intro hv
      exact ⟨n₀⁻¹ * v * n₀, hv, by simp [MulAut.conj_apply]; group⟩
  obtain ⟨l, hl, hconj⟩ := hL.exists_mem_conj hD'
  have hDK : D ≤ normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hlmul : l ∈ ((K : Subgroup Y) : Set Y) * (D : Set Y) := by
    rw [← coe_mul_of_right_le_normalizer_left K D hDK]
    exact hl
  obtain ⟨k₁, hk₁, d₁, hd₁, rfl⟩ := Set.mem_mul.1 hlmul
  refine ⟨k₁, hk₁, ?_⟩
  have hN : (k₁ * d₁)⁻¹ * n₀ ∈ normalizer (D : Set Y) := by
    rw [mem_normalizer_iff]
    intro u
    have h1 := hconj (n₀ * u * n₀⁻¹)
    rw [hD'mem] at h1
    have e1 : n₀⁻¹ * (n₀ * u * n₀⁻¹) * n₀ = u := by group
    rw [e1] at h1
    have e2 : (k₁ * d₁)⁻¹ * n₀ * u * ((k₁ * d₁)⁻¹ * n₀)⁻¹ =
        (k₁ * d₁)⁻¹ * (n₀ * u * n₀⁻¹) * (k₁ * d₁) := by group
    rw [e2]
    exact h1
  have hdN : d₁ ∈ normalizer (D : Set Y) := le_normalizer hd₁
  have e3 : k₁⁻¹ * n₀ = d₁ * ((k₁ * d₁)⁻¹ * n₀) := by group
  rw [e3]
  exact mul_mem hdN hN

theorem NormalizerExponent.quotient {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {K D : Subgroup Y} [K.Normal] (hK : p.Coprime (Nat.card K)) (hD : IsPGroup p D)
    (h : NormalizerExponent p D) : NormalizerExponent p (D.map (QuotientGroup.mk' K)) := by
  intro xb hxb hxk
  obtain ⟨k, hk⟩ := hxk
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk'_surjective K xb
  obtain ⟨k₁, hk₁, hN⟩ := zje_exists_mem_normalizer_of_map hp hK hD hxb
  set n : Y := k₁⁻¹ * n₀ with hn
  have hπn : QuotientGroup.mk' K n = QuotientGroup.mk' K n₀ := by
    have h1 : QuotientGroup.mk' K k₁ = 1 := (QuotientGroup.eq_one_iff k₁).2 hk₁
    rw [hn, map_mul, map_inv, h1, inv_one, one_mul]
  have hnK : n ^ p ^ k ∈ K := by
    rw [← QuotientGroup.ker_mk' K, MonoidHom.mem_ker, map_pow, hπn]
    exact hk
  have hcop : Nat.Coprime (p ^ k) (orderOf (n ^ p ^ k)) :=
    Nat.Coprime.pow_left k
      (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard K hnK) hK)
  obtain ⟨t, ht1, ht0⟩ := Nat.chineseRemainder hcop 1 0
  have hnt : n ^ t ∈ normalizer (D : Set Y) := pow_mem hN t
  have hntk : (n ^ t) ^ p ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 (Nat.modEq_zero_iff_dvd.1 ht0)
  have hπt : QuotientGroup.mk' K (n ^ t) = QuotientGroup.mk' K n₀ := by
    rw [map_pow, hπn, pow_eq_pow_mod t hk, ht1, ← pow_eq_pow_mod 1 hk, pow_one]
  have := h (n ^ t) hnt ⟨k, hntk⟩
  rw [← hπt, ← map_pow, this, map_one]

end CFSG.LocalAnalysis.RankThreeTheoremC
