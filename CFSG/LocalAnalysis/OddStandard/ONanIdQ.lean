module

public import CFSG.LocalAnalysis.OddStandard.ONanIdStab

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
open scoped Pointwise

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem card_Q :
    Nat.card ↥(alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G)) = 256 := by
  rw [(AlpEmb.centralizer_special_alpP D.E D.hF).2.1, AlpEmb.card_genMax D.E D.hF 0]

theorem y0_mem_P : v1 * v3 ∈ alpP v1 v2 v3 s t := D.V_le_P D.y0_mem_V

theorem isSylowOf_Q : IsSylowOf 2 (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G))
    (centralizer ({v1 * v3} : Set G)) := by
  refine isSylowOf_of_card_le D.isSylowOf_P D.y0_mem_P fun g hg => ?_
  rw [D.card_Q]
  set y := g⁻¹ * (v1 * v3) * g with hy
  have hy2 : y * y ≠ 1 := by
    intro h
    apply D.rep_ne_one 0
    calc invRep v1 v2 v3 s t 0 = g * (y * y) * g⁻¹ := by rw [hy, ← D.y0_sq]; group
      _ = 1 := by rw [h]; group
  have hnc : ¬ alpP v1 v2 v3 s t ≤ centralizer ({y} : Set G) := by
    intro h
    have hc : ∀ c ∈ alpP v1 v2 v3 s t, c * y = y * c := fun c hc =>
      mem_centralizer_singleton_iff.1 (h hc)
    rcases (AlpEmb.centre_alpP D.E D.hF hg).1 hc with h1 | h1
    · apply hy2
      rw [h1, mul_one]
    · apply hy2
      rw [h1]
      exact D.rep_sq 0
  set C := alpP v1 v2 v3 s t ⊓ centralizer ({y} : Set G) with hC
  have h1 := relIndex_mul_card (H := C) (K := alpP v1 v2 v3 s t)
  rw [inf_of_le_left inf_le_left, AlpEmb.card_alpP D.E] at h1
  have hr1 : C.relIndex (alpP v1 v2 v3 s t) ≠ 1 := by
    intro h
    rw [relIndex_eq_one] at h
    exact hnc (le_trans h inf_le_right)
  have hr0 : C.relIndex (alpP v1 v2 v3 s t) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    omega
  have hr2 : 2 ≤ C.relIndex (alpP v1 v2 v3 s t) := by omega
  nlinarith

omit [Finite G] D in
theorem normalizer_V_le_normalizer_centralizer :
    normalizer (alpV v1 v2 v3 : Set G) ≤
      normalizer (centralizer (alpV v1 v2 v3 : Set G) : Set G) := by
  intro n hn
  have key : ∀ m : G, m ∈ normalizer (alpV v1 v2 v3 : Set G) → ∀ c : G,
      c ∈ centralizer (alpV v1 v2 v3 : Set G) →
      m * c * m⁻¹ ∈ centralizer (alpV v1 v2 v3 : Set G) := by
    intro m hm c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : m⁻¹ * v * m ∈ alpV v1 v2 v3 := by
      have := conj_mem_V (inv_mem hm) hv
      rwa [inv_inv] at this
    have h := hc _ hv'
    calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [h]
      _ = m * c * m⁻¹ * v := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key n hn c, fun h => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ h
  rwa [show n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c by group] at this

omit [Finite G] D in
theorem centralizer_V_le_centralizer_y0 :
    centralizer (alpV v1 v2 v3 : Set G) ≤ centralizer ({v1 * v3} : Set G) := by
  intro c hc
  rw [mem_centralizer_singleton_iff]
  have hv : v1 * v3 ∈ alpV v1 v2 v3 := mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  exact (mem_centralizer_iff.1 hc _ hv).symm

theorem exists_mem_Q_of_normalizer {n : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hy : n * (v1 * v3) = v1 * v3 * n) :
    ∃ q ∈ alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G),
      q⁻¹ * n ∈ centralizer (alpV v1 v2 v3 : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer ({v1 * v3} : Set G) with hY
  set Q := alpP v1 v2 v3 s t ⊓ Y with hQ
  set CV := centralizer (alpV v1 v2 v3 : Set G) with hCV
  set NY := normalizer (alpV v1 v2 v3 : Set G) ⊓ Y with hNY
  have hCVNY : CV ≤ NY := fun c hc =>
    ⟨centralizer_le_normalizer _ hc, centralizer_V_le_centralizer_y0 hc⟩
  have hQNY : Q ≤ NY := fun q hq => ⟨D.P_le_normalizer_V hq.1, hq.2⟩
  have hQN : Q ≤ normalizer (CV : Set G) := fun q hq =>
    normalizer_V_le_normalizer_centralizer (D.P_le_normalizer_V hq.1)
  set R := Q ⊔ CV with hR
  have hRNY : R ≤ NY := sup_le hQNY hCVNY
  have hCVR : CV ≤ R := le_sup_right
  have hnorm : (CV.subgroupOf NY).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hCVNY]
    exact fun m hm => normalizer_V_le_normalizer_centralizer hm.1
  have h2grp : IsPGroup 2 (NY ⧸ CV.subgroupOf NY) := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := D.exists_pow_mem_centralizer_V m.2.1
      (mem_centralizer_singleton_iff.1 m.2.2)
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simpa using he
  obtain ⟨a, ha⟩ := h2grp.exists_card_eq
  have hidx : CV.relIndex NY = 2 ^ a := by
    rw [relIndex, index, ha]
  have hmul := relIndex_mul_relIndex CV R NY hCVR hRNY
  rw [hidx] at hmul
  have hdvd : R.relIndex NY ∣ 2 ^ a := Dvd.intro_left _ hmul
  have hodd : ¬ 2 ∣ R.relIndex NY := by
    have hS : IsSylowOf 2 Q NY := D.isSylowOf_Q.of_le hQNY inf_le_right
    have hQR : Q ≤ R := le_sup_left
    intro h2
    have := (isSylowOf_iff.1 hS).2.2
    apply this
    rw [← relIndex_mul_relIndex Q R NY hQR hRNY]
    exact h2.mul_left _
  have hone : R.relIndex NY = 1 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rcases k with _ | k
    · simpa using hk
    · exact absurd (hk ▸ dvd_pow_self 2 (Nat.succ_ne_zero k)) hodd
  have hNYR : NY ≤ R := relIndex_eq_one.1 hone
  have hnR : n ∈ R := hNYR ⟨hn, mem_centralizer_singleton_iff.2 hy⟩
  have hset := coe_mul_of_left_le_normalizer_right Q CV hQN
  have hnR' : n ∈ ((Q : Set G) * (CV : Set G)) := by
    rw [← hset]
    exact hnR
  obtain ⟨q, hq, c, hc, rfl⟩ := hnR'
  refine ⟨q, hq, ?_⟩
  rw [inv_mul_cancel_left]
  exact hc

end FusCtx

end CFSG.OddStandard.ONanRec
