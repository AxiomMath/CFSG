module

public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesSection
public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesSigns

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalGeneralBase
  CFSG.Wreathed.ConditionalCompleteBase CFSG.Wreathed.ConditionalFiveFixed

theorem multiset_degrees (a b c d e u w : ℤ) (M k N : ℕ) :
    ({a, b, c, d, e} : Multiset ℤ) + Multiset.replicate M u + Multiset.replicate k c +
        Multiset.replicate k d + Multiset.replicate N w =
      {a, b, e} + Multiset.replicate (k + 1) c + Multiset.replicate (k + 1) d +
        Multiset.replicate M u + Multiset.replicate N w := by
  simp only [Multiset.insert_eq_cons, Multiset.replicate_succ, ← Multiset.singleton_add]
  abel

theorem zpow_neg_odd_half {m M : ℕ} [NeZero m] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hm : m = 2 * M) {j : ℕ} (hj : Odd j) : ζ ^ (-((j : ℤ) * M)) = -1 := by
  rw [zpow_neg, show ((j : ℤ) * M) = ((j * M : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    pow_mul', pow_half_eq_neg_one hζ hm, hj.neg_one_pow, inv_neg, inv_one]

theorem neg_one_pow_three_sum (i j : ℕ) :
    ((-1 : ℂ) ^ i + (-1) ^ j + (-1) ^ (i + j)) = if Even i ∧ Even j then 3 else -1 := by
  rw [pow_add]
  rcases Nat.even_or_odd i with hi | hi <;> rcases Nat.even_or_odd j with hj | hj
  · rw [hi.neg_one_pow, hj.neg_one_pow, ite_eq_left ⟨hi, hj⟩]
    norm_num
  · rw [hi.neg_one_pow, hj.neg_one_pow, ite_eq_right fun h => (Nat.not_even_iff_odd.mpr hj) h.2]
    norm_num
  · rw [hi.neg_one_pow, hj.neg_one_pow, ite_eq_right fun h => (Nat.not_even_iff_odd.mpr hi) h.1]
    norm_num
  · rw [hi.neg_one_pow, hj.neg_one_pow, ite_eq_right fun h => (Nat.not_even_iff_odd.mpr hi) h.1]
    norm_num

variable {ι : Type*} [DecidableEq ι] {G : Type*} [Group G]

namespace SectionTable

variable {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {m M : ℕ} [NeZero m] {J : Finset ℕ}
  {χ : ℕ → ι} {γ : ℕ → Fin 4 → ι} {εs : ℕ → Fin 4 → ℤ} {P Q : ℕ → Fin 2 → ι}
  {er : ℕ → Fin 2} {ψ : ZMod m × ZMod m → ι} {ρ₀ : ℤ} {V : Finset (ZMod m × ZMod m)}
  {yc cc : ℕ → ι → ℤ} {Cz : ZMod m → ZMod m → ι → ℤ} {ζ : ℂ} {Xf : ι → ℕ → ℂ}
  {cb : ZMod m → ZMod m → ι → ℂ} {ch : ι → G → ℂ} {a : G} {Φ : G → ℂ} {ε : ℤ}
  (S : SectionTable B p A Bq Dq ω σ τ₀ κ m M J χ γ εs P Q er ψ ρ₀ V yc cc Cz ζ Xf cb ch a Φ ε)
include S

theorem half_even : Even M := by
  obtain ⟨n, hn⟩ := S.hpow
  have h1 := S.hm
  have h2 := S.hM
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := by
    rcases n with _ | _ | k
    · simp at hn
      omega
    · simp at hn
      omega
    · exact ⟨k, rfl⟩
  refine ⟨2 ^ k, ?_⟩
  rw [pow_add] at hn
  norm_num at hn
  omega

theorem one_mem : 1 ∈ Finset.Ico 1 M := by
  have h := S.hM
  exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩

theorem weighted_equations {deg : ι → ℤ} {q : ℕ} (hp1 : ∀ g, ch p g = 1)
    (h1 : ∀ φ ∈ B, ch φ 1 = deg φ) (hε : ε = 1 ∨ ε = -1) (hΦ1 : Φ 1 = q)
    (hdegPQ : ∀ e, deg (P 1 e) = deg Bq ∧ deg (Q 1 e) = deg Dq)
    (hWY : ∑ φ ∈ B, (yc 0 φ : ℂ) * (ch φ (a ^ M) * ch φ (a ^ M) / ch φ 1) = 0)
    (hWX : ∑ φ ∈ B, (cc (m - 2 * 1) φ : ℂ) * (ch φ (a ^ M) * ch φ (a ^ M) / ch φ 1) = 0) :
    (1 : ℂ) + σ * ((q : ℂ) ^ 2 / deg A) - τ₀ * ((2 + ε * q) ^ 2 / deg Bq) +
        κ * ((1 + 2 * ε * q) ^ 2 / deg Dq) = 0 ∧
      -(1 : ℂ) - σ * ((q : ℂ) ^ 2 / deg A) - τ₀ * ((2 + ε * q) ^ 2 / deg Bq) +
        κ * ((1 + 2 * ε * q) ^ 2 / deg Dq) + τ₀ * ((q : ℂ) ^ 2 / deg Bq + (q : ℂ) ^ 2 / deg Bq) -
        κ * (1 / deg Dq + 1 / deg Dq) = 0 := by
  have T := S.toColumnTable
  have hσ2 : (σ : ℂ) * σ = 1 := by rcases T.core.hσ with h | h <;> rw [h] <;> norm_num
  have hτ2 : (τ₀ : ℂ) * τ₀ = 1 := by rcases T.core.hτ₀ with h | h <;> rw [h] <;> norm_num
  have hκ2 : (κ : ℂ) * κ = 1 := by rcases T.core.hκ with h | h <;> rw [h] <;> norm_num
  have hε2 : (ε : ℂ) * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hnegM : (-1 : ℂ) ^ M = 1 := S.half_even.neg_one_pow
  have hz := Subgroup.one_mem (Subgroup.centralizer {a ^ M})
  have hzo : Odd (orderOf (1 : G)) := by simp
  have vA1 := S.vA S.half_mem hz hzo
  have vB1 := S.vB S.half_mem hz hzo
  have vD1 := S.vD S.half_mem hz hzo
  rw [mul_one, hΦ1] at vA1 vB1 vD1
  rw [hnegM] at vB1 vD1
  set wt : ι → ℂ := fun φ => ch φ (a ^ M) * ch φ (a ^ M) / ch φ 1 with hwt
  have wp : wt p = 1 := by simp [hwt, hp1]
  have wA : wt A = (q : ℂ) ^ 2 / deg A := by
    rw [hwt]
    dsimp only
    rw [vA1, h1 A T.core.hA]
    linear_combination ((ε : ℂ) ^ 2 * (q : ℂ) ^ 2 / deg A) * hσ2 + ((q : ℂ) ^ 2 / deg A) * hε2
  have wB : wt Bq = (2 + ε * q) ^ 2 / deg Bq := by
    rw [hwt]
    dsimp only
    rw [vB1, h1 Bq T.core.hBq]
    linear_combination ((2 + ε * (q : ℂ)) ^ 2 / deg Bq) * hτ2
  have wD : wt Dq = (1 + 2 * ε * q) ^ 2 / deg Dq := by
    rw [hwt]
    dsimp only
    rw [vD1, h1 Dq T.core.hDq]
    linear_combination ((1 + 2 * ε * (q : ℂ)) ^ 2 / deg Dq) * hκ2
  have wP : ∀ e, wt (P 1 e) = (q : ℂ) ^ 2 / deg Bq := fun e => by
    rw [hwt]
    dsimp only
    rw [S.vPx S.one_mem e, h1 _ (T.P_mem S.one_mem e), (hdegPQ e).1, hΦ1]
    linear_combination ((ε : ℂ) ^ 2 * (q : ℂ) ^ 2 / deg Bq) * hτ2 +
      ((q : ℂ) ^ 2 / deg Bq) * hε2
  have wQ : ∀ e, wt (Q 1 e) = 1 / deg Dq := fun e => by
    rw [hwt]
    dsimp only
    rw [S.vQx S.one_mem e, h1 _ (T.Q_mem S.one_mem e), (hdegPQ e).2, hΦ1]
    linear_combination (1 / (deg Dq : ℂ)) * hκ2
  rw [T.sum_y0_mul wt, wp, wA, wB, wD] at hWY
  rw [T.sum_x_mul S.one_mem wt, wp, wA, wB, wD, wP 0, wP 1, wQ 0, wQ 1] at hWX
  exact ⟨hWY, hWX⟩

theorem signs {deg : ι → ℤ} {q : ℕ} (hp1 : ∀ g, ch p g = 1)
    (h1 : ∀ φ ∈ B, ch φ 1 = deg φ) (hpos : ∀ φ ∈ B, 0 < deg φ) (hq : 3 ≤ q)
    (hε : ε = 1 ∨ ε = -1) (hΦ1 : Φ 1 = q)
    (hdeg0 : (1 : ℂ) + σ * ch A 1 - τ₀ * ch Bq 1 + κ * ch Dq 1 = 0)
    (hdegPQ : ∀ e, deg (P 1 e) = deg Bq ∧ deg (Q 1 e) = deg Dq)
    (hWY : ∑ φ ∈ B, (yc 0 φ : ℂ) * (ch φ (a ^ M) * ch φ (a ^ M) / ch φ 1) = 0)
    (hWX : ∑ φ ∈ B, (cc (m - 2 * 1) φ : ℂ) * (ch φ (a ^ M) * ch φ (a ^ M) / ch φ 1) = 0) :
    σ = -ε ∧ τ₀ = 1 ∧ κ = ε ∧ deg A = (q : ℤ) ^ 3 ∧ deg Bq = (q : ℤ) ^ 2 + ε * q + 1 ∧
      deg Dq = q * ((q : ℤ) ^ 2 + ε * q + 1) := by
  have T := S.toColumnTable
  obtain ⟨E1, E2⟩ := S.weighted_equations hp1 h1 hε hΦ1 hdegPQ hWY hWX
  have hY : 1 + σ * deg A - τ₀ * deg Bq + κ * deg Dq = 0 := by
    rw [h1 A T.core.hA, h1 Bq T.core.hBq, h1 Dq T.core.hDq] at hdeg0
    exact_mod_cast hdeg0
  exact signs_of_weighted (q := (q : ℤ)) (by exact_mod_cast hq) hε T.core.hσ T.core.hτ₀
    T.core.hκ (hpos A T.core.hA) (hpos Bq T.core.hBq) (hpos Dq T.core.hDq) hY
    (by push_cast; exact E1) (by push_cast; exact E2)

theorem x_values {q : ℕ} (hp1 : ∀ g, ch p g = 1) (hε : ε = 1 ∨ ε = -1) (hΦ1 : Φ 1 = q)
    (hσε : σ = -ε) (hτ1 : τ₀ = 1) (hκε : κ = ε) (hρ₀ : ρ₀ = -ε)
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6) :
    ch p (a ^ M) = 1 ∧ ch A (a ^ M) = q ∧ ch Bq (a ^ M) = 2 + ε * q ∧
      ch Dq (a ^ M) = 2 * q + ε ∧ ch ω (a ^ M) = 1 + ε * q ∧
      (∀ j ∈ J, ch (χ j) (a ^ M) = ε - q) ∧
      (∀ r ∈ Finset.Ico 1 M, ∀ e', ch (P r e') (a ^ M) = (if Odd r then -ε * q else 2 + ε * q) ∧
        ch (Q r e') (a ^ M) = (if Odd r then -ε else 2 * q + ε)) ∧
      ∀ I ∈ V, ch (ψ I) (a ^ M) =
        if Even I.1.val ∧ Even I.2.val then 3 * (q + ε) else -(q + ε) := by
  have T := S.toColumnTable
  have hε2 : (ε : ℂ) * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hnegM : (-1 : ℂ) ^ M = 1 := S.half_even.neg_one_pow
  have hz := Subgroup.one_mem (Subgroup.centralizer {a ^ M})
  have hzo : Odd (orderOf (1 : G)) := by simp
  have vA1 := S.vA S.half_mem hz hzo
  have vB1 := S.vB S.half_mem hz hzo
  have vD1 := S.vD S.half_mem hz hzo
  have vω1 := S.vω S.half_mem hz hzo
  rw [mul_one, hΦ1] at vA1 vB1 vD1 vω1
  rw [hnegM] at vB1 vD1
  refine ⟨hp1 _, ?_, ?_, ?_, ?_, fun j hj => ?_, fun r hr e' => ⟨?_, ?_⟩, fun I hI => ?_⟩
  · rw [vA1, hσε]
    push_cast
    linear_combination (q : ℂ) * hε2
  · rw [vB1, hτ1]
    push_cast
    ring
  · rw [vD1, hκε]
    linear_combination (2 * (q : ℂ)) * hε2
  · rw [vω1, hτ1]
    push_cast
    ring
  · have hjm : j ∈ Finset.Ico 1 m := by
      have h := T.hJ
      rw [h] at hj
      exact (Finset.mem_filter.mp hj).1
    have hjo : Odd j := by
      have h := T.hJ
      rw [h] at hj
      exact (Finset.mem_filter.mp hj).2
    have hv := S.vχ hj S.half_mem hz hzo
    rw [mul_one, hΦ1, zpow_neg_odd_half S.hζ T.hm hjo, hσε] at hv
    rw [hv]
    push_cast
    linear_combination (-(q : ℂ)) * hε2
  · rw [S.vPx hr e', hΦ1, hτ1]
    split_ifs with ho
    · rw [ho.neg_one_pow]
      push_cast
      ring
    · rw [(Nat.not_odd_iff_even.mp ho).neg_one_pow]
      push_cast
      ring
  · rw [S.vQx hr e', hΦ1, hκε]
    split_ifs with ho
    · rw [ho.neg_one_pow]
      push_cast
      ring
    · rw [(Nat.not_odd_iff_even.mp ho).neg_one_pow]
      push_cast
      linear_combination (2 * (q : ℂ)) * hε2
  · rw [S.vψx hI (hV6 I hI), hΦ1, hρ₀, neg_one_pow_three_sum]
    split_ifs
    · push_cast
      linear_combination (3 * (q : ℂ)) * hε2
    · push_cast
      linear_combination (-(q : ℂ)) * hε2

theorem section_values (hε : ε = 1 ∨ ε = -1) (hσε : σ = -ε) (hτ1 : τ₀ = 1) (hκε : κ = ε) :
    ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
      ch A (a ^ k * z) = Φ z ∧ ch ω (a ^ k * z) = 1 + ε * Φ z ∧
      ch Bq (a ^ k * z) = 1 + (-1) ^ k * (1 + ε * Φ z) ∧
      ch Dq (a ^ k * z) = -ε + ε * (1 + (-1) ^ k) * (1 + ε * Φ z) ∧
      ∀ j ∈ J, ch (χ j) (a ^ k * z) = (Φ z - ε) * ζ ^ (-((j : ℤ) * k)) := by
  intro k hk z hz hzo
  have hε2 : (ε : ℂ) * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [S.vA hk hz hzo, hσε]
    push_cast
    linear_combination Φ z * hε2
  · rw [S.vω hk hz hzo, hτ1]
    push_cast
    ring
  · rw [S.vB hk hz hzo, hτ1]
    push_cast
    ring
  · rw [S.vD hk hz hzo, hκε]
    ring
  · rw [S.vχ hj hk hz hzo, hσε]
    push_cast
    linear_combination (Φ z * ζ ^ (-((j : ℤ) * k))) * hε2

theorem global_conclusions {deg : ι → ℤ} {q : ℕ} {Δ : ℤ} {δ : ℕ} (hp1 : ∀ g, ch p g = 1)
    (h1 : ∀ φ ∈ B, ch φ 1 = deg φ) (hpos : ∀ φ ∈ B, 0 < deg φ) (hq : 3 ≤ q)
    (hε : ε = 1 ∨ ε = -1) (hΦ1 : Φ 1 = q)
    (hdeg0 : (1 : ℂ) + σ * ch A 1 - τ₀ * ch Bq 1 + κ * ch Dq 1 = 0)
    (hWY : ∑ φ ∈ B, (yc 0 φ : ℂ) * (ch φ (a ^ M) * ch φ (a ^ M) / ch φ 1) = 0)
    (hWX : ∑ φ ∈ B, (cc (m - 2 * 1) φ : ℂ) * (ch φ (a ^ M) * ch φ (a ^ M) / ch φ 1) = 0)
    (hdegPQ : ∀ r ∈ Finset.Ico 1 M, ∀ e, deg (P r e) = deg Bq ∧ deg (Q r e) = deg Dq)
    (hdω : deg ω = deg Bq - τ₀) (hdχ : ∀ j ∈ J, ch (χ j) 1 = δ) (hδ : (δ : ℂ) = ch A 1 + σ)
    (hρ₀ : ρ₀ = 1 ∨ ρ₀ = -1) (hΔ : 0 < Δ) (hρΔ : ρ₀ * Δ = -(τ₀ * deg Bq + κ * deg Dq))
    (hψd : ∀ I ∈ V, deg (ψ I) = Δ) (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6)
    (hmul : Multiset.map deg B.val = {1, deg A, deg Bq, deg Dq, deg Bq - τ₀} +
      Multiset.replicate M (δ : ℤ) + Multiset.replicate (m - 2) (deg Bq) +
      Multiset.replicate (m - 2) (deg Dq) + Multiset.replicate ((m - 1) * (m - 2) / 6) Δ) :
    (σ = -ε ∧ τ₀ = 1 ∧ κ = ε ∧ ρ₀ = -ε) ∧
    (deg A = (q : ℤ) ^ 3 ∧ deg Bq = (q : ℤ) ^ 2 + ε * q + 1 ∧
      deg Dq = q * ((q : ℤ) ^ 2 + ε * q + 1) ∧ deg ω = q * (q + ε) ∧
      (∀ j ∈ J, deg (χ j) = (q : ℤ) ^ 3 - ε) ∧
      (∀ r ∈ Finset.Ico 1 M, ∀ e', deg (P r e') = (q : ℤ) ^ 2 + ε * q + 1 ∧
        deg (Q r e') = q * ((q : ℤ) ^ 2 + ε * q + 1)) ∧
      (∀ I ∈ V, deg (ψ I) = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1)) ∧
      Δ = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1)) ∧
    Multiset.map deg B.val = {1, (q : ℤ) ^ 3, q * (q + ε)} +
      Multiset.replicate (m - 1) ((q : ℤ) ^ 2 + ε * q + 1) +
      Multiset.replicate (m - 1) (q * ((q : ℤ) ^ 2 + ε * q + 1)) +
      Multiset.replicate M ((q : ℤ) ^ 3 - ε) +
      Multiset.replicate ((m - 1) * (m - 2) / 6) ((q + ε) * ((q : ℤ) ^ 2 + ε * q + 1)) ∧
    (ch p (a ^ M) = 1 ∧ ch A (a ^ M) = q ∧ ch Bq (a ^ M) = 2 + ε * q ∧
      ch Dq (a ^ M) = 2 * q + ε ∧ ch ω (a ^ M) = 1 + ε * q ∧
      (∀ j ∈ J, ch (χ j) (a ^ M) = ε - q) ∧
      (∀ r ∈ Finset.Ico 1 M, ∀ e', ch (P r e') (a ^ M) = (if Odd r then -ε * q else 2 + ε * q) ∧
        ch (Q r e') (a ^ M) = (if Odd r then -ε else 2 * q + ε)) ∧
      ∀ I ∈ V, ch (ψ I) (a ^ M) =
        if Even I.1.val ∧ Even I.2.val then 3 * (q + ε) else -(q + ε)) ∧
    ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
      ch A (a ^ k * z) = Φ z ∧ ch ω (a ^ k * z) = 1 + ε * Φ z ∧
      ch Bq (a ^ k * z) = 1 + (-1) ^ k * (1 + ε * Φ z) ∧
      ch Dq (a ^ k * z) = -ε + ε * (1 + (-1) ^ k) * (1 + ε * Φ z) ∧
      ∀ j ∈ J, ch (χ j) (a ^ k * z) = (Φ z - ε) * ζ ^ (-((j : ℤ) * k)) := by
  have T := S.toColumnTable
  obtain ⟨hσε, hτ1, hκε, hdA, hdB, hdD⟩ := S.signs hp1 h1 hpos hq hε hΦ1 hdeg0
    (hdegPQ 1 S.one_mem) hWY hWX
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq3 : (3 : ℤ) ≤ q := by exact_mod_cast hq
  have hQd : (0 : ℤ) < (q : ℤ) ^ 2 + ε * q + 1 := by
    rcases hε with h | h <;> rw [h] <;> nlinarith
  rw [hτ1, hκε, hdB, hdD] at hρΔ
  have hρε : ρ₀ = -ε := by
    rcases hρ₀ with h | h <;> rcases hε with h' | h' <;> rw [h, h'] at hρΔ ⊢ <;>
      first | rfl | (exfalso; nlinarith)
  have hΔv : Δ = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1) := by
    rw [hρε] at hρΔ
    rcases hε with h | h <;> rw [h] at hρΔ ⊢ <;> linarith
  have hδv : (δ : ℤ) = (q : ℤ) ^ 3 - ε := by
    have h : ((δ : ℤ) : ℂ) = ((deg A + σ : ℤ) : ℂ) := by
      push_cast
      rw [← h1 A T.core.hA]
      exact hδ
    rw [Int.cast_inj.mp h, hdA, hσε]
    ring
  refine ⟨⟨hσε, hτ1, hκε, hρε⟩, ⟨hdA, hdB, hdD, ?_, fun j hj => ?_, fun r hr e' => ?_,
    fun I hI => by rw [hψd I hI, hΔv], hΔv⟩, ?_, S.x_values hp1 hε hΦ1 hσε hτ1 hκε hρε hV6,
    S.section_values hε hσε hτ1 hκε⟩
  · rw [hdω, hdB, hτ1]
    ring
  · have h : ((deg (χ j) : ℤ) : ℂ) = ((δ : ℤ) : ℂ) := by
      rw [← h1 _ (T.core.hχB j hj), hdχ j hj]
      push_cast
      rfl
    rw [Int.cast_inj.mp h, hδv]
  · rw [(hdegPQ r hr e').1, (hdegPQ r hr e').2, hdB, hdD]
    exact ⟨rfl, rfl⟩
  · have hm2 : 2 ≤ m := by
      have h₁ := T.hm
      have h₂ := T.hM
      omega
    rw [hmul, hdA, hdB, hdD, hτ1, hδv, hΔv, multiset_degrees,
      show m - 2 + 1 = m - 1 by omega,
      show (q : ℤ) ^ 2 + ε * q + 1 - 1 = q * (q + ε) by ring]

end SectionTable

end CFSG.Wreathed.ConditionalGlobalDegrees
