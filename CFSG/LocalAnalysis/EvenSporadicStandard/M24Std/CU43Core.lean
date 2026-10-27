module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Count
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup

section Basic

variable {Y : Type*} [Group Y]

theorem eq_one_of_sq_of_mem_odd {O : Subgroup Y} (hO : Odd (Nat.card O)) {a : Y}
    (ha : a * a = 1) (haO : a ∈ O) : a = 1 := by
  have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ha)
  have h2 : orderOf a ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨a, haO⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at h2
    exact absurd (even_iff_two_dvd.2 h2) (Nat.not_even_iff_odd.2 hO)

theorem exists_pow_involution {S₀ : Subgroup Y} (hS₀ : IsPGroup 2 S₀) {g : Y} (hg : g ∈ S₀)
    (hg1 : g ≠ 1) : ∃ k : ℕ, g ^ k * g ^ k = 1 ∧ g ^ k ≠ 1 := by
  obtain ⟨n, hn⟩ := hS₀ ⟨g, hg⟩
  have hn' : g ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn')
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hg1 (orderOf_eq_one_iff.1 (by simpa using hj))
  refine ⟨2 ^ (j - 1), ?_, ?_⟩
  · rw [← pow_add]
    have : 2 ^ (j - 1) + 2 ^ (j - 1) = 2 ^ j := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    rw [this, ← hj]
    exact pow_orderOf_eq_one g
  · apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [hj]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem card_map_mk_of_sq [Finite Y] (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    {D : Subgroup Y} (hD : ∀ a ∈ D, a * a = 1) :
    Nat.card (D.map (QuotientGroup.mk' O)) = Nat.card D := by
  have h := CResH4.natCard_map_mul_natCard_inf_ker (QuotientGroup.mk' O) D
  have hbot : D ⊓ (QuotientGroup.mk' O).ker = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [mem_bot]
    obtain ⟨haD, haK⟩ := mem_inf.1 ha
    rw [QuotientGroup.ker_mk'] at haK
    exact eq_one_of_sq_of_mem_odd hO (hD a haD) haK
  rw [hbot, Subgroup.card_bot, mul_one] at h
  exact h

end Basic

structure CoreHyp {Y : Type*} [Group Y] (O : Subgroup Y) [O.Normal] (E : Subgroup (Y ⧸ O))
    [E.Normal] (fx : Y → ℕ) (u : Y) : Prop where
  odd : Odd (Nat.card O)
  index : E.index = 2
  conj : ∀ s s' : Y ⧸ O, s ∈ E → s' ∈ E → s * s = 1 → s' * s' = 1 → s ≠ 1 → s' ≠ 1 →
    ∃ c ∈ E, s' = c * s * c⁻¹
  rank : ∀ B : Subgroup (Y ⧸ O), B ≤ E → (∀ a ∈ B, a * a = 1) → Nat.card B ≤ 16
  noncentral : ∀ d : Y ⧸ O, d ∉ E → d * d = 1 → ∀ S : Subgroup (Y ⧸ O), ¬ 2 ∣ S.index →
    ¬ S ≤ centralizer ({d} : Set (Y ⧸ O))
  fx_conj : ∀ s y : Y, fx (s * y * s⁻¹) = fx y
  fx_pow : ∀ (y : Y) (k : ℕ), fx y ≤ fx (y ^ k)
  fx_mul : ∀ y y' : Y, fx y * fx y' ≤ 4096 * fx (y * y')
  u_sq : u * u = 1
  u_ne : u ≠ 1
  u_mem : QuotientGroup.mk' O u ∈ E
  fx_u : fx u ≤ 64

namespace CoreHyp

variable {Y : Type*} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal] {E : Subgroup (Y ⧸ O)}
  [E.Normal] {fx : Y → ℕ} {u : Y}

omit [Finite Y] in
theorem eq_one_of_map (h : CoreHyp O E fx u) {a : Y} (ha : a * a = 1)
    (h1 : QuotientGroup.mk' O a = 1) : a = 1 :=
  eq_one_of_sq_of_mem_odd h.odd ha ((QuotientGroup.eq_one_iff a).1 h1)

theorem card_le_thirtytwo (h : CoreHyp O E fx u) {D : Subgroup Y} (hD : ∀ a ∈ D, a * a = 1) :
    Nat.card D ≤ 32 := by
  set B := D.map (QuotientGroup.mk' O) with hB
  have hBsq : ∀ b ∈ B, b * b = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hD a ha, map_one]
  have h1 := h.rank (E ⊓ B) inf_le_left (fun a ha => hBsq a (mem_inf.1 ha).2)
  have h2 := Subgroup.relIndex_mul_card (H := E) (K := B)
  have h3 : E.relIndex B ∣ 2 := h.index ▸ Subgroup.relIndex_dvd_index_of_normal E B
  have h4 : E.relIndex B ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  have h5 := card_map_mk_of_sq O h.odd hD
  rw [← h5, ← h2]
  calc E.relIndex B * Nat.card ↥(E ⊓ B) ≤ 2 * 16 := Nat.mul_le_mul h4 h1
    _ = 32 := by norm_num

theorem fx_le_of_inner (h : CoreHyp O E fx u) {v : Y} (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hvE : QuotientGroup.mk' O v ∈ E) : fx v ≤ 64 := by
  have hv1' : QuotientGroup.mk' O v ≠ 1 := fun h' => hv1 (h.eq_one_of_map hv2 h')
  have hu1' : QuotientGroup.mk' O u ≠ 1 := fun h' => h.u_ne (h.eq_one_of_map h.u_sq h')
  have hv2' : QuotientGroup.mk' O v * QuotientGroup.mk' O v = 1 := by
    rw [← map_mul, hv2, map_one]
  have hu2' : QuotientGroup.mk' O u * QuotientGroup.mk' O u = 1 := by
    rw [← map_mul, h.u_sq, map_one]
  obtain ⟨c, hcE, hc⟩ := h.conj _ _ h.u_mem hvE hu2' hv2' hu1' hv1'
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  have hu'2 : (y * u * y⁻¹) * (y * u * y⁻¹) = 1 := by
    calc (y * u * y⁻¹) * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
      _ = 1 := by rw [h.u_sq]; group
  have hmk : QuotientGroup.mk' O (y * u * y⁻¹) = QuotientGroup.mk' O v := by
    rw [hc]
    simp [map_mul, map_inv]
  obtain ⟨g, hg⟩ := exists_conj_of_map_eq (QuotientGroup.mk' O)
    (by rw [QuotientGroup.ker_mk']; exact h.odd) hu'2 hv2 hmk
  rw [← hg, h.fx_conj, h.fx_conj]
  exact h.fx_u

theorem sylow_conditions (h : CoreHyp O E fx u) {S₀ : Subgroup Y} (hS₀ : IsPGroup 2 S₀)
    (hS₀odd : ¬ 2 ∣ S₀.index) :
    (∀ D : Subgroup Y, D ≤ S₀ → (∀ a ∈ D, a * a = 1) → Nat.card D ≤ 32) ∧
      (∀ D : Subgroup Y, D ≤ S₀ → (∀ a ∈ D, a * a = 1) → D ≠ ⊥ →
        ∃ d ∈ D, d ≠ 1 ∧ ∃ b : ℕ, fx d ≤ b ∧ Nat.card D * b < 4096) := by
  refine ⟨fun D _ hD2 => h.card_le_thirtytwo hD2, ?_⟩
  intro D hDS hD2 hDbot
  by_cases hA : ∃ d ∈ D, d ≠ 1 ∧ QuotientGroup.mk' O d ∈ E
  · obtain ⟨d, hdD, hd1, hdE⟩ := hA
    refine ⟨d, hdD, hd1, 64, h.fx_le_of_inner (hD2 d hdD) hd1 hdE, ?_⟩
    have := h.card_le_thirtytwo hD2
    calc Nat.card D * 64 ≤ 32 * 64 := Nat.mul_le_mul_right _ this
      _ < 4096 := by norm_num
  · push Not at hA
    obtain ⟨⟨d, hdD⟩, hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDbot
    have hd1 : d ≠ 1 := fun h1 => hd (Subtype.ext h1)
    have hd2 := hD2 d hdD
    have hdE : QuotientGroup.mk' O d ∉ E := hA d hdD hd1
    have hd2' : QuotientGroup.mk' O d * QuotientGroup.mk' O d = 1 := by
      rw [← map_mul, hd2, map_one]
    have hDle : D ≤ zpowers d := by
      intro a haD
      by_cases ha1 : a = 1
      · rw [ha1]
        exact one_mem _
      · have haE : QuotientGroup.mk' O a ∉ E := hA a haD ha1
        have hadE : QuotientGroup.mk' O (a * d) ∈ E := by
          rw [map_mul, Subgroup.mul_mem_iff_of_index_two h.index]
          exact iff_of_false haE hdE
        have had1 : a * d = 1 := by
          by_contra hne
          exact hA (a * d) (mul_mem haD hdD) hne hadE
        have : a = d := by
          have h1 : a = d⁻¹ := eq_inv_of_mul_eq_one_left had1
          rw [h1]
          exact inv_eq_of_mul_eq_one_right hd2
        rw [this]
        exact mem_zpowers d
    have hDcard : Nat.card D ≤ 2 := by
      have h1 := Subgroup.card_le_of_le hDle
      rwa [Nat.card_zpowers, orderOf_eq_prime (by rwa [sq]) hd1] at h1
    have hSodd : ¬ 2 ∣ (S₀.map (QuotientGroup.mk' O)).index := fun h2 =>
      hS₀odd (h2.trans (Subgroup.index_map_dvd S₀ (QuotientGroup.mk'_surjective O)))
    obtain ⟨_, ⟨s, hsS, rfl⟩, hsc⟩ := IsConcreteLE.not_le_iff_exists.1
      (h.noncentral _ hdE hd2' _ hSodd)
    have hsd : s * d ≠ d * s := fun h1 => hsc (mem_centralizer_singleton_iff.2 (by
      rw [← map_mul, ← map_mul, h1.symm]))
    set d' := s * d * s⁻¹ with hd'
    have hd'S : d' ∈ S₀ := mul_mem (mul_mem hsS (hDS hdD)) (inv_mem hsS)
    have hd'2 : d' * d' = 1 := by
      calc d' * d' = s * (d * d) * s⁻¹ := by simp only [hd']; group
        _ = 1 := by rw [hd2]; group
    have hd'ne : d' ≠ d := by
      intro h1
      apply hsd
      calc s * d = (s * d * s⁻¹) * s := by group
        _ = d * s := by rw [← hd', h1]
    have hd'E : QuotientGroup.mk' O d' ∉ E := by
      intro hmem
      apply hdE
      have := Normal.conj_mem inferInstance _ hmem (QuotientGroup.mk' O s⁻¹)
      have e : QuotientGroup.mk' O s⁻¹ * QuotientGroup.mk' O d' * (QuotientGroup.mk' O s⁻¹)⁻¹ =
          QuotientGroup.mk' O d := by
        simp only [hd', map_mul, map_inv]
        group
      rwa [e] at this
    have hg1 : d * d' ≠ 1 := by
      intro h1
      apply hd'ne
      have h2 : d' = d⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact inv_eq_of_mul_eq_one_right hd2
    have hgS : d * d' ∈ S₀ := mul_mem (hDS hdD) hd'S
    have hgE : QuotientGroup.mk' O (d * d') ∈ E := by
      rw [map_mul, Subgroup.mul_mem_iff_of_index_two h.index]
      exact iff_of_false hdE hd'E
    obtain ⟨k, hk2, hk1⟩ := exists_pow_involution hS₀ hgS hg1
    have hkE : QuotientGroup.mk' O ((d * d') ^ k) ∈ E := by
      rw [map_pow]
      exact pow_mem hgE k
    have hfxg : fx (d * d') ≤ 64 :=
      (h.fx_pow (d * d') k).trans (h.fx_le_of_inner hk2 hk1 hkE)
    have hfxd' : fx d' = fx d := h.fx_conj s d
    have hsq : fx d * fx d ≤ 4096 * 64 :=
      calc fx d * fx d = fx d * fx d' := by rw [hfxd']
        _ ≤ 4096 * fx (d * d') := h.fx_mul d d'
        _ ≤ 4096 * 64 := Nat.mul_le_mul_left _ hfxg
    have hfd : fx d ≤ 512 := by
      by_contra hlt
      push Not at hlt
      nlinarith
    refine ⟨d, hdD, hd1, 512, hfd, ?_⟩
    calc Nat.card D * 512 ≤ 2 * 512 := Nat.mul_le_mul_right _ hDcard
      _ < 4096 := by norm_num

end CoreHyp

end CFSG.EvenSporadicStandard.M24Std.CU43
