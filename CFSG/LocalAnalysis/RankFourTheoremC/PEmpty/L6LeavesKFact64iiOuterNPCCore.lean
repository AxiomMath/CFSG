module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPCCyc
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPCSyl
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC

theorem exists_orderOf_eq_pow_of_mem_sylow {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    (S : Sylow p G) {x : G} (hx : x ∈ (S : Subgroup G)) : ∃ a : ℕ, orderOf x = p ^ a := by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
  have h1 : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨a, ha⟩

theorem orderOf_pow_torsion {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {g₀ : G} {a : ℕ}
    (ha : orderOf g₀ = p ^ a) (ha0 : 0 < a) : orderOf (g₀ ^ (p ^ (a - 1))) = p := by
  have hdvd : p ^ (a - 1) ∣ orderOf g₀ := by
    rw [ha]
    exact pow_dvd_pow p (by omega)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.out.ne_zero) hdvd, ha,
    Nat.pow_div (by omega) hp.out.pos]
  have : a - (a - 1) = 1 := by omega
  rw [this, pow_one]

theorem mem_zpowers_torsion {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {g₀ : G} {a : ℕ}
    (ha : orderOf g₀ = p ^ a) (ha0 : 0 < a) {x : G} (hx : x ∈ Subgroup.zpowers g₀)
    (hxp : x ^ p = 1) : x ∈ Subgroup.zpowers (g₀ ^ (p ^ (a - 1))) := by
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h1 : (g₀ ^ s) ^ p = g₀ ^ (s * p) := by
    rw [← zpow_natCast, ← zpow_mul]
  rw [h1] at hxp
  have h2 : ((p ^ a : ℕ) : ℤ) ∣ s * p := by
    have := orderOf_dvd_iff_zpow_eq_one.2 hxp
    rwa [ha] at this
  have hpa : ((p ^ a : ℕ) : ℤ) = (p : ℤ) ^ (a - 1) * (p : ℤ) := by
    push_cast
    rw [← pow_succ]
    congr 1
    omega
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h3 : (p : ℤ) ^ (a - 1) ∣ s := by
    rw [hpa] at h2
    exact (mul_dvd_mul_iff_right hp0).1 h2
  obtain ⟨s', rfl⟩ := h3
  refine Subgroup.mem_zpowers_iff.2 ⟨s', ?_⟩
  rw [← zpow_natCast, ← zpow_mul]
  push_cast
  ring_nf

theorem exists_centralizing_normalizing
    {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (Kn : Subgroup G) [Kn.Normal] (f : G) (hf : f ^ p = 1)
    (hG : ∀ g : G, ∃ k ∈ Kn, ∃ j : ℕ, g = k * f ^ j)
    (S : Sylow p G) (hfS : f ∈ (S : Subgroup G))
    {g₀ : G} (hg₀ : g₀ ∈ (S : Subgroup G) ⊓ Kn)
    (hgen : ∀ x ∈ (S : Subgroup G) ⊓ Kn, x ∈ Subgroup.zpowers g₀)
    (hmov : f * g₀ * f⁻¹ ≠ g₀)
    {y₀ : G} (hy₀N : ∀ z ∈ (S : Subgroup G) ⊓ Kn, y₀ * z * y₀⁻¹ ∈ (S : Subgroup G) ⊓ Kn)
    (hy₀N' : ∀ z ∈ (S : Subgroup G) ⊓ Kn, y₀⁻¹ * z * y₀ ∈ (S : Subgroup G) ⊓ Kn)
    {x : G} (hxP : x ∈ (S : Subgroup G) ⊓ Kn) (hxp : x ^ p = 1) (hyx : y₀ * x * y₀⁻¹ ≠ x) :
    ∃ k r : G, k ∈ Kn ∧ r ∈ Kn ∧ orderOf r = p ∧ f * k = k * f ∧ f * r = r * f ∧
      k * r * k⁻¹ ∈ Subgroup.zpowers r ∧ k * r * k⁻¹ ≠ r := by
  classical
  set P : Subgroup G := (S : Subgroup G) ⊓ Kn with hP
  obtain ⟨a, ha⟩ := exists_orderOf_eq_pow_of_mem_sylow S hg₀.1
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      have : g₀ = 1 := by rwa [pow_zero, orderOf_eq_one_iff] at ha
      subst this
      exact absurd (by simp) hmov
    · exact h
  set r₀ : G := g₀ ^ (p ^ (a - 1)) with hr₀
  have hr₀ord : orderOf r₀ = p := orderOf_pow_torsion ha ha0
  have hr₀p : r₀ ^ p = 1 := by
    have := pow_orderOf_eq_one r₀
    rwa [hr₀ord] at this
  have hr₀P : r₀ ∈ P := P.pow_mem hg₀ _
  have htors : ∀ z ∈ P, z ^ p = 1 → z ∈ Subgroup.zpowers r₀ := fun z hz hzp =>
    mem_zpowers_torsion ha ha0 (hgen z hz) hzp
  have hnorm : ∀ n : G, (∀ z ∈ P, n * z * n⁻¹ ∈ P) → n * r₀ * n⁻¹ ∈ Subgroup.zpowers r₀ := by
    intro n hn
    refine htors _ (hn r₀ hr₀P) ?_
    rw [conj_pow, hr₀p]
    simp
  have hSnorm : ∀ s ∈ (S : Subgroup G), ∀ z ∈ P, s * z * s⁻¹ ∈ P := by
    intro s hs z hz
    exact ⟨S.mul_mem (S.mul_mem hs hz.1) (S.inv_mem hs),
      Subgroup.Normal.conj_mem inferInstance z hz.2 s⟩
  have hScomm : ∀ s ∈ (S : Subgroup G), s * r₀ = r₀ * s := by
    intro s hs
    obtain ⟨c, hc⟩ := S.isPGroup' ⟨s, hs⟩
    have hsc : s ^ (p ^ c) = 1 := by simpa using congrArg Subtype.val hc
    refine commute_of_pow_prime_pow hr₀ord (hnorm s (hSnorm s hs)) (c := c) ?_
    rw [hsc, one_mul, mul_one]
  have hfr : f * r₀ = r₀ * f := hScomm f hfS
  have hy₀r : y₀ * r₀ * y₀⁻¹ ∈ Subgroup.zpowers r₀ := hnorm y₀ hy₀N
  have hy₀r' : y₀⁻¹ * r₀ * y₀ ∈ Subgroup.zpowers r₀ := by
    have := hnorm y₀⁻¹ (fun z hz => by simpa using hy₀N' z hz)
    simpa using this
  set D : Subgroup G := Subgroup.centralizer ({r₀} : Set G) with hD
  have hmemD : ∀ d : G, d ∈ D ↔ r₀ * d = d * r₀ := by
    intro d
    rw [hD, Subgroup.mem_centralizer_iff]
    simp
  have hSD : (S : Subgroup G) ≤ D := fun s hs => (hmemD s).2 (hScomm s hs).symm
  have hyD : ∀ s ∈ (S : Subgroup G), y₀ * s * y₀⁻¹ ∈ D := by
    intro s hs
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hy₀r'
    have h1 : s * r₀ ^ j = r₀ ^ j * s := Commute.zpow_right (hScomm s hs) j
    refine (hmemD _).2 ?_
    calc r₀ * (y₀ * s * y₀⁻¹) = y₀ * (y₀⁻¹ * r₀ * y₀) * s * y₀⁻¹ := by group
      _ = y₀ * (r₀ ^ j) * s * y₀⁻¹ := by rw [hj]
      _ = y₀ * (s * r₀ ^ j) * y₀⁻¹ := by rw [h1]; group
      _ = (y₀ * s * y₀⁻¹) * r₀ := by rw [hj]; group
  obtain ⟨d, hdD, hdn⟩ := exists_mem_normalizer_sylow S D hSD y₀ hyD
  have hunorm : ∀ s ∈ (S : Subgroup G), (d * y₀) * s * (d * y₀)⁻¹ ∈ (S : Subgroup G) :=
    fun s hs => (Subgroup.mem_normalizer_iff.1 hdn s).1 hs
  have hdcomm : ∀ i : ℤ, d * r₀ ^ i = r₀ ^ i * d := fun i =>
    Commute.zpow_right ((hmemD d).1 hdD).symm i
  have hu_act : ∀ z ∈ Subgroup.zpowers r₀, (d * y₀) * z * (d * y₀)⁻¹ = y₀ * z * y₀⁻¹ := by
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have h1 : y₀ * r₀ ^ i * y₀⁻¹ ∈ Subgroup.zpowers r₀ := by
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ hy₀r i
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 h1
    calc (d * y₀) * r₀ ^ i * (d * y₀)⁻¹ = d * (y₀ * r₀ ^ i * y₀⁻¹) * d⁻¹ := by group
      _ = y₀ * r₀ ^ i * y₀⁻¹ := by rw [← hl, hdcomm l]; group
  obtain ⟨k₀, hk₀K, j₀, hk₀⟩ := hG (d * y₀)
  have hf₂S : (d * y₀) * f * (d * y₀)⁻¹ ∈ (S : Subgroup G) := hunorm f hfS
  have hf₂k : (d * y₀) * f * (d * y₀)⁻¹ = k₀ * f * k₀⁻¹ := by
    rw [hk₀]
    group
  have htS : ((d * y₀) * f * (d * y₀)⁻¹) * f⁻¹ ∈ (S : Subgroup G) :=
    S.mul_mem hf₂S (S.inv_mem hfS)
  have htK : ((d * y₀) * f * (d * y₀)⁻¹) * f⁻¹ ∈ Kn := by
    rw [hf₂k]
    have : k₀ * f * k₀⁻¹ * f⁻¹ = k₀ * (f * k₀⁻¹ * f⁻¹) := by group
    rw [this]
    exact Kn.mul_mem hk₀K (Subgroup.Normal.conj_mem inferInstance _ (Kn.inv_mem hk₀K) f)
  have htP : ((d * y₀) * f * (d * y₀)⁻¹) * f⁻¹ ∈ P := ⟨htS, htK⟩
  have htf : ((((d * y₀) * f * (d * y₀)⁻¹) * f⁻¹) * f) ^ p = 1 := by
    rw [inv_mul_cancel_right, conj_pow, hf]
    group
  have hf_norm : f * g₀ * f⁻¹ ∈ P := hSnorm f hfS g₀ hg₀
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hgen _ hf_norm)
  obtain ⟨z, hz, hzf⟩ := exists_conj_eq_of_pow_eq_one hp2 ha hf hm.symm hmov
    (hgen _ htP) htf
  have hf₂z : (d * y₀) * f * (d * y₀)⁻¹ = z * f * z⁻¹ := by
    rw [hzf]
    group
  have hwf : (z⁻¹ * (d * y₀)) * f = f * (z⁻¹ * (d * y₀)) := by
    have h1 : (z⁻¹ * (d * y₀)) * f * (z⁻¹ * (d * y₀))⁻¹ = f := by
      calc (z⁻¹ * (d * y₀)) * f * (z⁻¹ * (d * y₀))⁻¹
          = z⁻¹ * ((d * y₀) * f * (d * y₀)⁻¹) * z := by group
        _ = z⁻¹ * (z * f * z⁻¹) * z := by rw [hf₂z]
        _ = f := by group
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hzcomm : ∀ b ∈ Subgroup.zpowers r₀, z * b = b * z := by
    intro b hb
    have hb' : b ∈ Subgroup.zpowers g₀ := Subgroup.zpowers_le.2 (hgen r₀ hr₀P) hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
    exact (Commute.zpow_zpow_self g₀ i l).eq
  have hw_act : (z⁻¹ * (d * y₀)) * r₀ * (z⁻¹ * (d * y₀))⁻¹ = y₀ * r₀ * y₀⁻¹ := by
    have h1 : (z⁻¹ * (d * y₀)) * r₀ * (z⁻¹ * (d * y₀))⁻¹
        = z⁻¹ * ((d * y₀) * r₀ * (d * y₀)⁻¹) * z := by group
    rw [h1, hu_act r₀ (Subgroup.mem_zpowers r₀)]
    have h2 := hzcomm _ hy₀r
    calc z⁻¹ * (y₀ * r₀ * y₀⁻¹) * z = z⁻¹ * ((y₀ * r₀ * y₀⁻¹) * z) := by group
      _ = z⁻¹ * (z * (y₀ * r₀ * y₀⁻¹)) := by rw [h2]
      _ = y₀ * r₀ * y₀⁻¹ := by group
  obtain ⟨k, hkK, j, hk⟩ := hG (z⁻¹ * (d * y₀))
  have hkr : k * r₀ * k⁻¹ = y₀ * r₀ * y₀⁻¹ := by
    have h1 : f ^ j * r₀ = r₀ * f ^ j := (Commute.pow_left hfr j).eq
    have hk' : k = (z⁻¹ * (d * y₀)) * (f ^ j)⁻¹ := eq_mul_inv_of_mul_eq hk.symm
    rw [← hw_act, hk']
    calc (z⁻¹ * (d * y₀)) * (f ^ j)⁻¹ * r₀ * ((z⁻¹ * (d * y₀)) * (f ^ j)⁻¹)⁻¹
        = (z⁻¹ * (d * y₀)) * ((f ^ j)⁻¹ * r₀ * f ^ j) * (z⁻¹ * (d * y₀))⁻¹ := by group
      _ = (z⁻¹ * (d * y₀)) * r₀ * (z⁻¹ * (d * y₀))⁻¹ := by
          have : (f ^ j)⁻¹ * r₀ * f ^ j = r₀ := by
            calc (f ^ j)⁻¹ * r₀ * f ^ j = (f ^ j)⁻¹ * (r₀ * f ^ j) := by group
              _ = (f ^ j)⁻¹ * (f ^ j * r₀) := by rw [h1]
              _ = r₀ := by group
          rw [this]
  have hfk : f * k = k * f := by
    have h1 := hwf
    rw [hk] at h1
    have h2 : k * f * f ^ j = f * k * f ^ j := by
      calc k * f * f ^ j = k * (f ^ j * f) := by group
        _ = (k * f ^ j) * f := by rw [mul_assoc]
        _ = f * (k * f ^ j) := h1
        _ = f * k * f ^ j := by rw [mul_assoc]
    exact (mul_right_cancel h2).symm
  refine ⟨k, r₀, hkK, hr₀P.2, hr₀ord, hfk, hfr, ?_, ?_⟩
  · rw [hkr]
    exact hy₀r
  · rw [hkr]
    intro h
    apply hyx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (htors x hxP hxp)
    rw [← hi, ← conj_zpow, h]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC
