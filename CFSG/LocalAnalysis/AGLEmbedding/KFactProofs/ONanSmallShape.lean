module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem pow_eq_one_of_sylowSq (hp : p.Prime) (hK : SylowSq p K) (T : Sylow p K)
    (hT : ¬ IsCyclic (T : Subgroup K)) (t : K) (ht : ∃ n : ℕ, t ^ p ^ n = 1) : t ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact pow_eq_one_of_sylow_exp T (fun s hs => pow_eq_one_of_card_sq hp (hK T) hT s hs) t ht

theorem pow_eq_one_of_sylowCube (hp : p.Prime) (hK : SylowCube p K) (T : Sylow p K) (t : K)
    (ht : ∃ n : ℕ, t ^ p ^ n = 1) : t ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact pow_eq_one_of_sylow_exp T (hK T).2 t ht

theorem exists_noncomm_of_cube (hp : p.Prime) (hrk : Open.pRank p (⊤ : Subgroup K) ≤ 2)
    (T : Sylow p K) (hcard : Nat.card T = p ^ 3) (hexp : ∀ t ∈ (T : Subgroup K), t ^ p = 1) :
    ∃ a ∈ (T : Subgroup K), ∃ b ∈ (T : Subgroup K), a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hE : IsElemAbelian p (T : Subgroup K) :=
    ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, hexp⟩
  have := CFSG.SectionRank.le_pRank hp.one_lt (le_top : (T : Subgroup K) ≤ ⊤) hE hcard
  omega

theorem sylowCube_of_equiv {H : Type} [Group H] [Finite H] {m : ℕ} (hp : p.Prime) (e : K ≃* H)
    (hcard : Nat.card K = p ^ 3 * m) (hm : ¬ p ∣ m) (S : Sylow p H)
    (hS : ∀ s ∈ (S : Subgroup H), s ^ p = 1) : SylowCube p K := by
  have : Fact p.Prime := ⟨hp⟩
  intro T
  refine ⟨card_sylow_eq_pow_of_card_eq hcard hm T, fun t ht => ?_⟩
  have hp' : IsPGroup p (T : Subgroup K) := T.2
  obtain ⟨n, hn⟩ := hp'.exists_card_eq
  have hord : orderOf (⟨t, ht⟩ : (T : Subgroup K)) ∣ p ^ n := hn ▸ orderOf_dvd_natCard _
  have ht' : t ^ p ^ n = 1 := by
    have h1 := pow_orderOf_eq_one (⟨t, ht⟩ : (T : Subgroup K))
    obtain ⟨c, hc⟩ := hord
    have : (⟨t, ht⟩ : (T : Subgroup K)) ^ p ^ n = 1 := by
      rw [hc, pow_mul, h1, one_pow]
    simpa using congrArg Subtype.val this
  have h2 : (e t) ^ p = 1 :=
    pow_eq_one_of_sylow_exp S hS (e t) ⟨n, by rw [← map_pow, ht', map_one]⟩
  exact e.injective (by rw [map_pow, h2, map_one])

omit [Finite K] in
theorem card_center_of_cube (hp : p.Prime) (T : Sylow p K) (hcard : Nat.card T = p ^ 3)
    (hnc : ∃ a ∈ (T : Subgroup K), ∃ b ∈ (T : Subgroup K), a * b ≠ b * a) :
    Nat.card (Subgroup.center (T : Subgroup K)) = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow (G := (T : Subgroup K)) (p := p)
    (n := 3) (by simpa using hcard) (by norm_num)
  have hdvd : Nat.card (Subgroup.center (T : Subgroup K)) ∣ p ^ 3 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd ⊢
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  by_contra hk1
  have hk1' : k ≠ 1 := fun h => hk1 (by rw [h, pow_one])
  have hk2 : 2 ≤ k := by omega
  have hidx : (Subgroup.center (T : Subgroup K)).index ∣ p := by
    have h := Subgroup.index_mul_card (Subgroup.center (T : Subgroup K))
    rw [hk, hcard] at h
    obtain ⟨j, hj⟩ : ∃ j, 3 = k + j := ⟨3 - k, by omega⟩
    have hj' : (Subgroup.center (T : Subgroup K)).index = p ^ j := by
      have h' : (Subgroup.center (T : Subgroup K)).index * p ^ k = p ^ k * p ^ j := by
        rw [h, hj, pow_add]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos k) (by rw [h']; ring)
    rw [hj']
    have : j ≤ 1 := by omega
    interval_cases j
    · simp
    · simp
  have hcyc : IsCyclic ((T : Subgroup K) ⧸ Subgroup.center (T : Subgroup K)) := by
    apply isCyclic_of_card_dvd_prime (p := p)
    rwa [← Subgroup.index]
  have hcomm := isMulCommutative_of_isCyclic_quotient_center_self (T : Subgroup K)
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  exact hab (congrArg Subtype.val (hcomm.is_comm.comm (⟨a, ha⟩ : (T : Subgroup K)) ⟨b, hb⟩))

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
