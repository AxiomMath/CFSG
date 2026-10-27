module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Abstract

variable {X : Type*} [Group X] [Finite X]

theorem card_le_mul_of_decomp {S K Y : Subgroup X} (hYS : Y ≤ S)
    (hdec : ∀ r ∈ S, ∃ t ∈ S ⊓ K, ∃ c ∈ Y, t * c = r) :
    Nat.card S ≤ Nat.card (S ⊓ K : Subgroup X) * Nat.card Y := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun x : (S ⊓ K : Subgroup X) × Y => (⟨(x.1 : X) * (x.2 : X),
      S.mul_mem x.1.2.1 (hYS x.2.2)⟩ : S)) fun r => ?_
  obtain ⟨t, ht, c, hc, htc⟩ := hdec r r.2
  exact ⟨(⟨t, ht⟩, ⟨c, hc⟩), Subtype.ext htc⟩

theorem mul_card_le_of_inf_eq_bot {A B R : Subgroup X} (hA : A ≤ R) (hB : B ≤ R)
    (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card R := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun x : A × B => (⟨(x.1 : X) * (x.2 : X), R.mul_mem (hA x.1.2) (hB x.2.2)⟩ : R)) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : (a : X) * b = a' * b' := congrArg Subtype.val h
  have hmem : (a' : X)⁻¹ * a ∈ A ⊓ B := by
    refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
    have he : (a' : X)⁻¹ * a = b' * (b : X)⁻¹ :=
      calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * (a * b) * (b : X)⁻¹ := by group
        _ = (a' : X)⁻¹ * (a' * b') * (b : X)⁻¹ := by rw [h1]
        _ = b' * (b : X)⁻¹ := by group
    rw [he]
    exact B.mul_mem b'.2 (B.inv_mem b.2)
  rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  rw [← hmem] at h1
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext (mul_left_cancel h1))

theorem exists_pow_eq_of_decomp {p : ℕ} (hp : p.Prime) {S K Y : Subgroup X} {z : X}
    (hzY : z ∈ Y) (hzp : orderOf z = p) [IsCyclic Y] (hYp : IsPGroup p Y)
    (hYcard : p < Nat.card Y) (hYS : Y ≤ S) (hexp : ∀ t ∈ S ⊓ K, t ^ p = 1)
    (hcomm : ∀ a ∈ S ⊓ K, ∀ c ∈ Y, Commute a c)
    (hdec : ∀ r ∈ S, ∃ t ∈ S ⊓ K, ∃ c ∈ Y, t * c = r) :
    ∃ N : ℕ, (∀ t ∈ S, t ^ N ∈ Subgroup.zpowers z) ∧ ∃ o ∈ S, o ^ N = z := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hYp
  have he2 : 2 ≤ e := by
    by_contra h
    have h' : e ≤ 1 := by omega
    interval_cases e
    · rw [he, pow_zero] at hYcard
      exact absurd hYcard (by have := hp.one_lt; omega)
    · rw [he, pow_one] at hYcard
      exact lt_irrefl p hYcard
  set N := p ^ (e - 1) with hN
  have hpN : p ∣ N := dvd_pow_self p (by omega)
  have hNp : N * p = Nat.card Y := by
    rw [he, hN, ← pow_succ]
    congr 1
    omega
  refine ⟨N, fun t ht => ?_, ?_⟩
  · obtain ⟨a, ha, c, hc, rfl⟩ := hdec t ht
    rw [(hcomm a ha c hc).mul_pow]
    have ha1 : a ^ N = 1 := by
      obtain ⟨m, hm⟩ := hpN
      rw [hm, pow_mul, hexp a ha, one_pow]
    rw [ha1, one_mul]
    have hcY : c ^ N ∈ Y := Y.pow_mem hc N
    have hcp : (c ^ N) ^ p = 1 := by
      rw [← pow_mul, hNp]
      have h2 : (⟨c, hc⟩ : Y) ^ Nat.card Y = 1 := pow_card_eq_one'
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
        congrArg (fun x : Y => (x : X)) h2
    by_cases h1 : c ^ N = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · exact mem_zpowers_of_orderOf_eq_of_isCyclic hcY hzY (by rw [orderOf_eq_prime hcp h1, hzp])
  · obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Y)
    have hyX : orderOf (y : X) = p ^ e := by rw [Subgroup.orderOf_coe, hy, he]
    have hNdvd : N ∣ orderOf (y : X) := by
      rw [hyX, hN]
      exact pow_dvd_pow p (by omega)
    have hyN : orderOf ((y : X) ^ N) = p := by
      rw [orderOf_pow_of_dvd (pow_pos hp.pos _).ne' hNdvd, hyX, Nat.pow_div (by omega) hp.pos]
      rw [show e - (e - 1) = 1 by omega, pow_one]
    have hyNY : (y : X) ^ N ∈ Y := Y.pow_mem y.2 N
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_orderOf_eq_of_isCyclic hzY hyNY (by rw [hzp, hyN]))
    refine ⟨(y : X) ^ j, hYS (Y.zpow_mem y.2 j), ?_⟩
    rw [← hj, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem eq_of_pow_mem_zpowers {p : ℕ} [Fact p.Prime] {Q T : Subgroup X} {z : X}
    (hQ : IsPGroup p Q) (hTQ : T ≤ Q) (hzp : orderOf z = p)
    (hQC : Q ⊓ Subgroup.centralizer ({z} : Set X) ≤ T) {N : ℕ}
    (hN : ∀ t ∈ T, t ^ N ∈ Subgroup.zpowers z) (ho : ∃ o ∈ T, o ^ N = z) : Q = T := by
  obtain ⟨o, hoT, hoz⟩ := ho
  refine eq_of_isPGroup_of_le_of_normalizer hQ hTQ fun g hgQ hgN => ?_
  have hgo : g * o * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hgN o).mp hoT
  have hgz : g * z * g⁻¹ ∈ Subgroup.zpowers z := by
    have h1 : g * z * g⁻¹ = (g * o * g⁻¹) ^ N := by rw [conj_pow, hoz]
    rw [h1]
    exact hN _ hgo
  have hgzN : g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set X) :=
    mem_normalizer_zpowers_of_mem_zpowers hgz
  obtain ⟨n, hn⟩ := hQ ⟨g, hgQ⟩
  have hgn : g ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact hQC ⟨hgQ, Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_mem_normalizer_zpowers_of_pow_prime_pow Fact.out hzp hgzN hgn).eq⟩

end Abstract

end CFSG.AGLEmbedding
