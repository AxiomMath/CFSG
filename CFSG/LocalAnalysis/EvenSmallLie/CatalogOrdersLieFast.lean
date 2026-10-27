module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.Open

@[expose] def lieSearchB (ps : List ℕ) (N L : ℕ) (C : StatedLieTag → ℕ → ℕ → ℕ → Bool) : Bool :=
  Nat.ble (2 ^ L) N && Nat.blt N (2 ^ (L + 1)) &&
  ps.all fun p =>
    Nat.blt 1 p &&
    (List.range L).all fun f =>
      !(N % p ^ (f + 1) == 0) || searchTags.all fun t =>
        (List.range (L + 2)).all fun n =>
          !(decide (lieMin t ≤ n) && lieAdm t p (f + 1) && Nat.ble ((f + 1) * lieExp t n) L &&
              N % ((p ^ (f + 1)) ^ lieExp t n) == 0 && N % lieOrd t n (p ^ (f + 1)) == 0) ||
            C t n (p ^ (f + 1)) (lieOrd t n (p ^ (f + 1)))

theorem lieSearch_of_lieSearchB {ps : List ℕ} {N L : ℕ} {C : StatedLieTag → ℕ → ℕ → ℕ → Bool}
    (h : lieSearchB ps N L C = true) : lieSearch ps N C = true := by
  unfold lieSearchB at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hlo, hhi⟩, h⟩ := h
  have hN : N ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (Nat.two_pow_pos L) hlo)
  have hL : Nat.log 2 N = L := Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
  unfold lieSearch
  simp only [List.all_eq_true, List.mem_range]
  rw [hL]
  intro p hp f hf t ht n hn
  obtain ⟨hp1, hpf⟩ := h p hp
  have hff := hpf f hf
  by_cases hdiv : (N % p ^ (f + 1) == 0) = true
  swap
  · by_cases hmin : lieMin t ≤ n
    · have he := one_le_lieExp ht hmin
      have hc : (N % ((p ^ (f + 1)) ^ lieExp t n) == 0) = false :=
        Bool.eq_false_iff.mpr fun h0 => hdiv (beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd
          ((dvd_pow_self _ (by omega)).trans (Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h0)))))
      simp [hc]
    · simp [hmin]
  rw [hdiv, Bool.not_true, Bool.false_or] at hff
  simp only [List.all_eq_true, List.mem_range] at hff
  have key := hff t ht n hn
  by_cases hc : (N % ((p ^ (f + 1)) ^ lieExp t n) == 0) = true
  · have hd : (p ^ (f + 1)) ^ lieExp t n ∣ N :=
      Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hc)
    have hle : (f + 1) * lieExp t n ≤ L := by
      rw [← pow_mul] at hd
      rw [← hL]
      exact le_log_of_pow_dvd hN hp1 hd
    have hg : Nat.ble ((f + 1) * lieExp t n) L = true := Nat.ble_eq.mpr hle
    rw [hg, Bool.and_true] at key
    exact key
  · rw [Bool.not_eq_true] at hc
    simp [hc]

end CFSG.EvenSmallLie.CatalogOrders

end
