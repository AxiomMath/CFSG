module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Survivors
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Embed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Irred

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module CFSG.GroupTheory.GL52

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem card_dvd_G52(hV : finrank (ZMod 2) V ≤ 5) (Y : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Nat.card Y ∣ 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by
  have hinj := embG52_injective hV
  have := Subgroup.card_subgroup_dvd_card (Y.map (embG52 hV))
  rw [Subgroup.card_map_of_injective hinj, card_G52] at this
  exact this

theorem threePrime_map(hV : finrank (ZMod 2) V ≤ 5) {Y : Subgroup (V ≃ₗ[ZMod 2] V)}
    (h3 : ¬ 3 ∣ Nat.card Y) : ¬ 3 ∣ Nat.card (Y.map (embG52 hV)) := by
  rwa [Subgroup.card_map_of_injective (embG52_injective hV)]

theorem primes_of_pow_mul{N a r : ℕ} (hN : N = 2 ^ a * r) (hr : r.Prime) :
    ∀ q, q.Prime → q ∣ N → q = 2 ∨ q = r := by
  intro q hq hqN
  rw [hN] at hqN
  rcases (Nat.Prime.dvd_mul hq).1 hqN with h | h
  · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h)
  · right; exact (Nat.prime_dvd_prime_iff_eq hq hr).1 h

theorem irr_dvd_of_twoPrime [Nontrivial V] (hV : finrank (ZMod 2) V ≤ 5)
    {Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hY : Irreducible' Y) {a r M : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hcard : Nat.card Y = 2 ^ a * r) (hrG : ¬ r ^ 2 ∣ 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31)
    (hS : ∀ Q : Sylow r (GL (Fin 5) (ZMod 2)), Nat.card Q = r)
    (hN : ∀ Q : Sylow r (GL (Fin 5) (ZMod 2)),
      Nat.card (Subgroup.normalizer (Q : Set (GL (Fin 5) (ZMod 2)))) = M) :
    Nat.card Y ∣ M := by
  have hrY : r ∣ Nat.card Y := ⟨2 ^ a, by rw [hcard]; ring⟩
  have hrY2 : ¬ r ^ 2 ∣ Nat.card Y := fun h => hrG (h.trans (card_dvd_G52 hV Y))
  obtain ⟨P, -, hP, hnorm⟩ := exists_normal_prime_of_irreducible hY (Fact.out : r.Prime) hr2 hrY
    hrY2 (primes_of_pow_mul hcard (Fact.out : r.Prime))
  exact card_dvd_of_normal_prime hV hS hN hP hnorm

theorem irr_not_twoPower [Nontrivial V] (h2 : 2 ≤ finrank (ZMod 2) V)
    {Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hY : Irreducible' Y) {a : ℕ} (hcard : Nat.card Y = 2 ^ a) :
    False := by
  have hp : IsPGroup 2 Y := IsPGroup.of_card hcard
  have hbot := eq_bot_of_irreducible hY Y
    (fun g hg a ha => Y.mul_mem (Y.mul_mem hg ha) (Y.inv_mem hg)) hp
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hrank : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) = 1 := finrank_span_singleton hv
  have hle : Y ≤ stab (Submodule.span (ZMod 2) {v}) := by
    rw [hbot]; exact bot_le
  rcases hY _ hle with h | h
  · apply hv
    have : v ∈ Submodule.span (ZMod 2) {v} := Submodule.mem_span_singleton_self v
    rw [h] at this
    simpa using this
  · rw [h, finrank_top] at hrank
    omega

@[expose] def irrOrders : Finset ℕ := {5, 7, 10, 14, 20, 31, 155, 4960, 8680, 158720}

theorem irr_orders[Nontrivial V] (hV : finrank (ZMod 2) V ≤ 5) (h2 : 2 ≤ finrank (ZMod 2) V)
    {Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hY : Irreducible' Y) (h3 : ¬ 3 ∣ Nat.card Y) :
    Nat.card Y ∈ irrOrders := by
  have hmem := orders_of_threePrime _ (threePrime_map hV h3)
  rw [Subgroup.card_map_of_injective (embG52_injective hV)] at hmem
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have kill5 : ∀ a, Nat.card Y = 2 ^ a * 5 → ¬ (2 ^ a * 5 ∣ 60) → False := fun a hc hd =>
    hd (hc ▸ irr_dvd_of_twoPrime hV hY (by norm_num) hc (by norm_num) syl5_card_sylow
      (fun P => (syl5_structure P).2.2))
  have kill7 : ∀ a, Nat.card Y = 2 ^ a * 7 → ¬ (2 ^ a * 7 ∣ 126) → False := fun a hc hd =>
    hd (hc ▸ irr_dvd_of_twoPrime hV hY (by norm_num) hc (by norm_num) syl7_card_sylow
      (fun P => (syl7_structure P).1))
  have kill31 : ∀ a, Nat.card Y = 2 ^ a * 31 → ¬ (2 ^ a * 31 ∣ 155) → False := fun a hc hd =>
    hd (hc ▸ irr_dvd_of_twoPrime hV hY (by norm_num) hc (by norm_num) syl31_card_sylow
      (fun P => (syl31_structure P).1))
  have pow2 : ∀ a, Nat.card Y = 2 ^ a → False := fun a hc => irr_not_twoPower h2 hY hc
  simp only [survivorOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
  simp only [irrOrders, Finset.mem_insert, Finset.mem_singleton]
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (pow2 0 (by simpa using h)).elim
  · exact (pow2 1 (by simpa using h)).elim
  · exact (pow2 2 (by simpa using h)).elim
  · tauto
  · tauto
  · exact (pow2 3 (by simpa using h)).elim
  · tauto
  · tauto
  · exact (pow2 4 (by simpa using h)).elim
  · tauto
  · tauto
  · exact (pow2 5 (by simpa using h)).elim
  · exact (kill7 3 (by simpa using h) (by norm_num)).elim
  · exact (pow2 6 (by simpa using h)).elim
  · exact (kill5 4 (by simpa using h) (by norm_num)).elim
  · exact (kill7 4 (by simpa using h) (by norm_num)).elim
  · exact (pow2 7 (by simpa using h)).elim
  · tauto
  · exact (kill5 5 (by simpa using h) (by norm_num)).elim
  · exact (pow2 8 (by simpa using h)).elim
  · exact (kill5 6 (by simpa using h) (by norm_num)).elim
  · exact (kill7 6 (by simpa using h) (by norm_num)).elim
  · exact (pow2 9 (by simpa using h)).elim
  · exact (kill7 7 (by simpa using h) (by norm_num)).elim
  · exact (kill31 5 (by simpa using h) (by norm_num)).elim
  · exact (pow2 10 (by simpa using h)).elim
  · exact (kill5 8 (by simpa using h) (by norm_num)).elim
  · exact (kill5 9 (by simpa using h) (by norm_num)).elim
  · exact (kill7 9 (by simpa using h) (by norm_num)).elim
  · tauto
  · exact (kill5 10 (by simpa using h) (by norm_num)).elim
  · exact (kill7 10 (by simpa using h) (by norm_num)).elim
  · tauto
  · exact (kill31 10 (by simpa using h) (by norm_num)).elim
  · tauto

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
