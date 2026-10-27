module

public import CFSG.LocalAnalysis.Mason73.Fusion34
public import CFSG.LocalAnalysis.Mason73.TableIII

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem mul_self_of_conj_eq {ι : L4Model n →* G} (hι : Function.Injective ι) {a b : L4Model n}
    (ha : a * a = 1) {g : G} (hg : g * ι a * g⁻¹ = ι b) : b * b = 1 := by
  apply hι
  rw [map_mul, ← hg, map_one]
  calc g * ι a * g⁻¹ * (g * ι a * g⁻¹) = g * ι (a * a) * g⁻¹ := by rw [map_mul]; group
    _ = 1 := by rw [ha, map_one]; group

theorem not_mem_A_of_conj_tT_of_central (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hz : ∀ g : G, g * ι (zT (by omega)) = ι (zT (by omega)) * g) {ν : L4Model n} {g : G}
    (hg : g * ι (tT (by omega)) * g⁻¹ = ι ν) : ν ∉ A n := by
  intro hνA
  have hzconj : ∀ k : G, k⁻¹ * ι (zT (n := n) (by omega)) * k = ι (zT (by omega)) := fun k => by
    rw [mul_assoc, ← hz k, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨q, rfl⟩ :=
    exists_eq_omegaEl hn hνA (mul_self_of_conj_eq hι (tT_mul_self (by omega)) hg)
  rcases Nat.mod_two_eq_zero_or_one (pat q 0 + pat q 1 + pat q 2 + pat q 3) with hq | hq
  · have key : ∀ q : Fin 2 × Fin 2 × Fin 2,
        (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 0 →
        q = (0, 0, 0) ∨ q = (0, 1, 1) ∨ q = (1, 0, 1) ∨ q = (1, 1, 0) := by
      decide
    have ht : ι (tT (n := n) (by omega)) = g⁻¹ * ι (omegaEl hn q) * g := by
      rw [← hg]; group
    rcases key q hq with rfl | rfl | rfl | rfl
    · rw [omegaEl_zero, map_one, show g⁻¹ * 1 * g = 1 by group] at ht
      exact tT_not_mem_A (n := n) (by omega)
        (by rw [hι (ht.trans (map_one ι).symm)]; exact one_mem _)
    · rw [← zT_eq_omegaEl, hzconj] at ht
      exact tT_not_mem_A (n := n) (by omega) (by rw [hι ht]; exact zT_mem_A _)
    · exact not_conj_tT_x1T_of_central hn hι hS hz g (by rw [hg, x1T_eq_omegaEl hn])
    · apply not_conj_tT_x1T_of_central hn hι hS hz ((ι (uT (by omega)))⁻¹ * g)
      rw [show (ι (uT (n := n) (by omega)))⁻¹ * g * ι (tT (by omega)) *
          ((ι (uT (by omega)))⁻¹ * g)⁻¹ =
          (ι (uT (by omega)))⁻¹ * (g * ι (tT (by omega)) * g⁻¹) * ι (uT (by omega)) by
          group,
        hg, ← y1T_eq_omegaEl hn, ← uT_conj_x1T (by omega), map_mul, map_mul, map_inv]
      group
  · exact not_conj_tT_omegaEl_of_central hn hι hS hz hq g hg

theorem card_centralizer_le_of_conj_eq_tT_of_central (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hz : ∀ g : G, g * ι (zT (by omega)) = ι (zT (by omega)) * g) {ν : L4Model n} {g : G}
    (hg : g * ι (tT (by omega)) * g⁻¹ = ι ν) :
    Nat.card (centralizer {ν}) ≤ 2 ^ (2 * n) := by
  have hνA := not_mem_A_of_conj_tT_of_central hn hι hS hz hg
  have hle : ∀ k, k ≤ n + 3 → 2 ^ k ≤ 2 ^ (2 * n) := fun k hk =>
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases piT_eq_of_mul_self (mul_self_of_conj_eq hι (tT_mul_self (by omega)) hg) with
    h | h | h | h | h | h
  · exact absurd (mem_A_iff.2 h) hνA
  · exact card_centralizer_le_of_piT_s23 (by omega) (Or.inl h)
  · exact card_centralizer_le_of_piT_s23 (by omega) (Or.inr h)
  · exact (card_centralizer_le_of_piT_zP (by omega) h).trans (hle _ le_rfl)
  · exact (card_centralizer_le_of_piT_tP (by omega) (Or.inl h)).trans (hle _ (by omega))
  · exact (card_centralizer_le_of_piT_tP (by omega) (Or.inr h)).trans (hle _ (by omega))

theorem not_conj_tT_of_piT_s23_of_central (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hz : ∀ g : G, g * ι (zT (by omega)) = ι (zT (by omega)) * g) {l : L4Model n}
    (hl2 : l * l = 1) (hπ : piT l = s23 ∨ piT l = s01) (g : G) :
    g * ι (tT (by omega)) * g⁻¹ ≠ ι l := by
  intro hg
  have hext : IsSylowOf 2 (ι.range ⊓ centralizer {ι l}) (centralizer {ι l}) := by
    refine GHarris.isSylowOf_of_card_le hS ⟨l, rfl⟩ fun g' hg' => ?_
    obtain ⟨ν, hν⟩ := hg'
    rw [← hν, card_range_inf_centralizer hι, card_range_inf_centralizer hι,
      card_centralizer_of_piT_s23 hn hl2 hπ]
    refine card_centralizer_le_of_conj_eq_tT_of_central hn hι hS hz (g := g'⁻¹ * g) ?_
    rw [hν, ← hg]
    group
  obtain ⟨E', hE', hE'l, hcard⟩ := exists_elementary_of_conj_extremal hι hS hext hg
    (E1 (n := n) (by omega)) (E1_mul_self (by omega)) (E1_le_centralizer_tT (by omega))
  rw [card_E1 hn] at hcard
  rcases hπ with h | h
  · have h8 := card_le_eight_of_le_centralizer hn (g := l) (by rw [h]) E' hE' hE'l
    omega
  · have h8 := card_le_eight_of_le_centralizer_s01 hn (g := l) (by rw [h]) E' hE' hE'l
    omega

end CFSG.LocalAnalysis.Mason73
