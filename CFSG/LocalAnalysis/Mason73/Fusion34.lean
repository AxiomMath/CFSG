module

public import CFSG.LocalAnalysis.Mason73.Extremal
public import CFSG.LocalAnalysis.Mason73.Fusion33

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem exists_stabP_odd (p : Fin 2 × Fin 2 × Fin 2)
    (hp : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 1) :
    ∃ τ : Fin81.R0, ∀ π : Fin81.R0, π ∈ stabP p → π = 1 ∨ π = τ := by
  have key : ∀ q : Fin 2 × Fin 2 × Fin 2, (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 1 →
      ∃ τ ∈ (Finset.univ : Finset Fin81.R0), ∀ π ∈ (Finset.univ : Finset Fin81.R0),
        PatFix (π : Perm (Fin 4)) (pat q) → π = 1 ∨ π = τ := by
    decide
  obtain ⟨τ, -, hτ⟩ := key p hp
  exact ⟨τ, fun π hπ => hτ π (Finset.mem_univ _) hπ⟩

theorem card_le_eight_of_le_centralizer_omegaEl (hn : 3 ≤ n) {p : Fin 2 × Fin 2 × Fin 2}
    (hp : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 1) (E : Subgroup (L4Model n))
    (hE : ∀ x ∈ E, x * x = 1) (hEw : E ≤ centralizer {omegaEl hn p}) : Nat.card E ≤ 8 := by
  obtain ⟨τ, hτ⟩ := exists_stabP_odd p hp
  refine card_le_eight_of_piT_mem hn E hE (τ := τ) fun x hx => hτ _ ?_
  have := hEw hx
  rwa [centralizer_omegaEl hn, Subgroup.mem_comap] at this

theorem not_conj_tT_omegaEl_of_central (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hz : ∀ g : G, g * ι (zT (by omega)) = ι (zT (by omega)) * g) {p : Fin 2 × Fin 2 × Fin 2}
    (hp : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 1) (g : G) :
    g * ι (tT (by omega)) * g⁻¹ ≠ ι (omegaEl hn p) := by
  intro hg
  obtain ⟨μ, ⟨gμ, hgμ⟩, hμext, hmax⟩ := exists_extremal_conj hι hS (tT (n := n) (by omega))
  obtain ⟨E', hE', hE'μ, hE'card⟩ := exists_elementary_of_conj_extremal hι hS hμext hgμ
    (E1 (n := n) (by omega)) (E1_mul_self (by omega)) (E1_le_centralizer_tT (by omega))
  rw [card_E1 hn] at hE'card
  have ht2 := tT_mul_self (n := n) (by omega)
  have hμ2 : μ * μ = 1 := by
    apply hι
    rw [map_mul, ← hgμ, map_one]
    calc gμ * ι (tT (by omega)) * gμ⁻¹ * (gμ * ι (tT (by omega)) * gμ⁻¹)
        = gμ * ι (tT (by omega) * tT (by omega)) * gμ⁻¹ := by rw [map_mul]; group
      _ = 1 := by rw [ht2, map_one]; group
  have hw := hmax _ ⟨g, hg⟩
  rw [card_centralizer_omegaEl hn, card_stabP_of_odd p hp] at hw
  have hzconj : ∀ k : G, k⁻¹ * ι (zT (n := n) (by omega)) * k = ι (zT (by omega)) := fun k => by
    rw [mul_assoc, ← hz k, ← mul_assoc, inv_mul_cancel, one_mul]
  by_cases hμA : μ ∈ A n
  · obtain ⟨q, rfl⟩ := exists_eq_omegaEl hn hμA hμ2
    rcases Nat.mod_two_eq_zero_or_one (pat q 0 + pat q 1 + pat q 2 + pat q 3) with hq | hq
    · have key : ∀ q : Fin 2 × Fin 2 × Fin 2,
          (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 0 →
          q = (0, 0, 0) ∨ q = (0, 1, 1) ∨ q = (1, 0, 1) ∨ q = (1, 1, 0) := by
        decide
      have ht : ι (tT (n := n) (by omega)) = gμ⁻¹ * ι (omegaEl hn q) * gμ := by
        rw [← hgμ]; group
      rcases key q hq with rfl | rfl | rfl | rfl
      · rw [omegaEl_zero, map_one, show gμ⁻¹ * 1 * gμ = 1 by group] at ht
        exact tT_not_mem_A (n := n) (by omega)
          (by rw [hι (ht.trans (map_one ι).symm)]; exact one_mem _)
      · rw [← zT_eq_omegaEl, hzconj] at ht
        exact tT_not_mem_A (n := n) (by omega) (by rw [hι ht]; exact zT_mem_A _)
      · exact not_conj_tT_x1T_of_central hn hι hS hz gμ (by rw [hgμ, x1T_eq_omegaEl hn])
      · apply not_conj_tT_x1T_of_central hn hι hS hz ((ι (uT (by omega)))⁻¹ * gμ)
        rw [show (ι (uT (n := n) (by omega)))⁻¹ * gμ * ι (tT (by omega)) *
            ((ι (uT (by omega)))⁻¹ * gμ)⁻¹ =
            (ι (uT (by omega)))⁻¹ * (gμ * ι (tT (by omega)) * gμ⁻¹) * ι (uT (by omega)) by
            group,
          hgμ, ← y1T_eq_omegaEl hn, ← uT_conj_x1T (by omega), map_mul, map_mul, map_inv]
        group
    · have h8 := card_le_eight_of_le_centralizer_omegaEl hn hq E' hE' hE'μ
      omega
  · have h1 := card_centralizer_le_of_not_mem_A (by omega) hμA
    have h2 : 2 ^ (2 * n + 1) < 2 ^ (3 * n - 2) * 2 := by
      rw [← pow_succ]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end CFSG.LocalAnalysis.Mason73
