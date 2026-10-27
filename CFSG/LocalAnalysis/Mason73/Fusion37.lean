module

public import CFSG.LocalAnalysis.Mason73.Fusion34c
public import CFSG.LocalAnalysis.Mason73.Fusion36

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem conj_zT_of_piT_tP (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤)
    (hzx : ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega)))
    (h36i : ((∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) ∧
        ∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (w1T hn)) ∨
      ((∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (zT (by omega))) ∧
        ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (w1T hn)))
    (h36ii : ∀ μ : L4Model n, μ * μ = 1 → piT μ = zP →
      ∃ g : G, g * ι μ * g⁻¹ = ι (zT (by omega)))
    {l : L4Model n} (hl2 : l * l = 1) (hπ : piT l = tP ∨ piT l = tzP)
    {E : Subgroup (L4Model n)} (hE : ∀ x ∈ E, x * x = 1) (hEl : E ≤ centralizer {l})
    (hEcard : Nat.card E = 16) (hl : ι l ∈ commutator G) :
    ∃ g : G, g * ι l * g⁻¹ = ι (zT (by omega)) := by
  have hw : ∀ g : G, g * ι l * g⁻¹ ≠ ι (w1T hn) := by
    intro g hg
    obtain ⟨E', hE', hE'w, hcard'⟩ :=
      exists_elementary_of_conj_extremal hι hS (isSylowOf_w1T hn hι hS) hg E hE hEl
    have h8 := card_le_eight_of_le_centralizer_w1T hn E' hE' hE'w
    omega
  by_contra hz
  push Not at hz
  have hl1 : l ≠ 1 := fun h => by
    rw [h, map_one] at hπ
    rcases hπ with hπ | hπ <;> exact absurd hπ (by decide)
  refine not_mem_commutator_of_not_conj_into hι hS index_Q1T
    (orderOf_eq_prime (by rw [pow_two]; exact hl2) hl1) ?_ hl
  rintro x ⟨q, hq, hqx⟩
  have hlq : x⁻¹ * ι l * x⁻¹⁻¹ = ι q := by rw [inv_inv, hqx]
  have hq2 := mul_self_of_conj_eq hι hl2 hlq
  have key : (∃ g : G, g * ι q * g⁻¹ = ι (zT (by omega))) ∨
      ∃ g : G, g * ι q * g⁻¹ = ι (w1T hn) := by
    have hu : ∀ ν : L4Model n, IsConj q ν →
        ((∃ g : G, g * ι ν * g⁻¹ = ι (zT (by omega))) ∨
          ∃ g : G, g * ι ν * g⁻¹ = ι (w1T hn)) →
        (∃ g : G, g * ι q * g⁻¹ = ι (zT (by omega))) ∨
          ∃ g : G, g * ι q * g⁻¹ = ι (w1T hn) := by
      intro ν hqν h
      rcases h with ⟨g, hg⟩ | ⟨g, hg⟩
      · exact Or.inl (exists_conj_of_isConj hqν hg)
      · exact Or.inr (exists_conj_of_isConj hqν hg)
    have huu : ((∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) ∨
        ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (w1T hn)) ∧
        ((∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (zT (by omega))) ∨
          ∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (w1T hn)) := by
      rcases h36i with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨Or.inl h1, Or.inr h2⟩
      · exact ⟨Or.inr h2, Or.inl h1⟩
    rcases piT_cases_of_mem_Q1T hq with h | h | h | h
    · exact conj_zT_or_w1T_of_conj_mem_A hn hzx (mem_A_iff.2 h) hq2
        (ne_one_of_conj_eq hι hl1 hlq) (g := 1) (by group)
    · rcases isConj_uT_or_uw1T hn hq2 (Or.inr h) with h' | h'
      · exact hu _ h' huu.1
      · exact hu _ h' huu.2
    · rcases isConj_uT_or_uw1T hn hq2 (Or.inl h) with h' | h'
      · exact hu _ h' huu.1
      · exact hu _ h' huu.2
    · exact Or.inl (h36ii q hq2 h)
  rcases key with ⟨g, hg⟩ | ⟨g, hg⟩
  · obtain ⟨g', hg'⟩ := exists_conj_trans hlq hg
    exact hz g' hg'
  · obtain ⟨g', hg'⟩ := exists_conj_trans hlq hg
    exact hw g' hg'

theorem commutator_eq_top [IsSimpleGroup G] (hn : 2 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    apply uT_mul_tT_ne (n := n) hn
    apply hι
    have hc : ⁅ι (uT (n := n) (by omega)), ι (tT (by omega))⁆ ∈ commutator G := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    rw [map_mul, map_mul]
    exact hc
  · exact h

theorem fusion38 [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S)
    (hc0 : ∀ μ : L4Model n, piT μ = zP →
      ∃ c ∈ A n, c ∈ centralizer {μ} ∧ c * c = zT (by omega))
    (hM3 : ∀ b e : L4Model n, b * b ∉ A n → e ∈ centralizer {b} → e * e = 1 → e ≠ 1 →
      e = zT (by omega) ∨ e = b * b ∨ e = b * b * zT (by omega))
    (hx1t : x1T (by omega) ∈
      ⁅centralizer {tT (n := n) (by omega)}, centralizer {tT (n := n) (by omega)}⁆)
    (hx1tx : x1T (by omega) ∈ ⁅centralizer {txT n}, centralizer {txT n}⁆)
    (hsqrt : ∀ μ : L4Model n, μ * μ = 1 → piT μ = zP → ∃ r : L4Model n, r * r = μ)
    (hE16 : ∀ μ : L4Model n, μ * μ = 1 → (piT μ = tP ∨ piT μ = tzP) →
      ∃ E : Subgroup (L4Model n), (∀ x ∈ E, x * x = 1) ∧ E ≤ centralizer {μ} ∧
        Nat.card E = 16)
    (hM7 : ∀ B : Subgroup (L4Model n), B ≤ centralizer {x1T (by omega)} →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → 2 ^ (2 * n - 1) ≤ Nat.card B → B ≤ A n)
    (hM8 : ∀ B : Subgroup (L4Model n), B ≤ centralizer {uT (by omega)} →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → 2 ^ (2 * n - 1) ≤ Nat.card B → w1T hn ∈ B) :
    (∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega))) ∧
    (((∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) ∧
        ∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (w1T hn)) ∨
      ((∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (zT (by omega))) ∧
        ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (w1T hn))) ∧
    (∀ μ : L4Model n, μ * μ = 1 → piT μ = zP →
      ∃ g : G, g * ι μ * g⁻¹ = ι (zT (by omega))) ∧
    (∃ g : G, g * ι (tT (by omega)) * g⁻¹ = ι (zT (by omega))) ∧
    (∃ g : G, g * ι (txT n) * g⁻¹ = ι (zT (by omega))) ∧
    ∀ g : G, g * ι (w1T hn) * g⁻¹ ≠ ι (zT (by omega)) := by
  have hS' : IsSylowOf 2 ι.range ⊤ := by
    rw [hS]
    exact GHarris.isSylowOf_top S
  have htop := commutator_eq_top (G := G) (by omega) hι
  have hzx := conj_x1T_zT hn hι S hS hc0 hM3 hx1t hx1tx
  obtain ⟨h36i, h36ii⟩ := lemma36 hn hι hS' hzx hsqrt hE16 hM7 hM8
    (htop ▸ Subgroup.mem_top _)
  obtain ⟨Ex, hEx, hExl, hExc⟩ := hE16 (txT n) (txT_mul_self (by omega)) (Or.inl rfl)
  exact ⟨hzx, h36i, h36ii,
    conj_zT_of_piT_tP hn hι hS' hzx h36i h36ii (tT_mul_self (by omega)) (Or.inl rfl)
      (E1_mul_self (by omega)) (E1_le_centralizer_tT (by omega)) (card_E1 hn)
      (htop ▸ Subgroup.mem_top _),
    conj_zT_of_piT_tP hn hι hS' hzx h36i h36ii (txT_mul_self (by omega)) (Or.inl rfl) hEx hExl
      hExc (htop ▸ Subgroup.mem_top _),
    not_conj_w1T_zT hn hι hS'⟩

end CFSG.LocalAnalysis.Mason73
