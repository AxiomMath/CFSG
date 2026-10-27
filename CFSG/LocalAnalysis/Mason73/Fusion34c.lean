module

public import CFSG.LocalAnalysis.Mason73.Fusion34b
public import CFSG.LocalAnalysis.Mason73.TransferQ
public import CFSG.LocalAnalysis.Mason73.Transfer

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem not_conj_tT_of_piT_zP_of_central (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hz : ∀ g : G, g * ι (zT (by omega)) = ι (zT (by omega)) * g)
    (hcard : ∀ μ : L4Model n, μ * μ = 1 → piT μ = zP →
      2 ^ (n + 3) ≤ Nat.card (centralizer {μ}))
    (hsq : ∀ μ c : L4Model n, μ * μ = 1 → piT μ = zP → c ∈ centralizer {μ} → c * c ≠ 1 →
      c * c * (c * c) = 1 → c * c = zT (by omega) ∨ c * c = μ ∨ c * c = μ * zT (by omega))
    {l : L4Model n} (hl2 : l * l = 1) (hπ : piT l = zP) (g : G) :
    g * ι (tT (by omega)) * g⁻¹ ≠ ι l := by
  intro hg
  have hzconj : ∀ k : G, k⁻¹ * ι (zT (n := n) (by omega)) * k = ι (zT (by omega)) := fun k => by
    rw [mul_assoc, ← hz k, ← mul_assoc, inv_mul_cancel, one_mul]
  have hext : IsSylowOf 2 (ι.range ⊓ centralizer {ι l}) (centralizer {ι l}) := by
    refine GHarris.isSylowOf_of_card_le hS ⟨l, rfl⟩ fun g' hg' => ?_
    obtain ⟨ν, hν⟩ := hg'
    rw [← hν, card_range_inf_centralizer hι, card_range_inf_centralizer hι]
    have hgν : g'⁻¹ * g * ι (tT (by omega)) * (g'⁻¹ * g)⁻¹ = ι ν := by
      rw [hν, ← hg]
      group
    have hνA := not_mem_A_of_conj_tT_of_central hn hι hS hz hgν
    have hν2 := mul_self_of_conj_eq hι (tT_mul_self (by omega)) hgν
    refine le_trans ?_ (hcard l hl2 hπ)
    rcases piT_eq_of_mul_self hν2 with h | h | h | h | h | h
    · exact absurd (mem_A_iff.2 h) hνA
    · exact absurd hgν (not_conj_tT_of_piT_s23_of_central hn hι hS hz hν2 (Or.inl h) _)
    · exact absurd hgν (not_conj_tT_of_piT_s23_of_central hn hι hS hz hν2 (Or.inr h) _)
    · exact card_centralizer_le_of_piT_zP (by omega) h
    · exact (card_centralizer_le_of_piT_tP (by omega) (Or.inl h)).trans
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    · exact (card_centralizer_le_of_piT_tP (by omega) (Or.inr h)).trans
        (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨k, hkt, hk⟩ := GHarris.exists_conj_extremal (S := ι.range) hS.isPGroup hext
    (u := ι (tT (by omega))) (h := g) (by rw [← hg]; group)
  have hca : ι (aT n) ∈ (ι.range ⊓ centralizer {ι (tT (by omega))} : Subgroup G) := by
    refine Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 (aT_mem_centralizer_tT (by omega))]
  obtain ⟨⟨b, hb⟩, hbc⟩ := Subgroup.mem_inf.1 (hk _ hca)
  have hbl : b ∈ centralizer {l} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hι
    rw [map_mul, map_mul, hb]
    exact Subgroup.mem_centralizer_singleton_iff.1 hbc
  have he : k⁻¹ * ι (x1T (by omega)) * k = ι (b * b) := by
    rw [map_mul, hb, ← aT_mul_aT hn, map_mul]
    group
  have hx2 : x1T (n := n) (by omega) * x1T (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_x1T (by omega)]
  have he' : k⁻¹ * ι (x1T (by omega)) * k⁻¹⁻¹ = ι (b * b) := by rw [inv_inv, he]
  have hb2 := mul_self_of_conj_eq hι hx2 he'
  have hx : ι (x1T (n := n) (by omega)) = k * ι (b * b) * k⁻¹ := by rw [← he]; group
  have hb1 : b * b ≠ 1 := by
    intro h
    rw [h, map_one, show k * 1 * k⁻¹ = 1 by group] at hx
    have h1 := orderOf_x1T (n := n) (by omega)
    rw [← orderOf_injective ι hι, hx, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have ht : ι (tT (n := n) (by omega)) = k * ι l * k⁻¹ := by rw [← hkt]; group
  rcases hsq l b hl2 hπ hbl hb1 hb2 with h | h | h
  ·
    apply x1T_ne_zT (n := n) (by omega)
    apply hι
    rw [hx, h, show k * ι (zT (n := n) (by omega)) * k⁻¹ = (k⁻¹)⁻¹ * ι (zT (by omega)) * k⁻¹ by
      group, hzconj]
  ·
    apply tT_not_mem_A (n := n) (by omega)
    rw [hι (ht.trans (h ▸ hx).symm)]
    exact x1T_mem_A _
  ·
    apply tT_not_mem_A (n := n) (by omega)
    have hxt : ι (x1T (n := n) (by omega)) = ι (tT (by omega) * zT (by omega)) := by
      rw [hx, h, map_mul, map_mul, ht, show k * ι l * k⁻¹ * ι (zT (n := n) (by omega)) =
        k * (ι l * (k⁻¹ * ι (zT (by omega)) * k)) * k⁻¹ by group, hzconj]
    have h' : tT (n := n) (by omega) = x1T (by omega) * (zT (by omega))⁻¹ := by
      rw [hι hxt]
      group
    rw [h']
    exact mul_mem (x1T_mem_A _) (inv_mem (zT_mem_A _))

theorem piT_cases_of_mem_Q1T {q : L4Model n} (hq : q ∈ Q1T n) :
    piT q = 1 ∨ piT q = s01 ∨ piT q = s23 ∨ piT q = zP := by
  rcases hq with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

theorem tT_not_mem_commutator_of_central (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hz : ∀ g : G, g * ι (zT (by omega)) = ι (zT (by omega)) * g)
    (hcard : ∀ μ : L4Model n, μ * μ = 1 → piT μ = zP →
      2 ^ (n + 3) ≤ Nat.card (centralizer {μ}))
    (hsq : ∀ μ c : L4Model n, μ * μ = 1 → piT μ = zP → c ∈ centralizer {μ} → c * c ≠ 1 →
      c * c * (c * c) = 1 → c * c = zT (by omega) ∨ c * c = μ ∨ c * c = μ * zT (by omega)) :
    ι (tT (by omega)) ∉ commutator G := by
  refine not_mem_commutator_of_not_conj_into hι hS index_Q1T (orderOf_tT (by omega)) ?_
  rintro x ⟨q, hq, hqx⟩
  have hgq : x⁻¹ * ι (tT (by omega)) * x⁻¹⁻¹ = ι q := by rw [inv_inv, hqx]
  have hq2 := mul_self_of_conj_eq hι (tT_mul_self (by omega)) hgq
  rcases piT_cases_of_mem_Q1T hq with h | h | h | h
  · exact not_mem_A_of_conj_tT_of_central hn hι hS hz hgq (mem_A_iff.2 h)
  · exact not_conj_tT_of_piT_s23_of_central hn hι hS hz hq2 (Or.inr h) _ hgq
  · exact not_conj_tT_of_piT_s23_of_central hn hι hS hz hq2 (Or.inl h) _ hgq
  · exact not_conj_tT_of_piT_zP_of_central hn hι hS hz hcard hsq hq2 h _ hgq

theorem tT_not_mem_commutator_centralizer (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hcard : ∀ μ : L4Model n, μ * μ = 1 → piT μ = zP →
      2 ^ (n + 3) ≤ Nat.card (centralizer {μ}))
    (hsq : ∀ μ c : L4Model n, μ * μ = 1 → piT μ = zP → c ∈ centralizer {μ} → c * c ≠ 1 →
      c * c * (c * c) = 1 → c * c = zT (by omega) ∨ c * c = μ ∨ c * c = μ * zT (by omega)) :
    restrictCentralizer ι (by omega) (tT (by omega)) ∉
      commutator (centralizer {ι (zT (n := n) (by omega))}) :=
  tT_not_mem_commutator_of_central hn (restrictCentralizer_injective hι (by omega))
    (isSylowOf_restrictCentralizer (by omega) hS)
    (fun c => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)) hcard hsq

end CFSG.LocalAnalysis.Mason73
