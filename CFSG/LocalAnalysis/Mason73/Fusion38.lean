module

public import CFSG.LocalAnalysis.Mason73.Fusion37
public import CFSG.LocalAnalysis.Mason73.Powers2

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem exists_mul_self_eq_of_piT_zP (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = zP) : ∃ r : L4Model n, r * r = μ := by
  have hsq : ∀ ν r : L4Model n, IsConj μ ν → r * r = ν → ∃ r' : L4Model n, r' * r' = μ := by
    intro ν r h hr
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    refine ⟨c⁻¹ * r * c, ?_⟩
    calc c⁻¹ * r * c * (c⁻¹ * r * c) = c⁻¹ * (r * r) * c := by group
      _ = μ := by rw [hr]; group
  rcases isConj_uvT_or_uvxyT hn h2 hπ with h | h
  · exact hsq _ _ h (tT_mul_uT_mul_self (by omega))
  · obtain ⟨r, -, hr⟩ := exists_mul_self_eq_uvxyT (n := n) (by omega)
    exact hsq _ r h hr

theorem exists_E16_le_centralizer_of_piT_tP (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = tP ∨ piT μ = tzP) :
    ∃ E : Subgroup (L4Model n), (∀ x ∈ E, x * x = 1) ∧ E ≤ centralizer {μ} ∧
      Nat.card E = 16 := by
  have hconj : ∀ ν : L4Model n, IsConj μ ν → ∀ E : Subgroup (L4Model n),
      (∀ x ∈ E, x * x = 1) → E ≤ centralizer {ν} → Nat.card E = 16 →
      ∃ E' : Subgroup (L4Model n), (∀ x ∈ E', x * x = 1) ∧ E' ≤ centralizer {μ} ∧
        Nat.card E' = 16 := by
    intro ν h E hE hEν hcard
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    set θ : L4Model n ≃* L4Model n := MulAut.conj c⁻¹ with hθ
    have hθμ : θ (c * μ * c⁻¹) = μ := by
      rw [hθ, MulAut.conj_apply]
      group
    refine ⟨E.map θ.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, hE x hx, map_one]
    · calc E.map θ.toMonoidHom ≤ (centralizer {c * μ * c⁻¹}).map θ.toMonoidHom :=
            Subgroup.map_mono hEν
        _ = centralizer {θ (c * μ * c⁻¹)} := (centralizer_mulEquiv_apply θ _).symm
        _ = centralizer {μ} := by rw [hθμ]
    · rw [Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective, hcard]
  rcases isConj_tT_or_txT hn h2 hπ with h | h
  · exact hconj _ h _ (E1_mul_self (by omega)) (E1_le_centralizer_tT (by omega)) (card_E1 hn)
  · exact hconj _ h _ (E1x_mul_self (by omega)) (E1x_le_centralizer_txT (by omega))
      (card_E1x hn)

theorem map_subtype_commutator (C : Subgroup G) : (commutator C).map C.subtype = ⁅C, C⁆ := by
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem lemma34 (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) :
    ι (tT (by omega)) ∉
      ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆ := by
  intro h
  rw [← map_subtype_commutator] at h
  obtain ⟨y, hy, hyt⟩ := h
  apply tT_not_mem_commutator_centralizer hn hι hS
    (fun _ h2 hπ => le_card_centralizer_of_piT_zP hn h2 hπ)
    (fun _ _ h2 hπ hc hc1 hc2 => mul_self_eq_zT_or_of_piT_zP hn h2 hπ hc hc1 hc2)
  have : y = restrictCentralizer ι (by omega) (tT (by omega)) := Subtype.ext hyt
  rwa [← this]

theorem lemma34_txT (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) :
    ι (txT n) ∉
      ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆ := by
  set ι' : L4Model n →* G := ι.comp (diagAut n).toMonoidHom with hι'def
  have hι' : Function.Injective ι' := hι.comp (diagAut n).injective
  have hS' : IsSylowOf 2 ι'.range ⊤ := by
    rw [hι'def, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective (diagAut n).toMonoidHom (diagAut n).surjective,
      ← MonoidHom.range_eq_map]
    exact hS
  have hz : ι' (zT (n := n) (by omega)) = ι (zT (by omega)) := by
    change ι (diagAut n (zT (by omega))) = _
    rw [diagAut_of_mem_A (zT_mem_A _)]
  have ht : ι' (tT (n := n) (by omega)) = ι (txT n) := by
    change ι (diagAut n (tT (by omega))) = _
    rw [diagAut_tT]
  have h := lemma34 hn hι' hS'
  rwa [ht, hz] at h

theorem fusionPattern [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S) :
    (∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega))) ∧
    (((∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) ∧
        ∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (w1T hn)) ∨
      ((∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (zT (by omega))) ∧
        ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (w1T hn))) ∧
    (∀ μ : L4Model n, μ * μ = 1 → piT μ = zP →
      ∃ g : G, g * ι μ * g⁻¹ = ι (zT (by omega))) ∧
    (∃ g : G, g * ι (tT (by omega)) * g⁻¹ = ι (zT (by omega))) ∧
    (∃ g : G, g * ι (txT n) * g⁻¹ = ι (zT (by omega))) ∧
    ∀ g : G, g * ι (w1T hn) * g⁻¹ ≠ ι (zT (by omega)) :=
  fusion38 hn hι S hS (fun _ hπ => exists_mem_A_mul_self_eq_zT_of_piT_zP hn hπ)
    (fun _ _ hb he he2 he1 => eq_of_mem_centralizer_of_mul_self_not_mem_A hn hb he he2 he1)
    (x1T_mem_commutator_centralizer_tT hn) (x1T_mem_commutator_centralizer_txT hn)
    (fun _ h2 hπ => exists_mul_self_eq_of_piT_zP hn h2 hπ)
    (fun _ h2 hπ => exists_E16_le_centralizer_of_piT_tP hn h2 hπ)
    (fun B hB hc h => le_A_of_comm_of_le_centralizer_x1T hn B hB hc h)
    (fun B hB hc h => w1T_mem_of_comm_of_le_centralizer_uT hn B hB hc h)

end CFSG.LocalAnalysis.Mason73
