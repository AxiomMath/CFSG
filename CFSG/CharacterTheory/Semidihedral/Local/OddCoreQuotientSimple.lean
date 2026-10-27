module

public import CFSG.CharacterTheory.Semidihedral.Local.OddCoreQuotientSimpleSupport
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

universe u

theorem semidihedral_odd_core_quotient_simple_odd_index_subgroup {G : Type u} [Group G]
    [Finite G] (hG : ∀ U : Subgroup G, U.index ≠ 2) (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0) :
    let R := CFSG.pPrimeCore 2 G
    let H := G ⧸ R
    CFSG.pPrimeCore 2 H = ⊥ ∧
      ∃ L : Subgroup H,
        (L.Normal ∧ L ≠ ⊥ ∧ ∀ K : Subgroup H, K.Normal → K ≤ L → K = ⊥ ∨ K = L) ∧
        (∀ L' : Subgroup H,
          (L'.Normal ∧ L' ≠ ⊥ ∧ ∀ K : Subgroup H, K.Normal → K ≤ L' → K = ⊥ ∨ K = L') →
            L' = L) ∧
        IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ L.Characteristic ∧ Odd L.index ∧
        Subgroup.centralizer (L : Set H) = ⊥ ∧
        (∀ T : Sylow 2 L, Nonempty (SemidihedralGroup n ≃* T)) ∧
        Nat.card L ≤ Nat.card G ∧
        ∀ (X : Type u) [Group X] [Finite X] (K : Subgroup X), K ≠ ⊤ → Nonempty (G ≃* K) →
          Nat.card G < Nat.card X := by
  intro R H
  have hcoreH : CFSG.pPrimeCore 2 H = ⊥ := by
    have h := pPrimeCore_map_eq_of_coprime_ker 2 (QuotientGroup.mk' R)
      (QuotientGroup.mk'_surjective R)
      (by rw [QuotientGroup.ker_mk']; exact CFSG.pPrimeCore_coprime_card (p := 2) (G := G))
    rw [← h, QuotientGroup.map_mk'_self]
  have hH2 : ∀ U : Subgroup H, U.index ≠ 2 := fun U hU =>
    hG (U.comap (QuotientGroup.mk' R)) (by
      rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective R)]
      exact hU)
  have hRodd : Odd (Nat.card R) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))
  have hS0R : (S0 : Subgroup G) ⊓ R = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [Sylow.card_eq_multiplicity]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hRodd)
  have hinj : Function.Injective ((QuotientGroup.mk' R).comp (S0 : Subgroup G).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ R := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (x : G) ∈ (S0 : Subgroup G) ⊓ R := ⟨x.2, h1⟩
    rw [hS0R, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  have hrange : ((QuotientGroup.mk' R).comp (S0 : Subgroup G).subtype).range =
      (S0 : Subgroup G).map (QuotientGroup.mk' R) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardS : Nat.card ((S0 : Subgroup G).map (QuotientGroup.mk' R)) =
      2 ^ (Nat.card H).factorization 2 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Sylow.card_eq_multiplicity]
    congr 1
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup R,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (fun h => (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h)), add_zero]
  let SH : Sylow 2 H := Sylow.ofCard _ hcardS
  let fH : SemidihedralGroup n ≃* SH := f0.trans ((MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (hrange.trans (Sylow.coe_ofCard _ hcardS).symm)))
  have hL := unique_minimal_normal_of_semidihedral hH2 hn SH fH hcoreH
  obtain ⟨L, hLmin, huniq, hsimple, hnc, hchar, hodd, hC, hsyl⟩ := hL
  refine ⟨hcoreH, L, hLmin, huniq, hsimple, hnc, hchar, hodd, hC, hsyl, ?_, ?_⟩
  · calc Nat.card L ≤ Nat.card H := Subgroup.card_le_card_group L
      _ ≤ Nat.card G := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup R]
        exact Nat.le_mul_of_pos_right _ Nat.card_pos
  · intro X _ _ K hK hGK
    obtain ⟨e⟩ := hGK
    rw [Nat.card_congr e.toEquiv, ← Subgroup.card_top (G := X)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hK)

end CFSG.Semidihedral.Local
