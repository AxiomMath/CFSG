module

public import CFSG.FeitThompson.Foundations.NilpotentNormalizerCondition
public import CFSG.FeitThompson.Foundations.SylowNormalizerSelfNormalizing

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

theorem normal_of_natCard_eq_pow_factorization [Finite G] [Group.IsNilpotent G]
    {P : Subgroup G} (hP : Nat.card P = p ^ (Nat.card G).factorization p) : P.Normal := by
  rw [← normalizer_eq_top_iff]
  by_contra hN
  have h := Group.normalizerCondition_of_isNilpotent (G := G) _ (lt_top_iff_ne_top.mpr hN)
  rw [normalizer_normalizer_of_natCard_eq_pow_factorization (p := p) hP] at h
  exact absurd h (lt_irrefl _)

theorem characteristic_of_natCard_eq_pow_factorization [Finite G] [Group.IsNilpotent G]
    {P : Subgroup G} (hP : Nat.card P = p ^ (Nat.card G).factorization p) : P.Characteristic := by
  have hnormal : P.Normal := normal_of_natCard_eq_pow_factorization hP
  rw [characteristic_iff_map_eq]
  intro φ
  have : (P.map (φ : G →* G)).Normal := hnormal.map _ φ.surjective
  have hcard : Nat.card (P.map (φ : G →* G)) = p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective φ.injective, hP]
  obtain ⟨g, hg⟩ := exists_conj_smul_eq (p := p) hcard hP
  rwa [Subgroup.Normal.conj_smul_eq_self g (P.map (φ : G →* G))] at hg

theorem IsCentralSeries.normal_of_natCard_eq_pow_factorization [Finite G] {X : ℕ → Subgroup G}
    {r : ℕ} (hX : IsCentralSeries X r) {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) : P.Normal :=
  have : Group.IsNilpotent G := hX.isNilpotent
  _root_.CFSG.FeitThompson.normal_of_natCard_eq_pow_factorization hP

theorem IsCentralSeries.characteristic_of_natCard_eq_pow_factorization [Finite G]
    {X : ℕ → Subgroup G} {r : ℕ} (hX : IsCentralSeries X r) {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) : P.Characteristic :=
  have : Group.IsNilpotent G := hX.isNilpotent
  _root_.CFSG.FeitThompson.characteristic_of_natCard_eq_pow_factorization hP

theorem sylow_normal_of_isNilpotent [Finite G] [Group.IsNilpotent G] (P : Sylow p G) :
    (P : Subgroup G).Normal :=
  normal_of_natCard_eq_pow_factorization P.card_eq_multiplicity

theorem sylow_characteristic_of_isNilpotent [Finite G] [Group.IsNilpotent G] (P : Sylow p G) :
    (P : Subgroup G).Characteristic :=
  characteristic_of_natCard_eq_pow_factorization P.card_eq_multiplicity

end

end CFSG.FeitThompson
