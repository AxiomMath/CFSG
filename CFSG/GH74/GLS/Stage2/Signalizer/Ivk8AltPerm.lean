module

public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Equiv Equiv.Perm Subgroup

section Elementary

private abbrev M2 : Type := Multiplicative (ZMod 2)

private theorem m2_sq (a : M2) : a * a = 1 := by
  revert a
  decide

private def act5 : (Fin 5 → M2) →* Perm (Fin 5 × M2) where
  toFun v :=
    { toFun := fun x => (x.1, v x.1 * x.2)
      invFun := fun x => (x.1, (v x.1)⁻¹ * x.2)
      left_inv := fun x => Prod.ext rfl (inv_mul_cancel_left _ _)
      right_inv := fun x => Prod.ext rfl (mul_inv_cancel_left _ _) }
  map_one' := by
    ext x <;> simp
  map_mul' u v := by
    ext x
    · simp
    · simp [mul_assoc]

private theorem act5_injective : Function.Injective act5 := by
  intro u v h
  funext i
  have := congrArg (fun σ : Perm (Fin 5 × M2) => (σ (i, 1)).2) h
  simpa [act5] using this

theorem exists_elementary_two_five :
    ∃ E : Subgroup (Perm (Fin 11)), CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ 5 := by
  obtain ⟨ι⟩ : Nonempty (Fin 5 × M2 ↪ Fin 11) := Function.Embedding.nonempty_of_card_le (by
    simp [Fintype.card_prod, ZMod.card])
  let θ : (Fin 5 → M2) →* Perm (Fin 11) := (Equiv.Perm.viaEmbeddingHom ι).comp act5
  have hθ : Function.Injective θ :=
    (Equiv.Perm.viaEmbeddingHom_injective ι).comp act5_injective
  refine ⟨θ.range, ?_, ?_⟩
  · refine CFSG.GH74.GLS.IVK.Lifted.isElementaryAbelian_two_of_sq_eq_one ?_
    rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have : v ^ 2 = 1 := by
      funext i
      simpa [sq] using m2_sq (v i)
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]

end Elementary

private theorem factorization_two_pow_mul_odd (e m : ℕ) (hm : ¬ 2 ∣ m) :
    (2 ^ e * m).factorization 2 = e := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem five_le_pRank_of_sylow_perm_eleven {X : Subgroup (Perm (Fin 11))}
    (h : 2 ^ 8 ∣ Nat.card ↥X) : 5 ≤ CFSG.pRank 2 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardG : Nat.card (Perm (Fin 11)) = 2 ^ 8 * 155925 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hX0 : Nat.card ↥X ≠ 0 := Nat.card_pos.ne'
  have hG0 : Nat.card (Perm (Fin 11)) ≠ 0 := Nat.card_pos.ne'
  have hvX : (Nat.card ↥X).factorization 2 = 8 := by
    have h1 : 8 ≤ (Nat.card ↥X).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hX0).1 h
    have h2 : (Nat.card ↥X).factorization 2 ≤ (Nat.card (Perm (Fin 11))).factorization 2 :=
      (Nat.factorization_le_iff_dvd hX0 hG0).2 (Subgroup.card_subgroup_dvd_card X) 2
    rw [hcardG, factorization_two_pow_mul_odd 8 155925 (by norm_num)] at h2
    omega
  have hvG : (Nat.card (Perm (Fin 11))).factorization 2 = 8 := by
    rw [hcardG, factorization_two_pow_mul_odd 8 155925 (by norm_num)]
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥X) := inferInstance
  have hQcard : Nat.card ↥(Q : Subgroup ↥X) = 2 ^ 8 := by
    rw [Sylow.card_eq_multiplicity, hvX]
  let P₀ : Subgroup (Perm (Fin 11)) := (Q : Subgroup ↥X).map X.subtype
  have hP₀card : Nat.card ↥P₀ = 2 ^ (Nat.card (Perm (Fin 11))).factorization 2 := by
    rw [hvG, ← hQcard]
    exact Subgroup.card_map_of_injective X.subtype_injective
  let Pg : Sylow 2 (Perm (Fin 11)) := Sylow.ofCard P₀ hP₀card
  have h1 := (CFSG.SectionRank.pRank_sylow Pg).2
  have h2 := (CFSG.SectionRank.pRank_sylow Q).2
  have h3 : CFSG.pRank 2 ↥(Q : Subgroup ↥X) = CFSG.pRank 2 ↥P₀ :=
    CFSG.GH74.GLS.IVK.Lifted.pRank_two_congr
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥X) X.subtype X.subtype_injective)
  have hPg : (Pg : Subgroup (Perm (Fin 11))) = P₀ := rfl
  rw [hPg] at h1
  obtain ⟨E, hE, hEcard⟩ := exists_elementary_two_five
  have h4 : 5 ≤ CFSG.pRank 2 (Perm (Fin 11)) :=
    CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian (by norm_num) hE hEcard
  rw [← h2, h3, h1]
  exact h4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
