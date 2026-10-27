module

public import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne

universe u v

def normal_complement_semidirect_equiv
    {F : Type u} [Group F] (Q H : Subgroup F) [Q.Normal]
    (hcompl : Q.IsComplement' H) :
    Q ⋊[(Q.normalizerMonoidHom).comp
      (Subgroup.inclusion (Q.normalizer_eq_top ▸ le_top))] H ≃* F :=
  SemidirectProduct.mulEquivSubgroup hcompl

theorem normal_complement_semidirect_equiv_apply
    {F : Type u} [Group F] (Q H : Subgroup F) [Q.Normal]
    (hcompl : Q.IsComplement' H)
    (x : Q ⋊[(Q.normalizerMonoidHom).comp
      (Subgroup.inclusion (Q.normalizer_eq_top ▸ le_top))] H) :
    normal_complement_semidirect_equiv Q H hcompl x = (x.left : F) * x.right :=
  SemidirectProduct.mulEquivSubgroup_apply hcompl x

theorem regular_elementary_degree
    {F : Type u} [Group F] [Finite F]
    {Λ : Type v} [MulAction F Λ] [Finite Λ]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (Q : Subgroup F) [IsElementaryAbelian ℓ Q]
    (hregular : ∀ x y : Λ, ∃! q : Q, q • x = y)
    (a : Λ) (hdegree : 2 ≤ Nat.card Λ) :
    ∃ n : ℕ, 0 < n ∧ Nat.card Λ = Nat.card Q ∧ Nat.card Λ = ℓ ^ n := by
  have hbij : Function.Bijective (fun q : Q => q • a) :=
    (Function.bijective_iff_existsUnique _).mpr (hregular a)
  have hcard : Nat.card Λ = Nat.card Q :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  let : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup ℓ Q).exists_card_eq
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    rw [hnzero, pow_zero] at hn
    omega
  exact ⟨n, hnpos, hcard, hcard.trans hn⟩

theorem regular_elementary_degree_is_prime_power
    {F : Type u} [Group F] [Finite F]
    {Λ : Type v} [MulAction F Λ] [Finite Λ]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (Q : Subgroup F) [IsElementaryAbelian ℓ Q]
    (hregular : ∀ x y : Λ, ∃! q : Q, q • x = y)
    (a : Λ) (hdegree : 2 ≤ Nat.card Λ) :
    IsPrimePow (Nat.card Λ) := by
  obtain ⟨n, hn, _, hcard⟩ := regular_elementary_degree ℓ hℓ Q hregular a hdegree
  exact (isPrimePow_nat_iff _).mpr ⟨ℓ, n, hℓ, hn, hcard.symm⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne
