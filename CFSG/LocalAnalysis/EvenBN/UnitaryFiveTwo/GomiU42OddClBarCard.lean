module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClBarDefs
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Module QuadraticMap CFSG.GroupTheory.WeirSylow

theorem u42ProdSq_cast (q m : ℕ) (hq : 1 ≤ q) :
    ((u42ProdSq q m : ℕ) : ℤ) = ∏ i ∈ Finset.Icc 1 m, (((q : ℤ) ^ 2) ^ i - 1) := by
  unfold u42ProdSq
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), ← pow_mul]
  push_cast
  rfl

variable {F : Type} [Field F] [Finite F] {W : Type} [AddCommGroup W] [Module F W]
  [FiniteDimensional F W]

theorem u42_card_O_odd {q m : ℕ} (hF : Nat.card F = q) (hodd : ringChar F ≠ 2)
    {Q : QuadraticForm F W} (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank F W = 2 * m + 1) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * u42Sp q m := by
  have h1 := natCard_orthogonalGroup_odd hodd hQ hdim
  rw [hF] at h1
  have hq : 1 ≤ q := hF ▸ Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have h2 := u42ProdSq_cast q m hq
  have h3 : ((2 * u42Sp q m : ℕ) : ℤ) =
      2 * (q : ℤ) ^ (m ^ 2) * ∏ i ∈ Finset.Icc 1 m, (((q : ℤ) ^ 2) ^ i - 1) := by
    unfold u42Sp
    push_cast
    rw [h2]
    ring
  exact_mod_cast h1.trans h3.symm

theorem u42_card_O_even {q m : ℕ} (hF : Nat.card F = q)
    {Q : QuadraticForm F W} (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank F W = 2 * (m + 1)) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = u42OEvenPlus q m ∨
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = u42OEvenMinus q m := by
  have hq : 1 ≤ q := hF ▸ Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have h2 := u42ProdSq_cast q m hq
  by_cases hp : IsPlusType Q
  · left
    have h1 := natCard_orthogonalGroup_of_type hQ hdim (ε := 1) (Or.inl ⟨rfl, hp⟩)
    rw [hF] at h1
    have h3 : ((u42OEvenPlus q m : ℕ) : ℤ) =
        2 * (q : ℤ) ^ (m * (m + 1)) * ((q : ℤ) ^ (m + 1) - 1) *
          ∏ i ∈ Finset.Icc 1 m, (((q : ℤ) ^ 2) ^ i - 1) := by
      unfold u42OEvenPlus
      push_cast [Nat.cast_sub (Nat.one_le_pow (m + 1) q (by omega))]
      rw [h2]
    exact_mod_cast h1.trans h3.symm
  · right
    have h1 := natCard_orthogonalGroup_of_type hQ hdim (ε := -1) (Or.inr ⟨rfl, hp⟩)
    rw [hF] at h1
    have h3 : ((u42OEvenMinus q m : ℕ) : ℤ) =
        2 * (q : ℤ) ^ (m * (m + 1)) * ((q : ℤ) ^ (m + 1) - (-1)) *
          ∏ i ∈ Finset.Icc 1 m, (((q : ℤ) ^ 2) ^ i - 1) := by
      unfold u42OEvenMinus
      push_cast
      rw [h2]
      ring
    exact_mod_cast h1.trans h3.symm

theorem u42_card_Sp {q m : ℕ} (hF : Nat.card F = q) {B : LinearMap.BilinForm F W}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hdim : finrank F W = 2 * m) :
    Nat.card (TauCeti.BilinForm.isometryGroup B) = u42Sp q m := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup m B hB hnd hdim, hF]
  rfl

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
