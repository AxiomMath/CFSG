module

public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Cooperstein.StructureLie (orthGL)
open scoped commutatorElement

theorem card_orthGL_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W) :
    Nat.card (orthGL Q) = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  unfold orthGL
  have h := Subgroup.comap_equiv_eq_map_symm
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
    (TauCeti.QuadraticMap.orthogonalGroup Q)
  erw [h]
  exact Nat.card_congr (MulEquiv.subgroupMap _ _).toEquiv.symm

theorem card_orthGL_eq_two_mul {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W)
    (hidx : (⁅orthGL Q, orthGL Q⁆).relIndex (orthGL Q) = 2) :
    Nat.card (orthGL Q) = 2 * Nat.card ↥⁅orthGL Q, orthGL Q⁆ := by
  have h := Subgroup.relIndex_mul_card (H := ⁅orthGL Q, orthGL Q⁆) (K := orthGL Q)
  rw [inf_of_le_left (orthGL Q).commutator_le_self, hidx] at h
  omega

theorem odd_aux (m : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    Odd ((2 : ℤ) ^ (m + 1) - ε) ∧ Odd (∏ i ∈ Finset.Icc 1 m, (((2 : ℤ) ^ 2) ^ i - 1)) := by
  constructor
  · have h2 : Even ((2 : ℤ) ^ (m + 1)) := (even_two (α := ℤ)).pow_of_ne_zero (Nat.succ_ne_zero m)
    rcases hε with rfl | rfl
    · exact h2.sub_odd odd_one
    · simpa using h2.add_one
  · refine Finset.prod_induction _ (fun n : ℤ => Odd n) (fun a b ha hb => ha.mul hb) odd_one ?_
    intro i hi
    have hi1 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
    exact (((even_two (α := ℤ)).pow_of_ne_zero two_ne_zero).pow_of_ne_zero hi1).sub_odd odd_one

theorem orthTwoPart_holds : OrthTwoPart := by
  intro W _ _ _ Q hQ hidx k hk
  have hO0 := card_orthGL_eq_two_mul Q hidx
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := by
    refine ⟨k - 1, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exfalso
      have hsub : Subsingleton W := Module.finrank_zero_iff.1 (by omega)
      have hs : Subsingleton (orthGL Q) :=
        ⟨fun a b => Subtype.ext (Units.ext (LinearMap.ext fun x => Subsingleton.elim _ _))⟩
      have := Nat.card_of_subsingleton (1 : orthGL Q)
      omega
    · omega
  have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
      2 * (Nat.card ↥⁅orthGL Q, orthGL Q⁆ : ℤ) := by
    rw [← card_orthGL_eq]; exact_mod_cast hO0
  have key : ∀ ε : ℤ, ((ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
      (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)) →
      (Nat.card ↥⁅orthGL Q, orthGL Q⁆).factorization 2 = (m + 1) * (m + 1 - 1) := by
    intro ε hε
    have hεpm : ε = 1 ∨ ε = -1 := by rcases hε with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
    have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
      (K := ZMod 2) hQ hk hε
    rw [Nat.card_zmod] at hcard
    obtain ⟨hA, hP⟩ := odd_aux m ε hεpm
    have hΩ : (Nat.card ↥⁅orthGL Q, orthGL Q⁆ : ℤ) =
        2 ^ (m * (m + 1)) * (((2 : ℤ) ^ (m + 1) - ε) *
          ∏ i ∈ Finset.Icc 1 m, (((2 : ℤ) ^ 2) ^ i - 1)) := by
      simp only [Nat.cast_ofNat] at hcard
      linarith
    have hodd : Odd (((2 : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Finset.Icc 1 m, (((2 : ℤ) ^ 2) ^ i - 1)) := hA.mul hP
    have hN : Nat.card ↥⁅orthGL Q, orthGL Q⁆ = 2 ^ (m * (m + 1)) *
        (((2 : ℤ) ^ (m + 1) - ε) *
          ∏ i ∈ Finset.Icc 1 m, (((2 : ℤ) ^ 2) ^ i - 1)).natAbs := by
      have := congrArg Int.natAbs hΩ
      rw [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow] at this
      simpa using this
    have hodd' : ¬ 2 ∣ (((2 : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Finset.Icc 1 m, (((2 : ℤ) ^ 2) ^ i - 1)).natAbs := by
      have := Int.natAbs_odd.2 hodd
      rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]
    have hne : (((2 : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Finset.Icc 1 m, (((2 : ℤ) ^ 2) ^ i - 1)).natAbs ≠ 0 := by
      rintro h
      rw [h] at hodd'
      exact hodd' (dvd_zero 2)
    generalize (((2 : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Finset.Icc 1 m, (((2 : ℤ) ^ 2) ^ i - 1)).natAbs = N at hN hne hodd'
    rw [hN, Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hodd']
    simp
    ring
  by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType Q
  · exact key 1 (Or.inl ⟨rfl, hp⟩)
  · exact key (-1) (Or.inr ⟨rfl, hp⟩)

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
