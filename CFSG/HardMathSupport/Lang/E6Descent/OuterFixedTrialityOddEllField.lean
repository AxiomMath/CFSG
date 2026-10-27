module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnSL2
public import CFSG.HardMathSupport.Lang.Proving.G2OrderDvd
public import CFSG.LieType.AlgebraicGroups.OddG2F4E8InvolutionCases
public import CFSG.LieType.Chevalley.C2E6BruhatBuilding
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.Chevalley.SteinbergBID4WeylCert
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter
public import CFSG.RankThree.PartOne.KGD.PlaneBridge

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Polynomial

set_option linter.unusedSectionVars false

section Roots

theorem exists_cube_root_unit {L : Type} [Field L] [IsAlgClosed L] (h3 : (3 : L) ≠ 0) :
    ∃ A : Lˣ, A ^ 3 = 1 ∧ A ≠ 1 := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : L[X]) (by
    have : (Polynomial.X ^ 2 + Polynomial.X + 1 : L[X]).natDegree = 2 := by compute_degree!
    intro h
    rw [Polynomial.degree_eq_natDegree (by intro h0; rw [h0] at this; simp at this), this] at h
    exact absurd h (by decide))
  simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hr3 : r ^ 3 = 1 := by linear_combination (r - 1) * hr
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr3),
    fun h => hr1 (by simpa using congrArg Units.val h)⟩

theorem three_ne_zero_of_charP {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {L : Type} [Field L]
    [CharP L p] : (3 : L) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
  have := (CharP.cast_eq_zero_iff L p 3).1 h'
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)

theorem exists_cube_root_unit_finite {K : Type} [Field K] [Finite K]
    (h : 3 ∣ Nat.card K - 1) : ∃ d : Kˣ, d ^ 3 = 1 ∧ d ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hc]; exact h)
  refine ⟨d, ?_, ?_⟩
  · rw [← hd]
    exact pow_orderOf_eq_one d
  · intro h1
    rw [h1, orderOf_one] at hd
    omega

theorem exists_unit_map_eq_cube_root {K L : Type} [Field K] [Field L] [Algebra K L]
    {d₀ : Kˣ} (hd3 : d₀ ^ 3 = 1) (hd1 : d₀ ≠ 1) {b : Lˣ} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    ∃ d : Kˣ, d ^ 3 = 1 ∧ d ≠ 1 ∧ Units.map (algebraMap K L).toMonoidHom d = b := by
  set w : Lˣ := Units.map (algebraMap K L).toMonoidHom d₀ with hw
  have hw3 : w ^ 3 = 1 := by rw [hw, ← map_pow, hd3, map_one]
  have hw1 : w ≠ 1 := fun h => hd1 ((Units.map_injective (algebraMap K L).injective) (by
    rw [map_one]; exact h))
  have hwq : (w : L) ^ 2 + w + 1 = 0 := by
    have hx3 : (w : L) ^ 3 = 1 := by simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hw3
    have : ((w : L) - 1) * ((w : L) ^ 2 + w + 1) = 0 := by linear_combination hx3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) hw1
    · exact h
  have hbq : (b : L) ^ 2 + b + 1 = 0 := by
    have hx3 : (b : L) ^ 3 = 1 := by simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hb3
    have : ((b : L) - 1) * ((b : L) ^ 2 + b + 1) = 0 := by linear_combination hx3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) hb1
    · exact h
  have hprod : ((b : L) - w) * ((b : L) - (w : L) ^ 2) = 0 := by
    have hx3 : (w : L) ^ 3 = 1 := by simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hw3
    linear_combination hbq - (b : L) * hwq + hx3
  rcases mul_eq_zero.1 hprod with h | h
  · refine ⟨d₀, hd3, hd1, Units.ext ?_⟩
    simpa [hw] using (sub_eq_zero.1 h).symm
  · refine ⟨d₀ ^ 2, by rw [← pow_mul, mul_comm, pow_mul, hd3, one_pow], ?_, Units.ext ?_⟩
    · intro h2
      apply hd1
      have : d₀ = d₀ ^ 3 * (d₀ ^ 2)⁻¹ := by group
      rw [this, hd3, h2]
      group
    · have := sub_eq_zero.1 h
      simp only [map_pow, Units.val_pow_eq_pow_val] at this ⊢
      simpa [hw] using this.symm

end Roots

end CFSG.HardMathSupport.Lang.E6Descent
