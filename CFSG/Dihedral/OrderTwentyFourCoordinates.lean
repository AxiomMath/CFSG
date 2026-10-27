module

public import CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem CoordinateWitness.oddPrimePower_card (w : CoordinateWitness X) :
    IsOddPrimePower (Nat.card w.K) := by
  let : Fintype w.K := Fintype.ofFinite w.K
  obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' w.K
  have hpodd : Odd p := w.odd.of_dvd_nat (by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p (by have := n.pos; omega))
  exact ⟨p, n, hp, hpodd, by have := n.pos; omega, by
    simpa only [Nat.card_eq_fintype_card] using hcard⟩

theorem CoordinateWitness.card_eq_three_of_card_twentyFour
    (w : CoordinateWitness X) (hX : Nat.card X = 24) : Nat.card w.K = 3 := by
  let : Finite w.rho.range := Finite.of_surjective w.rho.rangeRestrict w.rho.rangeRestrict_surjective
  have hbound : Nat.card (PSL2 w.K) ≤ 24 := by
    have h := Subgroup.card_le_of_le w.containsPSL
    rw [← Nat.card_congr (pGammaL2PSLRangeEquiv w.K).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective w.injective).toEquiv, hX] at h
    exact h
  rw [psl2_card_formula w.K w.oddPrimePower_card] at hbound
  have hqpos : 1 < Nat.card w.K := by
    let : Fintype w.K := Fintype.ofFinite w.K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hqle : Nat.card w.K < 4 := by
    by_contra hnot
    have h4 : 4 ≤ Nat.card w.K := by omega
    have h16 : 16 ≤ Nat.card w.K ^ 2 := by nlinarith
    have h60 : 60 ≤ Nat.card w.K * (Nat.card w.K ^ 2 - 1) :=
      Nat.mul_le_mul h4 (by omega : 15 ≤ Nat.card w.K ^ 2 - 1)
    omega
  have hodd := w.odd
  obtain ⟨k, hk⟩ := hodd
  omega

theorem ringAut_eq_one_of_card_three (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3) (a : K ≃+* K) : a = 1 := by
  let : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rwa [Nat.card_eq_fintype_card] at hK
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hcard
  have h := Subsingleton.elim (e.trans a) e
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun h y

theorem pGammaL2PGLRange_eq_top_of_card_three (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3) : pGammaL2PGLRange K = ⊤ := by
  apply top_le_iff.mp
  intro x _
  refine ⟨x.left, ?_⟩
  apply SemidirectProduct.ext
  · rfl
  · exact (ringAut_eq_one_of_card_three K hK x.right).symm

theorem CoordinateWitness.range_eq_pgl_of_card_twentyFour
    (w : CoordinateWitness X) (hX : Nat.card X = 24) :
    w.rho.range = pGammaL2PGLRange w.K := by
  have hq := w.card_eq_three_of_card_twentyFour hX
  have hpgl : pGammaL2PGLRange w.K = ⊤ := pGammaL2PGLRange_eq_top_of_card_three w.K hq
  have hcard : Nat.card (pGammaL2PGLRange w.K) = 24 := by
    rw [← Nat.card_congr (pGammaL2PGLRangeEquiv w.K).toEquiv, pgl2_card_formula, hq]
    decide
  let : Finite (pGammaL2PGLRange w.K) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  apply Subgroup.eq_of_le_of_card_ge (by rw [hpgl]; exact le_top)
  rw [hcard, ← Nat.card_congr (MonoidHom.ofInjective w.injective).toEquiv, hX]

end CFSG.DihedralBlueprint
