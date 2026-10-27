module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SevenCensusRot
public import CFSG.Monster.Existence.BabyOrder
public import Certificates.Certificate41507
public import CFSG.Monster.B.Pinned.Primes.Data
public import Certificates.Data.CFSGNative.MonsterB.Primes

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.B CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native CFSG.Monster.B.Pinned
  CFSG.Blueprint

theorem isConj_of_conj_eq {G : Type*} [Group G] {s t p g h : G} (hg : g * s * g⁻¹ = p)
    (hh : h * t * h⁻¹ = p) : IsConj s t := by
  refine isConj_iff.2 ⟨h⁻¹ * g, ?_⟩
  calc h⁻¹ * g * s * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * s * g⁻¹) * h := by group
    _ = h⁻¹ * (h * t * h⁻¹) * h := by rw [hg, hh]
    _ = t := by group

theorem factorization_B_seven :
    (Nat.card NativeSporadic.B).factorization 7 = 2 := by
  rw [CFSG.Monster.Existence.card_nativeB,
    show CFSG.Open.monsterBabyOrder = 7 ^ 2 * 84791458800539310024032256000000 by decide,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section

theorem bSeven_census_of_rot {x y h k : NativeSporadic.B} (D : RotSevenData x y h k)
    (s : NativeSporadic.B) (hs : orderOf s = 7) : ∃ g : NativeSporadic.B, g * s * g⁻¹ = x := by
  have : Finite NativeSporadic.B := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Monster.Existence.card_nativeB]; decide)
  exact @SevenCensus.census_seven_rot_of_card NativeSporadic.B Units.instGroup _
    factorization_B_seven _ _ _ _ D.pow_x D.comm D.card D.hx D.hy D.kx D.ky s hs

theorem bSeven_isConj_of_rot {x y h k : NativeSporadic.B} (D : RotSevenData x y h k)
    {s t : NativeSporadic.B} (hs : orderOf s = 7) (ht : orderOf t = 7) : IsConj s t := by
  obtain ⟨g, hg⟩ := bSeven_census_of_rot D s hs
  obtain ⟨g', hg'⟩ := bSeven_census_of_rot D t ht
  exact @isConj_of_conj_eq NativeSporadic.B Units.instGroup _ _ _ _ _ hg hg'

theorem exists_census_B_seven_of_rot {x y h k : NativeSporadic.B} (D : RotSevenData x y h k) :
    ∃ p : NativeSporadic.B, orderOf p = 7 ∧
      ∀ s : NativeSporadic.B, orderOf s = 7 → IsConj s p := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite NativeSporadic.B := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Monster.Existence.card_nativeB]; decide)
  have ho : orderOf x = 7 := orderOf_eq_prime D.pow_x
    (@SevenCensus.ne_of_card_rot NativeSporadic.B Units.instGroup _ _ _ _ D.pow_x D.card D.hx).1
  exact ⟨x, ho, fun s hs => bSeven_isConj_of_rot D hs ho⟩

theorem bSeven_isConj
    {s t : NativeSporadic.B} (hs : orderOf s = 7) (ht : orderOf t = 7) : IsConj s t := by
  obtain ⟨x, y, h, k, D⟩ := Certificates.certificate41507
  exact bSeven_isConj_of_rot D hs ht

end

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
