module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Sylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import Certificates.Certificate17400
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpBase

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

theorem noOrder_mul_of_card_centralizer_lt {G : Type*} [Group G] [Finite G] {p m : ℕ}
    [Fact p.Prime] {y0 : G} (hy0 : orderOf y0 = p) (hfac : (Nat.card G).factorization p = 1)
    (hcop : Nat.Coprime p m) (hlt : Nat.card (Subgroup.centralizer ({y0} : Set G)) < m * p) :
    NoOrder (m * p) G := by
  have hcent : ∀ c : G, Commute c y0 → orderOf c ≠ m := by
    intro c hc hcm
    have hxc : Commute y0 c := hc.symm
    have hy : orderOf (y0 * c) = p * m := by
      rw [hxc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hy0, hcm]; exact hcop), hy0, hcm]
    have hmem : y0 * c ∈ Subgroup.centralizer ({y0} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Commute.refl y0).mul_left hc).eq
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hy] at hdvd
    have hpos : 0 < Nat.card (Subgroup.centralizer ({y0} : Set G)) := Nat.card_pos
    have := Nat.le_of_dvd hpos hdvd
    rw [mul_comm] at this
    omega
  exact fun g hg => no_order_mul_of_sylow hy0 hfac hcent g hg

section Th

theorem x31_facts : ∃ x : J, orderOf x = 31 ∧ Nat.card (Subgroup.centralizer ({x} : Set J)) ≤ 31 :=
  Certificates.certificate17400

theorem noOrder93_J : NoOrder 93 ↥CFSG.Sporadic.Th.J := by
  obtain ⟨x, ho, hle⟩ := x31_facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hfac : (Nat.card J).factorization 31 = 1 := by
    rw [CFSG.Sporadic.Th.Max3.natCard_J,
      show (90745943887872000 : ℕ) = 31 ^ 1 * 2927288512512000 by norm_num,
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair.factorization_pow_mul
        (by norm_num) 1 _ (by norm_num)]
  exact noOrder_mul_of_card_centralizer_lt (m := 3) ho hfac (by norm_num) (by omega)

theorem noOrder93_Th : NoOrder 93 NativeSporadic.Th := fun g hg =>
  noOrder93_J (CFSG.Sporadic.Th.thEquivJ g) (by rw [MulEquiv.orderOf_eq]; exact hg)

end Th

end CFSG.HardMathSupport.Dickson.Sec6.I1431
