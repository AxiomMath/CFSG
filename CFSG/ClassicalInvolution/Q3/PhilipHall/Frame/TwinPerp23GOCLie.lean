module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCBasic
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups

theorem outCyc_psl2_even {L : Type} [Group L] [Finite L] {f : ℕ}
    (hf : 2 ≤ f) (e : L ≃* PSL(2, GaloisField 2 f)) : OutCyc L := by
  have h : BenderType L f 1 1 := BenderType.linear f hf e
  exact outCyc_of_sylow fun S => h.isCyclic_sylow_outer S

theorem outCyc_sz {L : Type} [Group L] [Finite L] {n : ℕ}
    (hn : 1 ≤ n) (e : L ≃* Sz n) : OutCyc L := by
  have e' : L ≃* CFSG.Theory.Comparator.SzModel n :=
    e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz n).symm)
  have h : BenderType L (2 * n + 1) 2 1 := BenderType.suzuki n hn e'
  exact outCyc_of_sylow fun S => h.isCyclic_sylow_outer S

theorem outCyc_psu3 {L : Type} [Group L] [Finite L] {f : ℕ}
    (hf : 2 ≤ f) (e : L ≃* PSU3 2 f) : OutCyc L := by
  have h : BenderType L f 3 ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) := BenderType.unitary f hf e
  exact outCyc_of_sylow fun S => h.isCyclic_sylow_outer S

theorem odd_of_pow_mod_eight {p f : ℕ} (hp : Odd p) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) :
    Odd f := by
  rcases Nat.even_or_odd f with ⟨g, hg⟩ | hodd
  · exfalso
    have h1 : p ^ f = (p ^ g) ^ 2 := by rw [hg, ← two_mul, pow_mul']
    obtain ⟨c, hc⟩ := hp.pow (n := g)
    obtain ⟨d, hd⟩ := Nat.even_mul_succ_self c
    have h2 : (p ^ g) ^ 2 = 8 * d + 1 := by
      calc (p ^ g) ^ 2 = 4 * (c * (c + 1)) + 1 := by rw [hc]; ring
        _ = 8 * d + 1 := by rw [hd]; ring
    omega
  · exact hodd

theorem outCyc_psl2_odd {L : Type} [Group L] {p f : ℕ} [hp : Fact p.Prime] (hpo : Odd p)
    (hf : 0 < f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (e : L ≃* PSL(2, GaloisField p f)) :
    OutCyc L := by
  have hfodd : Odd f := odd_of_pow_mod_eight hpo h8
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
  obtain ⟨-, h2⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hp.out (GaloisField p f) hK
  refine outCyc_of_card_dvd hfodd ((h2 L ⟨e⟩).trans ?_)
  calc f * Nat.gcd 2 (p ^ f - 1) ∣ f * 2 := Nat.mul_dvd_mul_left f (Nat.gcd_dvd_left 2 _)
    _ = 2 * f := mul_comm f 2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
