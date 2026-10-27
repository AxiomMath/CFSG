module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2AtT
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwG2D4
public import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8G2

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG3

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77

theorem centralizer_one_eq_top {X : Type*} [Group X] :
    Subgroup.centralizer ({1} : Set X) = ⊤ :=
  eq_top_iff.2 fun g _ => Subgroup.mem_centralizer_singleton_iff.2 (by simp)


theorem twinMFGeneration_g2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) :
    TwinMFGeneration p e .G2 0 := by
  intro R R' x x' hd a ha a' ha' hax ha'x S _
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .G2 0 p e := ⟨Fact.out, he, rfl, by omega⟩
  obtain ⟨-, hZ, -, hG⟩ := T3CII.T3U.g2d4_model_facts (p := p) (f := e) hp2 hq (Or.inl rfl)
    trivial hadm (Or.inl rfl)
  have hsame := hd.same
  rw [hZ, Subgroup.mem_bot] at hax ha'x hsame
  have hxx : x = x' := mul_inv_eq_one.mp hsame
  have haa : a * a = x := mul_inv_eq_one.mp hax
  have ha'a' : a' * a' = x' := mul_inv_eq_one.mp ha'x
  have hx2 : x * x = 1 := ModelFacts.fundCentral_sq_G2 0 p e hadm R hd.mem x hd.hx hd.cx
  have hcomm : a * a' = a' * a := hd.comm a ha a' ha'
  have hu2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [hcomm]
      _ = (a * a) * (a' * a') := by group
      _ = 1 := by rw [haa, ha'a', ← hxx, hx2]
  have hxu : x * (a * a') = (a * a') * x := by
    have h1 : x * a = a * x := hd.cx a ha
    have h2 : x * a' = a' * x := by rw [hxx]; exact hd.cx' a' ha'
    calc x * (a * a') = (x * a) * a' := by group
      _ = a * (x * a') := by rw [h1]; group
      _ = (a * a') * x := by rw [h2]; group
  by_cases hu1 : a * a' = 1
  · rw [hu1, centralizer_one_eq_top, sup_top_eq, top_sup_eq]
    exact le_top
  by_cases hux : a * a' = x
  · rw [hux, hx2, centralizer_one_eq_top, sup_top_eq]
    exact le_top
  rw [hG x (a * a') hx2 hu2 hd.nx hu1 (Ne.symm hux) hxu]
  exact le_top

end CFSG.ClassicalInvolution.NDB.NDBG3
