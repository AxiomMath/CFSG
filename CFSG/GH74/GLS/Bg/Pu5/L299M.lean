module

public import CFSG.GH74.GLS.Bg.Pu5.L299MIIa
public import CFSG.GH74.GLS.Bg.Pu5.L299MIIb
public import CFSG.GH74.GLS.Bg.Pu5.L299Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem l299m_of (h44 : II4_44) (hquat : II4_4_quat) (h293 : L293) (h296 : L296)
    (hFour : L299FourS) : L299MS := by
  intro G _ _ z t S hC hcard K hK
  by_contra hcon
  push Not at hcon
  obtain ⟨hnc, hnm⟩ := hcon
  by_cases hIIa : ∀ q ∈ S ⊓ cSec K, q * t = t * q → q ∈ zpowers z
  · rcases l299m_caseIIa h44 hquat h296 hFour hC hcard hK hIIa with h | h
    · exact hnc h
    · exact hnm h
  · push Not at hIIa
    exact l299m_caseIIb h44 hquat h293 h296 hC hcard hK hIIa hnc hnm

end CFSG.GH74.GLS.Bg.Pu5
