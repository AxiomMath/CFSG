module

public import CFSG.GH74.GLS.Stage4.Statements
public import CFSG.GH74.GLS.SP.GlueBN

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.BNPair CFSG.GH74.GLS.SP

theorem ch6LocalBN_of_rgd2 (h : Ch6LocalRGD2) : Ch6LocalBN := by
  intro G _ _ hStd hr Gs _ hG2
  obtain ⟨H, r₁, r₂, U, root, R, hgen, q, hq, hcase⟩ := h G hStd hr Gs hG2
  have : IsSimpleGroup G := hStd.kps.1
  exact ⟨(R.toPre hgen).toSystemOfSimple, q, hq, hcase⟩

end CFSG.GH74.GLS.Stage4
