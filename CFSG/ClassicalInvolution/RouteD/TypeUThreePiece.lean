module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.RouteD.TypeUThreeMain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem shapePiece_su4 (hMFZ : Gaps.FundNoncentral p) : ShapePiece p f 1 .PSU 4 := by
  intro G _ _ _ hnab K z S hS
  obtain ⟨D, -, -⟩ := routeD_typeU_three hMFZ S.odd S.five S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS.exists_two_components S.p1
  exact ⟨D⟩

end CFSG.ClassicalInvolution.RouteD
