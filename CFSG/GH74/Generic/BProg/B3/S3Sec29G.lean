module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29Tail
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29wDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Sec29G

variable {G : Type} [Group G] [Finite G]

theorem ctx29w_of_H29 {x y b : G} {K A B Q D J : Subgroup G} (h : H29 G x K A B Q y) (hb : b ∈ B)
    (hobs : Obs52 B b D J ∨
      (b = y ∧ Obs32 A y D J ∧ D ≤ A ∧ IsA7Bar J ∧ ¬ J ≤ gammaK 2 B 3)) :
    Ctx29w G x K A B Q y b D J :=
  ⟨h.hyp, h.noAlt, h.circ, h.shape, h.src, h.ext, h.rankB, h.C_rank, h.B0_le_C, h.Q_syl,
    h.Q_cent, h.B0_le_Q, h.y_mem, h.y_ord, h.notG, hb, hobs⟩

end S3Sec29G

end CFSG.GH74.Generic.BProg.B3
