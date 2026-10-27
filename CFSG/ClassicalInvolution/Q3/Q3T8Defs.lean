module

public import CFSG.ClassicalInvolution.Q3.Q3DStand
public import CFSG.ClassicalInvolution.Q3.Q3CLApi

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.Disc3

section Stand

structure AscStand {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  modU : HypOmegaModU (.sl2 3 1) Ω
  hyp : HypOmegaGen Ω
  cls : Q3CL.ClassicalClause Ω
  rank : 3 ≤ CFSG.Open.twoRank G
  notFour : ¬ TwoSubgroupsFourGenerated G
  below : CITBelowT (.sl2 3 1) (Nat.card G)
  ih : IH8T 3 1 (Nat.card G)
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}

theorem AscStand.of_stand3 (h : AscStand3 Ω K) (h3 : 3 ≤ CFSG.Open.twoRank G)
    (h4 : ¬ TwoSubgroupsFourGenerated G) : AscStand Ω K where
  modU := h.hyp
  hyp := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) h.hyp
  cls := Q3CL.classicalClause_of_modU h.hyp
  rank := h3
  notFour := h4
  below := h.below
  ih := h.ih
  aEmpty := h.aEmpty
  mem := h.mem
  trans := h.trans
  gen := h.gen

theorem AscStand.toStand3 (h : AscStand Ω K) : AscStand3 Ω K where
  hyp := h.modU
  below := h.below
  ih := h.ih
  aEmpty := h.aEmpty
  mem := h.mem
  trans := h.trans
  gen := h.gen

end Stand

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
