module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat22
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Reduce
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I81Res : Prop where
  a3 : H81FactA3
  twa3 : H81FactTwA3
  b3 : H81FactB3
  twd4 : H81FactTwD4
  d4 : H81FactD4
  disj : H81FamilyDisjoint

structure I196Res : Prop where
  fix : ∀ p : ℕ, I196OuterFix p
  core : ∀ p : ℕ, I196OuterCore p
  char : ∀ p : ℕ, I196ChevOfChar p
  card : ∀ p : ℕ, I196ChevCard p

structure S6Cat23Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i2019 : I2019At G p
  i267 : I267At G p
  i268 : I268At G p

section Ys05Cat23

theorem S6Cat23Inputs.toS6Cat22Inputs
    (h81 : I81Res) (h196 : I196Res) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S6Cat23Inputs G p) : S6Cat22Inputs G p where
  i196 := i196_of_facts G p (h196.fix p) (h196.core p) (h196.char p) (h196.card p)
  i2019 := h.i2019
  i267 := h.i267
  i268 := h.i268
  i81 := H81.i81At_of_facts h81.a3 h81.twa3 h81.b3 h81.twd4 h81.d4 h81.disj G p

end Ys05Cat23

end CFSG.LocalAnalysis.GLTheoremA
