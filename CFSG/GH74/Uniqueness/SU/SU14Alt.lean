module

public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.GH74.Uniqueness.SU.SU8Stmts
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open Subgroup

theorem map_center_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (center X).map e.toMonoidHom = center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ center X := hx
    rw [mem_center_iff] at hx'
    rw [mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    have := congrArg e (hx' a)
    simpa using this
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    rw [mem_center_iff] at hy
    show x ∈ center X
    rw [mem_center_iff]
    intro g
    apply e.injective
    simpa using hy (e g)

theorem card_center_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (center X) = Nat.card (center Y) :=
  Nat.card_congr
    ((e.subgroupMap (center X)).trans (MulEquiv.subgroupCongr (map_center_equiv e))).toEquiv

theorem isTwoAlt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : K.IsTwoAlt X n) : K.IsTwoAlt Y n := by
  obtain ⟨hq, hfin, hc, ⟨f⟩⟩ := h
  refine ⟨(CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq,
    Finite.of_equiv X e.toEquiv, ?_, ?_⟩
  · rw [← card_center_equiv e]
    exact hc
  · exact ⟨(QuotientGroup.congr (center X) (center Y) e (map_center_equiv e)).symm.trans f⟩

theorem isTwoAlt_of_pPrimeCore_eq_bot {G : Type} [Group G] (C : Subgroup G)
    (hC : pPrimeCore 2 ↥C = ⊥) {n : ℕ} (h : K.IsTwoAlt (SU8.Hbar C) n) : K.IsTwoAlt ↥C n :=
  isTwoAlt_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot) h

end CFSG.GH74.Uniqueness.SU.SU14
