module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup sporOrd SporadicOrdersTable)

@[expose] def I1431SporRow (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J → catalogIs (PSimple 3 J) S9.isU4two → False

@[expose] def i1431SporNames : Finset TauCeti.SporadicName :=
  {.J3, .McL, .Suz, .ONan, .Co3, .Fi22, .HN, .Ly, .Th, .Fi23, .Co1, .Fi24Prime, .B, .M}

theorem i1431_card_dvd {S : Type} [Group S] [Finite S] {J : Subgroup S}
    (hJU : catalogIs (PSimple 3 J) S9.isU4two) : 25920 ∣ Nat.card S := by
  obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_u4two hJU
  have h1 : Nat.card (PSimple 3 J) = 25920 := by
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.LieType.Multipliers.U42.card_PSp43
  have h2 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
  have h3 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  have h4 : Nat.card J ∣ Nat.card S := Subgroup.card_subgroup_dvd_card J
  rw [← h1]
  exact h2.trans (h3.trans h4)

theorem i1431_names_of_dvd (s : TauCeti.SporadicName) (h : 25920 ∣ sporOrd s) :
    s = TauCeti.SporadicName.Co2 ∨ s ∈ i1431SporNames := by
  revert h
  cases s <;> decide +kernel

end CFSG.LocalAnalysis.GLTheoremA

end
