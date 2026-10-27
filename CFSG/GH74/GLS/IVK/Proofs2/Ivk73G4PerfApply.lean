module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Comp2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Perf
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvOut

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem u2_data_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : (HasL2Model (A ⧸ pPrimeCore 2 A) Odd ∨
        Nonempty ((A ⧸ pPrimeCore 2 A) ≃* alternatingGroup (Fin 7))) ∧
      Odd (Nat.card (center A))) :
    (HasL2Model (B ⧸ pPrimeCore 2 B) Odd ∨
        Nonempty ((B ⧸ pPrimeCore 2 B) ≃* alternatingGroup (Fin 7))) ∧
      Odd (Nat.card (center B)) := by
  let e2 : (A ⧸ pPrimeCore 2 A) ≃* (B ⧸ pPrimeCore 2 B) :=
    QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
  refine ⟨?_, ?_⟩
  · rcases h.1 with hL | he
    · exact Or.inl (TwoThin.hasL2Model_of_mulEquiv e2 hL)
    · obtain ⟨e'⟩ := he
      exact Or.inr ⟨e2.symm.trans e'⟩
  · have h1 : (center A).map e.toMonoidHom = center B := Subgroup.map_center_eq e
    rw [← h1, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at *
    exact h.2

theorem false_of_isCompIn_perfect_centralizer {M : Type} [Group M] [Finite M] {y : M}
    (hperf : Group.IsPerfect ↥(centralizer ({y} : Set M)))
    (hN : Nat.card ↥(centralizer ({y} : Set M)) = 1920 ∨
      Nat.card ↥(centralizer ({y} : Set M)) = 2688) {B : Subgroup M}
    (hB : IsCompIn (centralizer ({y} : Set M)) B)
    (hU : HasL2Model (↥B ⧸ pPrimeCore 2 ↥B) Odd ∨
      Nonempty ((↥B ⧸ pPrimeCore 2 ↥B) ≃* alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card (center ↥B))) : False := by
  let e : ↥(B.subgroupOf (centralizer ({y} : Set M))) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hB.1
  obtain ⟨hU', hodd'⟩ := u2_data_of_mulEquiv e.symm ⟨hU, hodd⟩
  exact false_of_perfect_u2_component hperf hN hB.2 hU' hodd'

theorem ivk73_empty_of_perfect_centralizers
    {P : (X : Type) → [Group X] → Prop}
    (hOut : ∀ (L : Type) [Group L] [Finite L], P L → Nat.card (Outer L) ≤ 2)
    (hperf : ∀ (L : Type) [Group L] [Finite L], P L → ∀ y : L, y * y = 1 → y ≠ 1 →
      Group.IsPerfect ↥(centralizer ({y} : Set L)) ∧
        (Nat.card ↥(centralizer ({y} : Set L)) = 1920 ∨
          Nat.card ↥(centralizer ({y} : Set L)) = 2688)) :
    Ivk73Empty P := by
  intro N _ _ L K Q h hL
  refine h.false_of_comp_u2 (GHInv.hOut_of_card_outer_le_two (hOut ↥L hL))
    fun y hy2 hy1 B hB hU hodd => ?_
  obtain ⟨hp, hn⟩ := hperf ↥L hL y hy2 hy1
  exact false_of_isCompIn_perfect_centralizer hp hn hB hU hodd

end CFSG.GH74.GLS.IVK
