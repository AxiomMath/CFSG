module

public import CFSG.Quasithin.H13.A7KLocal
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint

variable {G : Type} [Group G]

section Borel

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem mem_of_three_element_F4 (h1228 : Stmt12_2_8_F4) {T L V : Subgroup G} (hyp : Hyp1223 G T L V)
    (hA7 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)))
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : x ∈ L := by
  have hQ := card_quot_of_alternating_seven hA7
  have hZ : 0 < Nat.card (center (↥L ⧸ CFSG.pCore 2 ↥L)) := Nat.card_pos
  rcases h1228 G T L V hyp with h | h | ⟨-, h⟩
  · rw [← h]
    exact subset_closure ⟨hxM, 1, by rw [pow_one]; exact hx3⟩
  · exfalso
    rcases h with he | h
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, SteinbergCB.nat_card_alternating_five] at hQ
      omega
    · obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 h
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two] at hQ
      omega
  · rw [h]
    exact subset_closure ⟨hxM, orderOf_eq_prime hx3 hx1⟩

end Borel

end CFSG.Quasithin.H13.A7
