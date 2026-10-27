module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabA

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem le_or_le_of_forall_mem_or_mem {G : Type*} [Group G] (A B E : Subgroup G)
    (h : ∀ g ∈ E, g ∈ A ∨ g ∈ B) : E ≤ A ∨ E ≤ B := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hEA, hEB⟩ := hcon
  obtain ⟨x, hxE, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hEA
  obtain ⟨y, hyE, hyB⟩ := IsConcreteLE.not_le_iff_exists.mp hEB
  have hxB : x ∈ B := (h x hxE).resolve_left hxA
  have hyA : y ∈ A := (h y hyE).resolve_right hyB
  rcases h (x * y) (E.mul_mem hxE hyE) with hxy | hxy
  · exact hxA (by simpa using A.mul_mem hxy (A.inv_mem hyA))
  · exact hyB (by simpa using B.mul_mem (B.inv_mem hxB) hxy)

theorem only_E16 {F : Type} [Field F] [CharP F 2] (hq : Nat.card F = 4) :
    ∀ E : Subgroup (projectiveSL 3 F), E ≤ projUnitriangular 3 F → IsElemAbelian 2 E →
      Nat.card E = 16 →
        E = CFSG.QuasithinUnique.Fin257.L3.V2 ∨ E = CFSG.QuasithinUnique.Fin257.L3.V1 := by
  intro E hE hab hcard
  obtain ⟨-, hexp⟩ := hab
  have hmem : ∀ g ∈ E, g ∈ CFSG.QuasithinUnique.Fin257.L3.V1 ∨
      g ∈ CFSG.QuasithinUnique.Fin257.L3.V2 := by
    intro g hg
    have hgU : g ∈ projUnitriangular 3 F := hE hg
    have hsq : g * g = 1 := by
      have h2 := hexp g hg
      rwa [pow_two] at h2
    exact involution_mem_V1_or_V2 (F := F) ⟨g, hgU⟩ (Subtype.ext hsq)
  have hV1 : Nat.card (CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) = 16 := by
    rw [card_V1, hq] <;> norm_num
  have hV2 : Nat.card (CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) = 16 := by
    rw [card_V2, hq] <;> norm_num
  rcases le_or_le_of_forall_mem_or_mem CFSG.QuasithinUnique.Fin257.L3.V1
      CFSG.QuasithinUnique.Fin257.L3.V2 E hmem with hEV1 | hEV2
  · right
    haveI : Finite (CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :=
      Nat.finite_of_card_ne_zero (by rw [hV1]; norm_num)
    exact Subgroup.eq_of_le_of_card_ge hEV1 (hV1.trans hcard.symm).le
  · left
    haveI : Finite (CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :=
      Nat.finite_of_card_ne_zero (by rw [hV2]; norm_num)
    exact Subgroup.eq_of_le_of_card_ge hEV2 (hV2.trans hcard.symm).le

end CFSG.GH74.QTGen4.DSGen4.L34
