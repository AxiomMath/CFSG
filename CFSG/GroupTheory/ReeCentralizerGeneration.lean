module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem sup_eq_top_of_isCoatom_centralizer {x : G} {K L : Subgroup G}
    (hx2 : orderOf x = 2)
    (hdec : Subgroup.centralizer ({x} : Set G) = K ⊔ Subgroup.zpowers x)
    (hmax : IsCoatom (Subgroup.centralizer ({x} : Set G)))
    (hxL : x ∈ L) (hZ : Subgroup.center L = ⊥) : K ⊔ L = ⊤ := by
  classical
  by_contra hKL
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  obtain ⟨M, hMmax, hHle⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (K ⊔ L)).resolve_left hKL
  have hMne : M ≠ ⊤ := hMmax.1
  have hxM : x ∈ M := hHle (Subgroup.mem_sup_right hxL)
  have hCM : C ≤ M := by
    rw [hdec]
    exact sup_le (le_trans le_sup_left hHle) (Subgroup.zpowers_le.2 hxM)
  have hMC : M = C := by
    rcases (IsCoatom.le_iff hmax).mp hCM with h | h
    · exact absurd h hMne
    · exact h
  have hLC : L ≤ C := (le_trans le_sup_right hHle).trans (le_of_eq hMC)
  have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hyC : (y : G) ∈ C := hLC y.property
    exact Subtype.ext (by
      have := Subgroup.mem_centralizer_singleton_iff.1 hyC
      simpa [mul_comm] using this)
  rw [hZ, Subgroup.mem_bot] at hxZ
  have hx1 : x = 1 := congrArg Subtype.val hxZ
  rw [hx1, orderOf_one] at hx2
  exact absurd hx2 (by norm_num)

end CFSG.GroupTheory
