module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec63_mem_normalizer_of_comm [Finite G] {Y : Subgroup G} {x : G}
    (h : ⁅Y, zpowers x⁆ = Y) : x ∈ normalizer (Y : Set G) := by
  have hle : ∀ a ∈ Y, x * a * x⁻¹ ∈ Y := by
    intro a ha
    have hc : ⁅a⁻¹, x⁆ ∈ ⁅Y, zpowers x⁆ :=
      Subgroup.commutator_mem_commutator (Y.inv_mem ha) (Subgroup.mem_zpowers x)
    rw [h] at hc
    have e : x * a * x⁻¹ = a * ⁅a⁻¹, x⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Y.mul_mem ha hc
  have hmap : Y.map (MulAut.conj x).toMonoidHom ≤ Y := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hle a ha
  have hEq : Y.map (MulAut.conj x).toMonoidHom = Y :=
    Subgroup.eq_of_le_of_card_ge hmap
      (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => hle a ha, fun hax => ?_⟩
  have hax' : x * a * x⁻¹ ∈ Y.map (MulAut.conj x).toMonoidHom := by
    rw [hEq]
    exact hax
  obtain ⟨b, hb, hba⟩ := hax'
  have hba' : b = a := by simpa [MulAut.conj_apply] using hba
  rw [← hba']
  exact hb

theorem sec63_mem_normalizer_of_centralizes [Finite G] {y r : G} {V Y H : Subgroup G}
    (hY : IsComponentIn Y (centralizer ({y} : Set G))) (hr : r ∈ centralizer ({y} : Set G))
    (hV : IsComponentIn V H) (hVY : V ≤ Y) (hrV : ∀ a ∈ V, r * a = a * r) :
    r ∈ normalizer (Y : Set G) := by
  by_contra hn
  have hne : CFSG.conjugate Y r ≠ Y := fun h => hn (mem_normalizer_of_conjugate_eq h)
  have hY' : IsComponentIn (CFSG.conjugate Y r) (centralizer ({y} : Set G)) := hY.conjugate hr
  have hcomm := hY.commute_of_ne hY' hne.symm
  apply hV.not_le_centralizer
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbY' : b ∈ CFSG.conjugate Y r := by
    rw [mem_conjugate_iff]
    have hrb : r * b * r⁻¹ = b := by
      rw [hrV b hb]
      group
    rw [hrb]
    exact hVY hb
  exact (hcomm a (hVY ha) b hbY').symm

end CFSG.OddStandard.SmallF3.Omega
