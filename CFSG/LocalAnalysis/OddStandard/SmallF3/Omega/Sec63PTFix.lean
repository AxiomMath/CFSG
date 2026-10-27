module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec63PT_map_fixSub {A P : Type} [Group A] [Group P] {ρ : A →* P} (h : OddCentralCover ρ)
    {σ : MulAut A} {α : MulAut P} (hσ : σ * σ = 1) (hρσ : ∀ a, ρ (σ a) = α (ρ a)) :
    (fixSub σ).map ρ = fixSub α := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_fixSub_iff.mpr (by rw [← hρσ a, mem_fixSub_iff.mp ha])
  · intro p hp
    obtain ⟨y, hy⟩ := h.fixHom_surjective hσ hρσ ⟨p, hp⟩
    exact ⟨(y : A), y.2, congrArg Subtype.val hy⟩

theorem sec63PT_map_inf_centralizer {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) {V : Subgroup A} {b : A} (hb : b * b = 1) :
    (V ⊓ centralizer ({b} : Set A)).map ρ = V.map ρ ⊓ centralizer ({ρ b} : Set P) := by
  apply le_antisymm
  ·
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hvV, hvc⟩ := Subgroup.mem_inf.mp hv
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_map_of_mem ρ hvV, mem_centralizer_singleton_iff.mpr (by
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hvc])⟩
  ·
    intro p hp
    obtain ⟨hpV, hpc⟩ := Subgroup.mem_inf.mp hp
    obtain ⟨v, hvV, hρv⟩ := Subgroup.mem_map.mp hpV
    refine Subgroup.mem_map.mpr ⟨v, Subgroup.mem_inf.mpr ⟨hvV, ?_⟩, hρv⟩
    rw [h.centralizer_singleton_eq_comap hb, mem_comap, mem_centralizer_singleton_iff, hρv]
    exact mem_centralizer_singleton_iff.mp hpc

end CFSG.OddStandard.SmallF3.Omega
