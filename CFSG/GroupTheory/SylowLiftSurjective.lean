module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

theorem exists_isPGroup_not_dvd_index_map_le
    {G H : Type*} [Group G] [Group H] [Finite G]
    (φ : G →* H) (hφ : Function.Surjective φ) {p : ℕ} (hp : p.Prime) {T : Subgroup H}
    (hT : ¬ p ∣ T.index) :
    ∃ Tstar : Subgroup G, IsPGroup p Tstar ∧ ¬ p ∣ Tstar.index ∧ Tstar.map φ ≤ T := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Subgroup G := T.comap φ
  have hP : ¬ p ∣ P.index := by
    rw [Subgroup.index_comap_of_surjective T hφ]
    exact hT
  let Q : Sylow p P := Classical.choice (inferInstance : Nonempty (Sylow p P))
  let Tstar : Subgroup G := (Q : Subgroup P).map P.subtype
  have hmap_le : Tstar ≤ P := Subgroup.map_subtype_le _
  have hQ : ¬ p ∣ (Q : Subgroup P).index := Q.not_dvd_index
  have hrel : Tstar.relIndex P = (Q : Subgroup P).index := by
    change (Subgroup.comap P.subtype ((Q : Subgroup P).map P.subtype)).index =
      (Q : Subgroup P).index
    rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  have hodd : ¬ p ∣ Tstar.index := by
    rw [← Subgroup.relIndex_mul_index hmap_le, hrel]
    exact hp.not_dvd_mul hQ hP
  refine ⟨Tstar, Q.isPGroup'.map _, hodd, ?_⟩
  calc Tstar.map φ ≤ P.map φ := Subgroup.map_mono hmap_le
    _ = T := by rw [show P = T.comap φ from rfl, Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.mpr hφ, top_inf_eq]

end CFSG.GroupTheory

end
