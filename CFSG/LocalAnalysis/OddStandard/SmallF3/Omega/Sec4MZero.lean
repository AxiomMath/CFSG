module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G} {u : G}

private lemma mem_centerIn_iff' {K : Subgroup G} (a : G) :
    a ∈ centerIn K ↔ a ∈ K ∧ ∀ k ∈ K, a * k = k * a := by
  rw [centerIn, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨k, hk⟩)).symm⟩
  · rintro ⟨haK, hcent⟩
    exact ⟨⟨a, haK⟩,
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hcent (y : G) y.2).symm, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
