module

public import CFSG.LargeExtraspecial.AS35ESixEleven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem z_mem_BSet (hS : S.SixHyp) : S.z ∈ S.BSet := by
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  simpa using S.self_mem_BAt hS.sixFour ⟨t, ht⟩ 1

theorem mem_BStab_iff_of (hS : S.SixHyp)
    (h69 : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g = S.BSet) {x : G} :
    x ∈ S.BStab ↔ x * S.z * x⁻¹ ∈ S.BSet :=
  S.mem_BStab_iff hS.sixFour (fun g hg => (h69 g hg).le) (S.z_mem_BSet hS)

theorem M_le_BStab (hS : S.SixHyp)
    (h69 : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g = S.BSet) : S.M ≤ S.BStab := fun m hm =>
  (S.mem_BStab_iff_of hS h69).mpr (by rw [S.conj_z_of_mem_M hm]; exact S.z_mem_BSet hS)

omit [Finite G] in
theorem isConj_of_mem_BAt {g b : G} (hb : b ∈ S.BAt g) : IsConj S.z b := by
  obtain ⟨k, -, hbk⟩ := hb
  obtain ⟨h, rfl⟩ := S.exists_conj_of_mem_DAt hbk
  exact isConj_iff.mpr ⟨h, rfl⟩

end Setting

end CFSG.LargeExtraspecial
