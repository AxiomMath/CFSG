module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLMain
public import CFSG.ClassicalInvolution.Q3.TL4D1ML32D

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG.ClassicalInvolution.Q3

theorem commutator_eq_top_of_perfect {G : Type} [Group G] {H : Subgroup G} (h : ⁅H, H⁆ = H) :
    commutator ↥H = ⊤ := by
  have h1 : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective H.subtype_injective
  rw [h1, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem not_hasS3Quot_of_perfect {E : Type} [Group E] (h : commutator E = ⊤) : ¬ HasS3Quot E := by
  rintro ⟨π, hπ⟩
  have hk := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp π)
  rw [h] at hk
  obtain ⟨x, hx⟩ := hπ (Equiv.swap (0 : Fin 3) 1)
  have h2 := hk (Subgroup.mem_top x)
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hx, Equiv.Perm.sign_swap (by decide)] at h2
  exact absurd h2 (by decide)

theorem e64NoS3_proved : E64NoS3 :=
  not_hasS3Quot_of_perfect (commutator_eq_top_of_perfect TL4.e64_perfect)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
