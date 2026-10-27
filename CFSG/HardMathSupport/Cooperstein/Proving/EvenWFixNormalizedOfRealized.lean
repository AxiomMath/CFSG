module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockWreath

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

theorem mem_normalizer_of_conj_le {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (hle : ∀ h ∈ H, g * h * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hmap : H.map (MulAut.conj g).toMonoidHom = H := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨h, hh, rfl⟩
      simpa [MulAut.conj_apply] using hle h hh
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hle h
  · intro hgh
    have hmem : g * h * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by
      rw [hmap]
      exact hgh
    obtain ⟨x, hx, hxh⟩ := Subgroup.mem_map.1 hmem
    have hxe : x = h := by
      simpa [MulAut.conj_apply] using hxh
    exact hxe ▸ hx

variable {M : Type*} [Group M] {n : ℕ}

end CFSG.HardMathSupport.Cooperstein.Proving
