module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5AbsAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescOm6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem t5_desc_isActQuot (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    {s : G} (hs : s ∈ normalizer (L : Set G)) :
    IsActQuot (descRes L t) s (descElt L t s hs) where
  surjective := descRes_surjective L t
  ker_le_center := descRes_ker_le_center hL ht ht2
  center_of_map := fun l hl => descRes_center hL ht ht2 l hl
  mem_normalizer := hs
  mem_normalizer' := t5_desc_mem_normalizer L t hs
  conj := by
    intro l l' hl'
    rw [coe_descRes, coe_descRes]
    have h : (⟨(l' : G), Subgroup.le_normalizer l'.2⟩ : ↥(normalizer (L : Set G))) =
        ⟨s, hs⟩ * ⟨(l : G), Subgroup.le_normalizer l.2⟩ * ⟨s, hs⟩⁻¹ :=
      Subtype.ext (by simp [hl'])
    rw [h, map_mul, map_mul, map_inv]
    rfl

theorem t5_desc_inducesTypeSome_iff (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G)) (n : ℕ) (ε : ℤˣ) (r : ℕ)
    (α : ℤˣ) :
    InducesTypeSome (DescL L t) (descElt L t s hs) n ε r α ↔ InducesTypeSome L s n ε r α :=
  inducesTypeSome_transfer ⟨descRes L t, t5_desc_isActQuot hL ht ht2 hs⟩ n ε r α

theorem t5_desc_inducesProjective_iff (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G)) (n : ℕ) (ε : ℤˣ) :
    InducesProjective (DescL L t) n ε (descElt L t s hs) ↔ InducesProjective L n ε s :=
  inducesProjective_transfer ⟨descRes L t, t5_desc_isActQuot hL ht ht2 hs⟩ n ε

theorem t5_desc_inducesOutsideGStar_iff (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G)) (n : ℕ) (ε : ℤˣ) :
    InducesOutsideGStar (DescL L t) n ε (descElt L t s hs) ↔ InducesOutsideGStar L n ε s :=
  inducesOutsideGStar_transfer ⟨descRes L t, t5_desc_isActQuot hL ht ht2 hs⟩ n ε

end CFSG.OddStandard.SmallF3.Omega
