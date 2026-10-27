module

public import CFSG.LargeExtraspecial.S9PA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hP : PGL25Case H C ht ht1 hVQ)
include H C ht ht1 hVQ hP

theorem card_Abar_mul_two_pow_pgl25 :
    Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width := by
  have h1 := card_Abar_mul_four_pgl25 H C ht ht1 hVQ hP
  have hn := H.two_lt_width
  obtain ⟨k, hk⟩ : ∃ k, S.width = k + 1 := ⟨S.width - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel] at h1
  rw [hP.finrank_eq, hk]
  calc Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 2 ^ (4 - 1) =
      Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 4 * 2 := by ring
    _ = 2 ^ (k + 1) := by rw [h1, pow_succ]

end CFSG.LargeExtraspecial.S9
