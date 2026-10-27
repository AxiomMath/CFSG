module

public import CFSG.GH74.GLS.IVK.L2.ExistEven

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section Exist

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_notation (hF : L2Field F) (e : K ≃* L2 F) : Nonempty (L2Notation e) := by
  rcases Nat.even_or_odd (Nat.card ↥(fieldAutSub e)) with h | h
  · exact exists_notation_of_even e hF h
  · exact exists_notation_of_odd e hF h

theorem ivk_1_2a_exists : IVK_1_2a_exists := by
  intro F _ _ hF K _ _ e T
  obtain ⟨N⟩ := exists_notation hF e
  exact exists_notation_of_exists N T

theorem ivk_1_2a : IVK_1_2a := IVK_1_2a_of_parts ivk_1_2a_exists ivk_1_2a_struct

end Exist

theorem ivk_1_2_general : IVK_1_2_general := by
  intro F _ _ hF H _ _ K _ hKe T
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hKe
  obtain ⟨N₀⟩ := exists_notation hF e
  have hTbar : IsPGroup 2 ↥((T : Subgroup H).map (MulAut.conjNormal : H →* MulAut ↥K)) :=
    T.isPGroup'.map _
  obtain ⟨T', hT'⟩ := hTbar.exists_le_sylow
  obtain ⟨e', N, hN⟩ := exists_notation_of_exists N₀ T'
  refine ⟨e', N, ?_, ?_⟩
  · rw [hN]
    exact hT'
  · have hle : ((T : Subgroup H) ⊓ K).map (MulAut.conjNormal : H →* MulAut ↥K) ≤ N.P := by
      rintro _ ⟨x, ⟨hxT, hxK⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hN]
        exact hT' ⟨x, hxT, rfl⟩
      · obtain ⟨k, rfl⟩ : ∃ k : ↥K, (k : H) = x := ⟨⟨x, hxK⟩, rfl⟩
        rw [MulAut.conjNormal_val]
        exact ⟨k, rfl⟩
    have hinjOn : Set.InjOn (MulAut.conjNormal : H →* MulAut ↥K) (((T : Subgroup H) ⊓ K : Subgroup H) : Set H) := by
      intro x hx y hy hxy
      obtain ⟨kx, rfl⟩ : ∃ k : ↥K, (k : H) = x := ⟨⟨x, hx.2⟩, rfl⟩
      obtain ⟨ky, rfl⟩ : ∃ k : ↥K, (k : H) = y := ⟨⟨y, hy.2⟩, rfl⟩
      rw [MulAut.conjNormal_val, MulAut.conjNormal_val] at hxy
      exact congrArg Subtype.val (conj_injective_of_L2 e hxy)
    have hcard1 : Nat.card ↥(((T : Subgroup H) ⊓ K).map (MulAut.conjNormal : H →* MulAut ↥K)) =
        Nat.card ↥((T : Subgroup H) ⊓ K) := Nat.card_image_of_injOn hinjOn
    have hcard2 := card_sylow_inf_normal 2 T K
    have hcard3 := card_P_eq e' N
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard3, ← hcard2, hcard1]))

end CFSG.GH74.GLS.IVK
