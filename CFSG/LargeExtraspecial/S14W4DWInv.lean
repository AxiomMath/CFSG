module

public import CFSG.LargeExtraspecial.S14W4SetPi
public import CFSG.LargeExtraspecial.DW4Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Hyp

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.DW.W4
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {c : Config}
  (h : W4Hyp S g t c)
include h

theorem two_pow_nine_le_card_Lbar : 2 ^ 9 ≤ Nat.card (S.Lbar g) := by
  have hwidth : S.width = 10 := by
    rcases h.hc with rfl | rfl <;> exact h.occ.2.1
  have := S.card_Lbar_ge h.haQ h.stage.hyp4.conj_ne
  rwa [hwidth] at this

omit h in
theorem mem_comap_Lbar {e : ↥(Mbar0 S)} : e ∈ (S.Lbar g).comap (ι S) ↔ ι S e ∈ S.Lbar g :=
  Iff.rfl

theorem card_comap_Lbar : Nat.card ((S.Lbar g).comap (ι S)) = Nat.card (S.Lbar g) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun e : (S.Lbar g).comap (ι S) => (⟨ι S e, mem_comap_Lbar.mp e.2⟩ : S.Lbar g))
    ⟨fun e e' hee' => ?_, fun y => ?_⟩)
  · apply Subtype.ext
    apply ι_injective S
    have := congrArg Subtype.val hee'
    exact this
  · have hy := exists_ι_eq (h.le (Lbar_le_Rbar h.stage.mem y.2))
    refine ⟨⟨hy.choose, mem_comap_Lbar.mpr ?_⟩, Subtype.ext hy.choose_spec⟩
    rw [hy.choose_spec]
    exact y.2

theorem comap_Lbar_le : (S.Lbar g).comap (ι S) ≤ h.S₀.M := fun _ he =>
  h.R₀_le_M (Lbar_le_Rbar h.stage.mem (mem_comap_Lbar.mp he))

theorem comap_Lbar_comm : ∀ e ∈ (S.Lbar g).comap (ι S), ∀ e' ∈ (S.Lbar g).comap (ι S),
    e * e' = e' * e := by
  have := S.isElementaryAbelian_Lbar h.haQ
  intro e he e' he'
  apply ι_injective S
  rw [map_mul, map_mul]
  exact congrArg Subtype.val
    (mul_comm (⟨ι S e, mem_comap_Lbar.mp he⟩ : S.Lbar g) ⟨ι S e', mem_comap_Lbar.mp he'⟩)

theorem comap_Lbar_sq : ∀ e ∈ (S.Lbar g).comap (ι S), e * e = 1 := fun e he =>
  ι_injective S (by
    rw [map_mul, map_one]
    exact mul_self_of_mem_Lbar S h.haQ (mem_comap_Lbar.mp he))

theorem exists_isRank2Inv_res {W₁ W₂ : Submodule (ZMod 2) h.S₀.Qt} (H : DW.W4.Hyp h.S₀ W₁ W₂) :
    ∃ x : h.S₀.M, x * x = 1 ∧ IsRank2Inv (H.res x) :=
  H.exists_isRank2Inv_of_le h.comap_Lbar_le h.comap_Lbar_comm h.comap_Lbar_sq
    (h.two_pow_nine_le_card_Lbar.trans_eq h.card_comap_Lbar.symm)

end CFSG.LargeExtraspecial.S14.W4Hyp
