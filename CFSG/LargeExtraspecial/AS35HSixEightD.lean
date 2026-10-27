module

public import CFSG.LargeExtraspecial.AS35EFiveOne
public import CFSG.LargeExtraspecial.AS35EResid
public import CFSG.LargeExtraspecial.AS35HQuot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuot

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem closure_DSet_le_M (hS : S.SixFourConcl) : closure S.DSet ≤ S.M := by
  rw [closure_le]
  intro d hd
  exact S.mem_M_of_mem_ESet hS hd.1

theorem mem_closure_DbarAsc_of_mem_closure (hS : S.SixFourConcl) {y : G}
    (hy : y ∈ closure S.DSet) (hyM : y ∈ S.M) : S.ρ ⟨y, hyM⟩ ∈ closure S.DbarAsc := by
  have key : ∀ y ∈ closure S.DSet, ∀ hyM : y ∈ S.M, S.ρ ⟨y, hyM⟩ ∈ closure S.DbarAsc := by
    intro y hy
    induction hy using closure_induction with
    | mem d hd =>
      intro hdM
      exact subset_closure ⟨d, hd, hdM, rfl⟩
    | one =>
      intro h1
      have : (⟨1, h1⟩ : S.M) = 1 := rfl
      rw [this, map_one]
      exact one_mem _
    | mul a b ha hb iha ihb =>
      intro hab
      have haM := S.closure_DSet_le_M hS ha
      have hbM := S.closure_DSet_le_M hS hb
      have : (⟨a * b, hab⟩ : S.M) = ⟨a, haM⟩ * ⟨b, hbM⟩ := rfl
      rw [this, map_mul]
      exact mul_mem (iha haM) (ihb hbM)
    | inv a ha iha =>
      intro hainv
      have haM := S.closure_DSet_le_M hS ha
      have : (⟨a⁻¹, hainv⟩ : S.M) = (⟨a, haM⟩ : S.M)⁻¹ := rfl
      rw [this, map_inv]
      exact inv_mem (iha haM)
  exact key y hy hyM

omit [Finite G] in
theorem eq_one_of_mem_center_zGen {H : Type} [Group H] (T : Setting H) (hA2 : T.AschTwo)
    {l : H} (hl : l ∈ T.zGen) (hc : ∀ l' ∈ T.zGen, l * l' = l' * l) : l = 1 := by
  have := hA2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center T.zGen) with h | h
  · have h1 : (⟨l, hl⟩ : T.zGen) ∈ center T.zGen :=
      mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm
    rw [h, mem_bot] at h1
    exact congrArg Subtype.val h1
  · exfalso
    have hz : T.z ∈ centralizer (T.zGen : Set H) := by
      rw [mem_centralizer_iff]
      intro l' hl'
      have h1 : (⟨T.z, T.z_mem_zGen⟩ : T.zGen) ∈ center T.zGen := by rw [h]; exact mem_top _
      exact congrArg Subtype.val (mem_center_iff.mp h1 ⟨l', hl'⟩)
    rw [hA2.2.1, mem_bot] at hz
    exact T.z_ne_one hz

end Setting

end CFSG.LargeExtraspecial
