module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Out
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Count

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem fixSet_top_card_le {Y : Type} [Group Y] [Finite Y]
    (hout : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g) (z : Y) (hz1 : z ≠ 1)
    (hzc : ∀ y : Y, z * y = y * z) (B : Set (Subgroup Y)) (L : List Y)
    (hL : ∀ g : Y, (∀ y : Y, (∃ b ∈ B, y ∈ b) → g * y = y * g) → g ∈ L) :
    2 * Nat.card ↥(fixSet (⊤ : Subgroup Y) B) ≤ L.length := by
  have h := card_fixSet_mul_card_center_le (⊤ : Subgroup Y) B
  have hinn : innAut ↥(⊤ : Subgroup Y) = ⊤ := by
    rw [eq_top_iff]
    intro α _
    let β : MulAut Y := (Subgroup.topEquiv (G := Y)).symm.trans (α.trans (Subgroup.topEquiv (G := Y)))
    obtain ⟨g, hg⟩ := hout β
    refine ⟨⟨g, trivial⟩, ?_⟩
    ext x
    have := congrArg (fun γ : MulAut Y => γ (x : Y)) hg
    simp only [β, MulEquiv.trans_apply] at this
    have e : (Subgroup.topEquiv (G := Y)).symm (x : Y) = x := rfl
    show g * (x : Y) * g⁻¹ = ((α x : ↥(⊤ : Subgroup Y)) : Y)
    simp only [MulAut.conj_apply] at this
    rw [e] at this
    exact this.symm
  have hout1 : Nat.card (MulAut ↥(⊤ : Subgroup Y) ⧸ innAut ↥(⊤ : Subgroup Y)) = 1 := by
    rw [hinn]
    exact Subgroup.index_top
  have hz2 : 2 ≤ Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup Y)) := by
    have hzmem : (⟨z, trivial⟩ : ↥(⊤ : Subgroup Y)) ∈ Subgroup.center ↥(⊤ : Subgroup Y) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hzc y).symm
    have hnt : Nontrivial ↥(Subgroup.center ↥(⊤ : Subgroup Y)) :=
      ⟨⟨1, ⟨⟨z, trivial⟩, hzmem⟩, fun h => hz1 (congrArg (fun x : ↥(Subgroup.center ↥(⊤ : Subgroup Y)) =>
        ((x : ↥(⊤ : Subgroup Y)) : Y)) h).symm⟩⟩
    have := Finite.one_lt_card_iff_nontrivial.2 hnt
    omega
  have hC : Nat.card ↥(Subgroup.centralizer {y : ↥(⊤ : Subgroup Y) | ∃ b ∈ B, (y : Y) ∈ b}) ≤
      L.length := by
    let f : ↥(Subgroup.centralizer {y : ↥(⊤ : Subgroup Y) | ∃ b ∈ B, (y : Y) ∈ b}) → Y :=
      fun c => ((c : ↥(⊤ : Subgroup Y)) : Y)
    have hf : Function.Injective f := fun a b hab =>
      Subtype.ext (Subtype.ext hab)
    have h1 : Nat.card ↥(Subgroup.centralizer {y : ↥(⊤ : Subgroup Y) | ∃ b ∈ B, (y : Y) ∈ b}) =
        (Set.range f).ncard := by
      rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hf]
    rw [h1]
    refine ncard_le_of_subset_list _ _ ?_
    rintro _ ⟨c, rfl⟩
    refine hL _ ?_
    intro y hy
    have := Subgroup.mem_centralizer_iff.1 c.2 ⟨y, trivial⟩ (by simpa using hy)
    exact (congrArg Subtype.val this).symm
  rw [hout1, one_mul] at h
  nlinarith

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711
