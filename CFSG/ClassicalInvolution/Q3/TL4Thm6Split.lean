module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6Defs
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Split

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint

namespace Thm6

theorem split_l3 : ∀ (F : Type) [Group F], TA3.SmallL3 F →
    LieModel F .PSL 3 3 1 ∨ TA3.SmallL3Ne3 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3
    exact Or.inl (Or.inl ⟨by decide, hm⟩)
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem split_u3 : ∀ (F : Type) [Group F], TA3.SmallU3 F →
    LieModel F .PSU 3 3 1 ∨ TA3.SmallU3Ne3 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3
    exact Or.inl (Or.inl ⟨by decide, hm⟩)
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem split_psp4 : ∀ (F : Type) [Group F], TA3.SmallPSp4 F →
    LieModel F .PSp 2 3 1 ∨ TA3.SmallPSp4Ne3 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem split_g2 : ∀ (F : Type) [Group F], TA3.SmallG2 F →
    LieModel F .G2 0 3 1 ∨ TA3.SmallG2Ne3 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem split_d4 : ∀ (F : Type) [Group F], TA3.SmallD4 F →
    LieModel F .trialityD4 0 3 1 ∨ TA3.SmallD4Ne3 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem split_l4 : ∀ (F : Type) [Group F], TA3.SmallL4 F →
    LieModel F .PSL 4 3 1 ∨ TA3.SmallL4Ne3 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

theorem split_u4 : ∀ (F : Type) [Group F], TA3.SmallU4 F →
    LieModel F .PSU 4 3 1 ∨ TA3.SmallU4Ne3 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

theorem split_l5 : ∀ (F : Type) [Group F], TA3.SmallL5 F →
    LieModel F .PSL 5 3 1 ∨ TA3.SmallL5Ne3 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

end Thm6

section Cit3


theorem SmallSimpleLeaf6.of_noDatum {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → Nobq.NoDatum F) : SmallSimpleLeaf6 P := by
  intro Y _ _ _ _ hnab _ hPF R S t hd _ _
  exfalso
  have := genFittingFStar_normal Y
  obtain ⟨r, hr, ⟨eS⟩⟩ := hd.quat
  exact h _ hPF Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) R S r hr ⟨eS⟩ t hd.mem hd.order hd.cent
    hd.normal

theorem SmallSimpleLeaf6.of_good {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup ↥(genFittingFStar Y)],
      (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) → P ↥(genFittingFStar Y) →
      ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → GoodThreeElement R t) :
    SmallSimpleLeaf6 P :=
  fun Y _ _ _ _ hnab _ hP R S t hd _ _ => Or.inl (h Y hnab hP R S t hd)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
