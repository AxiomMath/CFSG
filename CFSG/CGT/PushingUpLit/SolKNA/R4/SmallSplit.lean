module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Split
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3

theorem SmallLeafR.of_split {r : ℕ} {P Q₃ Q : ∀ (F : Type) [Group F], Prop}
    (hsplit : ∀ (F : Type) [Group F], P F → Q₃ F ∨ Q F) (h₃ : SmallLeafR r Q₃)
    (h : SmallLeafR r Q) : SmallLeafR r P :=
  fun Y _ _ _ hnab hG hPF R S t hd hc hE2 =>
    (hsplit _ hPF).elim (fun h3 => h₃ Y hnab hG h3 R S t hd hc hE2)
      (fun h4 => h Y hnab hG h4 R S t hd hc hE2)

theorem smallLeafR_l3_of_split {r : ℕ} (h₃ : SmallLeafR r fun F _ => LieModel F .PSL 3 3 1)
    (h : SmallLeafR r SmallL3Ne3) : SmallLeafR r SmallL3 := by
  refine SmallLeafR.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl (Or.inl ⟨by decide, hm⟩)
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem smallLeafR_u3_of_split {r : ℕ} (h₃ : SmallLeafR r fun F _ => LieModel F .PSU 3 3 1)
    (h : SmallLeafR r SmallU3Ne3) : SmallLeafR r SmallU3 := by
  refine SmallLeafR.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl (Or.inl ⟨by decide, hm⟩)
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem smallLeafR_psp4_of_split {r : ℕ} (h₃ : SmallLeafR r fun F _ => LieModel F .PSp 2 3 1)
    (h : SmallLeafR r SmallPSp4Ne3) : SmallLeafR r SmallPSp4 := by
  refine SmallLeafR.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem smallLeafR_g2_of_split {r : ℕ} (h₃ : SmallLeafR r fun F _ => LieModel F .G2 0 3 1)
    (h : SmallLeafR r SmallG2Ne3) : SmallLeafR r SmallG2 := by
  refine SmallLeafR.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem smallLeafR_d4_of_split {r : ℕ} (h₃ : SmallLeafR r fun F _ => LieModel F .trialityD4 0 3 1)
    (h : SmallLeafR r SmallD4Ne3) : SmallLeafR r SmallD4 := by
  refine SmallLeafR.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem smallLeafR_l4_of_split {r : ℕ} (h₃ : SmallLeafR r fun F _ => LieModel F .PSL 4 3 1)
    (h : SmallLeafR r SmallL4Ne3) : SmallLeafR r SmallL4 := by
  refine SmallLeafR.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

theorem smallLeafR_u4_of_split {r : ℕ} (h₃ : SmallLeafR r fun F _ => LieModel F .PSU 4 3 1)
    (h : SmallLeafR r SmallU4Ne3) : SmallLeafR r SmallU4 := by
  refine SmallLeafR.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

theorem smallLeafR_l5_of_split {r : ℕ} (h₃ : SmallLeafR r fun F _ => LieModel F .PSL 5 3 1)
    (h : SmallLeafR r SmallL5Ne3) : SmallLeafR r SmallL5 := by
  refine SmallLeafR.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
