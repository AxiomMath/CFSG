module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUCls

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kaU3_all5 (hS : KAUSplit) (hO : KAUGOrth) {p f : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (hF : Nat.card F = (p ^ f) ^ 2)
    {Y : Type} [Group Y] [Finite Y] (hY : Nonempty (Y ≃* StatedProj (StatedSU 3 (p ^ f) F)))
    {α : MulAut Y} (hα2 : α * α = 1) (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := hY
  have h : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hα'2 : MulAut.congr e α * MulAut.congr e α = 1 := by rw [← map_mul, hα2, map_one]
  have hα'1 : MulAut.congr e α ≠ 1 := fun h' =>
    hα1 ((MulAut.congr e).injective (by rw [h', map_one]))
  exact ka_kaAll_of_congr e (kaAll_pu3 h hS hO hp2 h5 hα'2 hα'1)

theorem kaU3I5_of_classes (hS : KAUSplit) (hO : KAUGOrth) : KAU3I5 := by
  intro p f F _ _ hp hp2 hf h5 hF Y _ _ hY α _ hα2 hα1
  exact kaU3_all5 hS hO hp hp2 hf h5 hF hY hα2 hα1

theorem kaU3II5_of_classes (hS : KAUSplit) (hO : KAUGOrth) : KAU3II5 := by
  intro p f F _ _ hp hp2 hf h5 hF Y _ _ hY α hin hα2
  have hα1 : α ≠ 1 := fun h1 => hin (h1 ▸ Subgroup.one_mem _)
  exact kaU3_all5 hS hO hp hp2 hf h5 hF hY hα2 hα1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
