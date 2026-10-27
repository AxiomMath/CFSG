module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUCls

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem ka_kay_of_kaAll {F : (Y : Type) → [Group Y] → Prop}
    (h : ∀ (Y : Type) [Group Y] [Finite Y], F Y → ∀ α : MulAut Y, α * α = 1 → α ≠ 1 →
      KAAll α) : KAY F := by
  intro Y _ _ hF _ α hα2 hα1 p hp hp2 P hPp hP1 hcomm hnorm
  have hc := h Y hF α hα2 hα1 p hp hp2 P ⟨hPp, hP1, hcomm, hnorm⟩
  exact ⟨hc.1, Or.inl hc.2⟩

theorem kay_U4_of_classes (hS : KAUSplit) (hS3 : KAU4SplitThree) (hP : KAU4Pair)
    (hO : KAUGOrth) (hO3 : KAU4GOrthThree) (hSp : KAU4GSp) : KAY FU4 := by
  refine ka_kay_of_kaAll ?_
  intro Y _ _ hY α hα2 hα1
  obtain ⟨p, f, hp, hf, hp2, -, hLie⟩ := hY
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hLie
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hα'2 : MulAut.congr e α * MulAut.congr e α = 1 := by rw [← map_mul, hα2, map_one]
  have hα'1 : MulAut.congr e α ≠ 1 := fun h' =>
    hα1 ((MulAut.congr e).injective (by rw [h', map_one]))
  exact ka_kaAll_of_congr e (kaAll_pu4 h hS hS3 hP hO hO3 hSp hp2 hα'2 hα'1)

theorem kay_U5_of_classes (hS : KAUSplit) (hO : KAUGOrth) : KAY FU5 := by
  refine ka_kay_of_kaAll ?_
  intro Y _ _ hY α hα2 hα1
  obtain ⟨p, f, hp, hf, hq4, hLie⟩ := hY
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hLie
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hα'2 : MulAut.congr e α * MulAut.congr e α = 1 := by rw [← map_mul, hα2, map_one]
  have hα'1 : MulAut.congr e α ≠ 1 := fun h' =>
    hα1 ((MulAut.congr e).injective (by rw [h', map_one]))
  exact ka_kaAll_of_congr e (kaAll_pu5 h hS hO hp2 hq4 hα'2 hα'1)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
