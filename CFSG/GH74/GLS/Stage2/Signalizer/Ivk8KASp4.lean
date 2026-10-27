module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4I
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4II
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Field
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Q3U1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Q3I

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kay_Sp4 : KAY FSp4 := by
  intro Y _ _ hY _ α hα2 hα1 p hp hp2 P hPp hP1 hcomm hnorm
  obtain ⟨p0, f0, hp0, hf0, hp02, hlie⟩ := hY
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack hlie
  have hodd : ringChar F ≠ 2 := ringChar_ne_two_of_card_psp4 hp0 hp02 hcard
  have hα'2 : MulAut.congr e α * MulAut.congr e α = 1 := by rw [← map_mul, hα2, map_one]
  have hα'1 : MulAut.congr e α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (by rw [h, map_one]))
  have hK : KAAll (MulAut.congr e α) :=
    kaAll_psp4 kaSp4U1_thm kaSp4I_thm kaSp4II_thm kaSp4Field_thm kaSp4U1Three_thm
      kaSp4IThree_thm hodd hα'2 hα'1
  have h := KAAll.of_mulEquiv e.symm hK
  have key : MulAut.congr e.symm (MulAut.congr e α) = α := by
    ext y
    simp [MulAut.congr_apply]
  rw [key] at h
  have hc := h p hp hp2 P ⟨hPp, hP1, hcomm, hnorm⟩
  exact ⟨hc.1, Or.inl hc.2⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
