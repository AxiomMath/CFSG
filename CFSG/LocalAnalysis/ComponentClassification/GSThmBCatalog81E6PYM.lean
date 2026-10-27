module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PYT
public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.GH74.Generic.S45.LSporMathB
public import CFSG.GH74.Generic.S45.LSporJ3
public import CFSG.Sporadic.Schreier.M23

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211Y

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer P211 P211X

theorem p211For_M22 :
    P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .M22 := by
  intro X _ _ hsimp hC ⟨e⟩ p f hp hp2 hf a J D _ _ _ _ hJt hJF hDJ hDsyl hbound b K hb hb1
    hKC hK hKt
  exfalso
  have e' : ↥(generalizedFitting X) ≃* ↥Blueprint.NativeSporadic.M22 := e
  refine p211_of_fixed_lt hC (outer_solvable_of_equiv e' Sporadic.Schreier.at_m22_schreier.2.2)
    (fun α hα2 hα1 => ?_) hp hp2 hf hb hb1 hKC hK hKt
  have hβ2 : MulAut.congr e' α * MulAut.congr e' α = 1 := by rw [← map_mul, hα2, map_one]
  have hβ1 : MulAut.congr e' α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  rw [← card_fixed_congr e' α]
  rcases GH74.Generic.S45.m22_fixed_card (MulAut.congr e' α) hβ2 hβ1 with h | h | h <;> omega

theorem p211For_M23 :
    P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .M23 := by
  intro X _ _ hsimp hC ⟨e⟩ p f hp hp2 hf a J D _ _ _ _ hJt hJF hDJ hDsyl hbound b K hb hb1
    hKC hK hKt
  exfalso
  have e' : ↥(generalizedFitting X) ≃* ↥Blueprint.NativeSporadic.M23 := e
  refine p211_of_fixed_lt hC (outer_solvable_of_equiv e' Sporadic.Schreier.at_m23_schreier.2.2)
    (fun α hα2 hα1 => ?_) hp hp2 hf hb hb1 hKC hK hKt
  have hβ2 : MulAut.congr e' α * MulAut.congr e' α = 1 := by rw [← map_mul, hα2, map_one]
  have hβ1 : MulAut.congr e' α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  rw [← card_fixed_congr e' α, GH74.Generic.S45.LAlt.m23_fixed_card (MulAut.congr e' α) hβ2 hβ1]
  norm_num

theorem p211For_J3 :
    P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .J3 := by
  intro X _ _ hsimp hC ⟨e⟩ p f hp hp2 hf a J D _ _ _ _ hJt hJF hDJ hDsyl hbound b K hb hb1
    hKC hK hKt
  exfalso
  refine p211_of_fixed_lt hC (outer_solvable_of_equiv e Sporadic.Schreier.AT_J3_Schreier.2)
    (fun α hα2 hα1 => ?_) hp hp2 hf hb hb1 hKC hK hKt
  have hcard : Nat.card {y : ↥(generalizedFitting X) // α y = y} =
      Nat.card ↥(GH74.Uniqueness.Bender.autFixed α) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => GH74.Uniqueness.Bender.mem_autFixed_iff.symm)
  rw [hcard]
  rcases GH74.Generic.S45.j3_fixed_card e α hα2 hα1 with h | h <;> omega

end P211Y

end CFSG.ComponentClassification.GSThmB
