module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Char

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem cf67_U3_char_of_lieModel {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hLie : LieModel Y .PSU 3 p f) (hs : IsSimpleGroup Y) (hn : ∃ a b : Y, a * b ≠ b * a)
    {V Z : Subgroup (MulAut Y)} (h2 : N2Cfg Y p V Z) (h3 : N3Full Y V Z) : False := by
  obtain ⟨hp, hf, F, _, _, hF, ⟨e₀⟩⟩ := Generic.lieModel_psu_data hLie
  have h : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  exact cf67_U3_char hp2 (e₀.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm) hs hn h2 h3

end CFSG.GH74.GLS.Stage2.Bender.Thm1
