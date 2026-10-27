module

public import CFSG.GF2Type.Smith1979.W4InspDegSym
public import CFSG.GF2Type.Smith1979.W4InspDegSix
public import CFSG.GF2Type.Smith1979.W4InspDegLie

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Subgroup Module CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem concl_of_sym (hc : Ctx S g t)
    (h : FischerSym (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : Concl S g t := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  exfalso
  rcases hm with rfl | hm5
  · exact false_of_sym3 hc φ
  by_cases h5 : m = 5
  · subst h5
    exact false_of_sym5 hc φ
  by_cases h7 : 7 ≤ m
  · exact Setting.false_of_perm_ge_seven hc.haQ hc.hne (by have := hc.hw; omega) hc.ht hc.htA h7
      φ hφ
  obtain rfl : m = 6 := by omega
  exact false_of_sym6 hc φ hφ

theorem concl_of_sp (hc : Ctx S g t) (hdeg : ¬ S.IsNondeg12 g)
    (h : FischerSp (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : Concl S g t := by
  obtain ⟨m, hm, b, halt, hnd, hmod⟩ := h
  by_cases hm3 : 3 ≤ m
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hdeg, fuseCert_of_sp3 hc ⟨m, hm3, b, halt, hnd, hmod⟩⟩)))
  obtain rfl : m = 2 := by omega
  exfalso
  obtain ⟨-, hcls, -⟩ := Setting.isTransClass34_Ebar12 hc.ht hc.htA hc.hS
  obtain ⟨φ, hφ⟩ := S12Insp5.exists_perm_six_of_sp_two hcls halt hnd hmod
  exact false_of_sym6 hc φ hφ

theorem concl_of_o (hc : Ctx S g t)
    (h : FischerO (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : Concl S g t := by
  obtain ⟨m, hm, Q, hnd, hmin, hmod⟩ := h
  exfalso
  have hw := hc.hw
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · rcases (by omega : m = 2 ∨ m = 3) with rfl | rfl
    · exact false_of_orth2 hc hnd (hmin rfl) hmod
    · exact Setting.false_of_orth_six hc.haQ hc.hne (by omega) hc.ht hc.htA hnd hmod
  · exact Setting.false_of_orth_ge_four hc.haQ hc.hne (by omega) hc.ht hc.htA hm4 hnd hmod

theorem concl_of_psu (hc : Ctx S g t)
    (h : FischerPSU (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : Concl S g t :=
  (false_of_psu hc h).elim

theorem concl_of_f3 (hc : Ctx S g t)
    (h : FischerF3 (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : Concl S g t :=
  (false_of_f3 hc h).elim

theorem concl_of_fi (hc : Ctx S g t)
    (h : FischerFi (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : Concl S g t :=
  (false_of_fi hc h).elim

end CFSG.GF2Type.Smith1979.W4Insp
