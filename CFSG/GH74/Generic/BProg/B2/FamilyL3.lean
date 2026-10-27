module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3Nine
public import CFSG.GH74.Generic.BProg.B2.GenLocU3
public import CFSG.GH74.Generic.BProg.B2.FamilyGeneric
public import CFSG.GH74.Generic.BProg.B1.Stage3aRank

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

namespace FamilyL3

section Lin


theorem genProp_psl3_ne_five {J : Type} [Group J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : 3 < p ^ f) (h5 : p ^ f ≠ 5) (hJ : LieModel J .PSL 3 p f) : GenProp J := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hmod := Nat.odd_iff.1 hodd
  by_cases h7 : p ^ f = 7
  · exact genProp_psl3_seven h7 hJ
  by_cases h9 : p ^ f = 9
  · exact genProp_psl3_nine h9 hJ
  exact genProp_psl3_lin hp hp2 (by omega) hJ

theorem genProp_psl3_of_sq {J : Type} [Group J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hJ : LieModel J .PSL 3 p (2 * f)) : GenProp J := by
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hge : 9 ≤ p ^ (2 * f) := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by omega)
  exact genProp_psl3_ne_five hp hp2 (by omega) (by omega) hJ

theorem genProp_psu3_ge11 {J : Type} [Group J] [Finite J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h11 : 11 ≤ p ^ f) (hJ : LieModel J .PSU 3 p f) : GenProp J :=
  fun _ _ _ α hA => gammaAct_psu3 hp hp2 h11 hJ α hA

end Lin

end FamilyL3

section Lin


theorem weakSig2NormG4_pul3sq {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h : PuL3sq J) : WeakSig2NormG4 J := by
  obtain ⟨p, f, hp, hp2, hf, hJ⟩ := h
  exact FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq
    (GenLoc.genLoc4 (GenProp.genLoc (FamilyL3.genProp_psl3_of_sq hp hp2 hf hJ)))

theorem genLoc4_qShape3
    (hL5 : ∀ (J : Type) [Group J] {p f : ℕ}, p ^ f = 5 → LieModel J .PSL 3 p f → GenLoc J)
    (hU : ∀ (J : Type) [Group J] [Finite J] {p f : ℕ},
      (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) → LieModel J .PSU 3 p f → GenProp J)
    {J : Type} [Group J] [Finite J] (h : QShape3 J) : GenLoc4 J := by
  obtain ⟨p, f, hp, hp2, h3, hJ | hJ⟩ := h
  · by_cases h5 : p ^ f = 5
    · exact GenLoc.genLoc4 (hL5 J h5 hJ)
    · exact GenLoc.genLoc4 (GenProp.genLoc (FamilyL3.genProp_psl3_ne_five hp hp2 h3 h5 hJ))
  · have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hmod := Nat.odd_iff.1 hodd
    by_cases hs : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9
    · exact GenLoc.genLoc4 (GenProp.genLoc (hU J hs hJ))
    · exact GenLoc.genLoc4 (GenProp.genLoc (FamilyL3.genProp_psu3_ge11 hp hp2 (by omega) hJ))

theorem weakSig2NormG4_qShape3
    (hL5 : ∀ (J : Type) [Group J] {p f : ℕ}, p ^ f = 5 → LieModel J .PSL 3 p f → GenLoc J)
    (hU : ∀ (J : Type) [Group J] [Finite J] {p f : ℕ},
      (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) → LieModel J .PSU 3 p f → GenProp J)
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : QShape3 J) : WeakSig2NormG4 J :=
  FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq (genLoc4_qShape3 hL5 hU h)

theorem weakSig2TwoG4_qShape3
    (hL5 : ∀ (J : Type) [Group J] {p f : ℕ}, p ^ f = 5 → LieModel J .PSL 3 p f → GenLoc J)
    (hU : ∀ (J : Type) [Group J] [Finite J] {p f : ℕ},
      (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) → LieModel J .PSU 3 p f → GenProp J)
    {J : Type} [Group J] [Finite J] (hs : IsSimpleGroup J) (hq : IsQuasisimple J)
    (h : QShape3 J) : WeakSig2TwoG4 J :=
  FamilyGeneric.weakSig2TwoG4_of_genLoc4_simple hs hq (genLoc4_qShape3 hL5 hU h)

theorem genProp_qShape3SD
    (hU : ∀ (J : Type) [Group J] [Finite J] {p f : ℕ},
      (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) → LieModel J .PSU 3 p f → GenProp J)
    {J : Type} [Group J] [Finite J] (h : B1.QShape3SD J) : GenProp J := by
  obtain ⟨p, f, hp, hp2, h3, ⟨hJ, h4⟩ | ⟨hJ, h4⟩⟩ := h
  · exact FamilyL3.genProp_psl3_ne_five hp hp2 h3 (by omega) hJ
  · have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hmod := Nat.odd_iff.1 hodd
    by_cases hs : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9
    · exact hU J hs hJ
    · exact FamilyL3.genProp_psu3_ge11 hp hp2 (by omega) hJ

end Lin

end CFSG.GH74.Generic.BProg.B2
