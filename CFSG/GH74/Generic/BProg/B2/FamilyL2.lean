module

public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.GH74.Generic.BProg.B2.GenLocL2Fam
public import CFSG.GH74.Generic.BProg.B2.FamilyGeneric
public import CFSG.GH74.Generic.BProg.B2.FamilyOddCentre
public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyList
public import CFSG.GH74.Generic.BProg.B2.SDOrders

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open scoped MatrixGroups

namespace FamilyL2

theorem five_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : p ^ f ≠ 3) :
    5 ≤ p ^ f := by
  have hoddq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hmod := Nat.odd_iff.1 hoddq
  omega

end FamilyL2

theorem weakSig2NormG4_of_psl2Cover
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : LieModel (J ⧸ center J) .PSL 2 p f) : WeakSig2NormG4 J := by
  obtain ⟨-, hf, -, hF3, -⟩ := CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hJ
  have h5 := FamilyL2.five_le_pow hp hp2 hf hF3
  rcases l2_cover_cases hq hp hp2 hJ with hz | ⟨-, hJ'⟩ | ⟨-, K, _, _, hK, ⟨e⟩⟩
  · exact weakSig2NormG4_of_odd_central hz
  · exact FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq
      (GenLoc.genLoc4 (genLoc_psl2 hp hp2 h5 hJ'))
  · exact FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq
      (GenLoc.genLoc4 (genLoc_sl2 hp hp2 hK h5 e))

theorem weakSig2NormG4_of_listedRankOne
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : ListedRankOne J) :
    WeakSig2NormG4 J := by
  obtain ⟨-, p, f, hp, hp2, -, hJ⟩ := h
  exact weakSig2NormG4_of_psl2Cover hq hp hp2 hJ

theorem weakSig2NormG4_of_smallLie_l2
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel (J ⧸ center J) .PSL 2 p f) :
    WeakSig2NormG4 J := by
  obtain ⟨p, f, hp, hp2, -, hJ⟩ := h
  exact weakSig2NormG4_of_psl2Cover hq hp hp2 hJ

theorem smallLie_weakSig_of
    (hL3three : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J →
      LieModel (J ⧸ center J) .PSL 3 3 1 → WeakSig2NormG4 J)
    (hL3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J →
      QShape3 (J ⧸ center J) → WeakSig2NormG4 J)
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : SD2.SmallLie J) :
    WeakSig2NormG4 J := by
  rcases h with h2 | h3 | hsh
  · exact weakSig2NormG4_of_smallLie_l2 hq h2
  · exact hL3three J hq h3
  · exact hL3 J hq hsh

end CFSG.GH74.Generic.BProg.B2
