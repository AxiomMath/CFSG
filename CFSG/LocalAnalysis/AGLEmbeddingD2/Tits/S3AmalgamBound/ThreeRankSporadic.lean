module

public import CFSG.RankThree.ThinCatalog.SporadicJ1
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.RankThree.PartOne.TCB.Sporadic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SporadicTwoRankThree

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor

open CFSG.Open CFSG.Blueprint TauCeti CFSG.RankThree.ThinCatalog CFSG.SectionRank

set_option linter.unusedSectionVars false


theorem two_le_pRank_three_sqtk {s : SporadicName} (hs : s ∈ sqtkSporadicNames) (hJ : s ≠ .J1)
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier s) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have h3p : Nat.Prime 3 := Nat.prime_three
  rw [← pRank_eq_open_pRank_top]
  cases s with
  | M11 => exact two_le_pRank_three_M11_sylow e
  | M12 =>
    have : Finite NativeSporadic.M12 := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := M12_sylow3_cubic_witness
    exact two_le_pRank_three_of_mulEquiv (G := NativeSporadic.M12) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)
  | M22 => exact two_le_pRank_three_M22_sylow e
  | M23 => exact two_le_pRank_three_M23_sylow e
  | M24 =>
    have : Finite NativeSporadic.M24 := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := M24_sylow3_cubic_witness
    exact two_le_pRank_three_of_mulEquiv (G := NativeSporadic.M24) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)
  | J1 => exact absurd rfl hJ
  | J2 =>
    have : Finite NativeSporadic.J2 := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := J2_sylow3_cubic_witness
    exact two_le_pRank_three_of_mulEquiv (G := NativeSporadic.J2) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)
  | J4 =>
    have : Finite NativeSporadic.J4 := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := J4_sylow3_cubic_witness
    exact two_le_pRank_three_of_mulEquiv (G := NativeSporadic.J4) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)
  | HS =>
    have : Finite NativeSporadic.HS := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, hy, hxy, hQ, -⟩ := HS_sylow3_square_witness
    exact two_le_pRank_three_of_mulEquiv (G := NativeSporadic.HS) e
      (two_le_pRank_of_square_witness h3p hx hy hxy hQ)
  | He =>
    have : Finite NativeSporadic.He := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := He_sylow3_cubic_witness
    exact two_le_pRank_three_of_mulEquiv (G := NativeSporadic.He) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)
  | Ru =>
    have : Finite NativeSporadic.Ru := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := Ru_sylow3_cubic_witness
    exact two_le_pRank_three_of_mulEquiv (G := NativeSporadic.Ru) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy)
  | _ => exact absurd hs (by simp [sqtkSporadicNames])

theorem two_le_pRank_three_sporadic_ne_J1
    {s : SporadicName} (hJ : s ≠ .J1)
    {S : Type} [Group S] [Finite S] [Nontrivial S]
    (hS : Nonempty (S ≃* (CFSGIndex.sporadic s).Group)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hbr := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
  by_cases hsq : s ∈ sqtkSporadicNames
  · obtain ⟨b⟩ := hbr
    obtain ⟨e⟩ := hS
    exact two_le_pRank_three_sqtk hsq hJ (e.trans b.symm)
  · by_cases hM : s = .M
    · subst hM
      obtain ⟨b⟩ := hbr
      obtain ⟨e⟩ := hS
      have e' : S ≃* NativeSporadic.Carrier .M := e.trans b.symm
      have : Nontrivial NativeSporadic.M := (show S ≃* NativeSporadic.M from e').symm.toEquiv.nontrivial
      obtain ⟨E, hE, hcard⟩ := M_nontrivial_elementary_three_rank_four
      exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.two_le_pRank_three_sporadic
        (s := .M) ⟨E, hE, 4, by norm_num, hcard⟩ ⟨b⟩ ⟨e⟩
    · exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.two_le_pRank_three_sporadic_all
        sporadicThreeRankWitnesses hsq hM hbr hS

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor
