module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420CoreDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Co1RowArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem co1Row_spor_of_rows (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (h22 : K14Spor.CardRow (sporOrd .Suz) .Fi22) (h23 : K14Spor.CardRow (sporOrd .Suz) .Fi23)
    (h24 : K14Spor.CardRow (sporOrd .Suz) .Fi24Prime) (hB : K14Spor.CardRow (sporOrd .Suz) .B)
    (hM : ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .M).Group) → ∀ β : MulAut S, β ^ 3 = 1 →
        β ≠ 1 → ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J →
          catalogIs (PSimple 3 J) (S8.sporIs .Suz) → False)
    (S : Type) [Group S] [Finite S] (t : TauCeti.SporadicName)
    (e : S ≃* (TauCeti.CFSGIndex.sporadic t).Group) (β : MulAut S) (J : Subgroup S)
    (hcore : I1420Core 3 3 .Suz β J) : t = .Co1 := by
  obtain ⟨hS, hnab, hβp, hβ1, -, hJ, ⟨eT⟩, -⟩ := hcore
  have hcard : Nat.card (PSimple 3 J) = sporOrd .Suz :=
    (Nat.card_congr eT.toEquiv).trans (hOrd .Suz)
  have hdvd := prime_mul_card_pSimple_dvd_sporOrd hOrd hOut Nat.prime_three (by norm_num) e hS
    hnab hβp hβ1 hJ.1
  rw [hcard] at hdvd
  rcases eq_survivor_of_three_mul_suz_dvd t hdvd with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd hcard (h22 S ⟨e⟩ β hβp hβ1 J hJ)
  · exact absurd hcard (h23 S ⟨e⟩ β hβp hβ1 J hJ)
  · exact absurd hcard (h24 S ⟨e⟩ β hβp hβ1 J hJ)
  · exact absurd hcard (hB S ⟨e⟩ β hβp hβ1 J hJ)
  · exact (hM S ⟨e⟩ β hβp hβ1 J hJ ⟨.sporadic .Suz, rfl, ⟨eT⟩⟩).elim

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
