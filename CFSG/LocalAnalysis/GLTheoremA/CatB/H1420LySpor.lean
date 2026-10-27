module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeRows
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420CoreDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)

theorem eq_of_three_mul_mcl_dvd (t : TauCeti.SporadicName)
    (h : 3 * sporOrd .McL ∣ sporOrd t) :
    t = .Co3 ∨ t = .Co1 ∨ t = .Ly ∨ t = .B ∨ t = .M := by
  revert h
  cases t <;> decide +kernel

theorem i1420SporLy_holds (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (hrow : ∀ t : TauCeti.SporadicName, (t = .Co3 ∨ t = .Co1 ∨ t = .B ∨ t = .M) →
      BMType.TypeRow (S8.sporIs .McL) t)
    {S : Type} [Group S] [Finite S] {t : TauCeti.SporadicName}
    (e : S ≃* (TauCeti.CFSGIndex.sporadic t).Group) {β : MulAut S} {J : Subgroup S}
    (hcore : I1420Core 3 3 .McL β J) : t = .Ly := by
  obtain ⟨hS, hnab, hβp, hβ1, -, hJ, ⟨eT⟩, -⟩ := hcore
  have hT : catalogIs (PSimple 3 J) (S8.sporIs .McL) := ⟨.sporadic .McL, rfl, ⟨eT⟩⟩
  have hcardT : Nat.card (PSimple 3 J) = sporOrd .McL :=
    (Nat.card_congr eT.toEquiv).trans (hOrd .McL)
  have h := prime_mul_card_pSimple_dvd_sporOrd hOrd hOut Nat.prime_three (by norm_num) e hS hnab
    hβp hβ1 hJ.1
  rw [hcardT] at h
  rcases eq_of_three_mul_mcl_dvd t h with ht | ht | ht | ht | ht
  · exact (hrow t (Or.inl ht) S ⟨e⟩ β hβp hβ1 J hJ hT).elim
  · exact (hrow t (Or.inr (Or.inl ht)) S ⟨e⟩ β hβp hβ1 J hJ hT).elim
  · exact ht
  · exact (hrow t (Or.inr (Or.inr (Or.inl ht))) S ⟨e⟩ β hβp hβ1 J hJ hT).elim
  · exact (hrow t (Or.inr (Or.inr (Or.inr ht))) S ⟨e⟩ β hβp hβ1 J hJ hT).elim

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
