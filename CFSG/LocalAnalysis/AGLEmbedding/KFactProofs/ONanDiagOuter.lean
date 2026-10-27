module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterUni
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open TauCeti CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem diagOuterLinUni : DiagOuterLinUni := by
  rintro ⟨d, hv⟩ hd
  cases d with
  | A r q =>
    obtain ⟨h3n, h3q⟩ := hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hn : 3 ≤ r + 1 := Nat.le_of_dvd (by omega) h3n
    have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', PrimePower.card_def]
    exact HasDiagOuterThree.of_mulEquiv
      ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1)
          (GaloisField q.p q.exponent))).symm
      (hasDiagOuterThree_projectiveSL hn h3n (by rw [hcard]; exact h3q))
  | twistedA r q =>
    obtain ⟨h3n, h3q⟩ := hd
    have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hn : 3 ≤ r + 1 := Nat.le_of_dvd (by omega) h3n
    rw [PrimePower.card_def] at h3q
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
      (G := ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) (MulEquiv.refl _)
    obtain ⟨-, F, _, _, hFcard, ⟨e⟩⟩ := hm
    have hU : UnitaryFieldData q.p q.exponent F :=
      ⟨q.prime_p, q.exponent_pos, by rw [hFcard, ← pow_mul, mul_comm]⟩
    have hq : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨h1, h2⟩
      have := hrange.2 (by omega)
      rw [PrimePower.card_def] at this
      omega
    exact HasDiagOuterThree.of_mulEquiv
      (e.trans (unitaryPSUEquiv hU (by omega)).symm).symm
      (hasDiagOuterThree_unitaryPSU hU hn hq h3n h3q)
  | _ => exact False.elim hd

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
