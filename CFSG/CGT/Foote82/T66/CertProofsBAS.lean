module

public import CFSG.CGT.Foote82.T66.CitedBAS
public import CFSG.CGT.Foote82.T66.FaithfulImage
import CFSG.LocalAnalysis.EvenBN.Tits.I21LModAHeart

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

theorem basA6NoSix_holds : BASA6NoSix := by
  intro V _ _ _ L ⟨e⟩ hirr hdim
  haveI := L13Aux.finite_tildeV L
  have hY := L13Aux.range_isIrr hirr
  haveI : Nontrivial (TildeV L) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hY.2.1.ne (Subsingleton.elim _ _)
  let φ : alternatingGroup (Fin 6) →* GLV (TildeV L) := (L13Aux.tildeRep L).comp e.symm.toMonoidHom
  have h := CFSG.LocalAnalysis.EvenBN.Tits.I21L.modA_finrank_irred φ (fun U hU => by
    have hinv : Invariant (L13Aux.tildeRep L).range U := by
      rintro k ⟨ℓ, rfl⟩ u hu
      have := hU (e ℓ) u hu
      simpa [φ] using this
    exact hY.2.2 U hinv bot_le le_top)
  omega

end CFSG.CGT.Foote82
