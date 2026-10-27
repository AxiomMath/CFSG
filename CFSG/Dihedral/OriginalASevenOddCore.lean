module

public import CFSG.Dihedral.OriginalCosetNormalizer
public import CFSG.Dihedral.GorensteinWalter.ASevenNormalizerOddCore
public import CFSG.Assembly.OddCoreBalance

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem N_oddCore_of_aligned_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) : oddCoreOf d.N = d.R := by
  let f : d.N ≃* a7ThreeNormalizer := (e.subgroupMap d.N).trans
    (MulEquiv.subgroupCongr (d.N_map_eq_a7ThreeNormalizer hR e ht))
  have hf : a7ThreeNormalizer.subtype.comp f.toMonoidHom =
      e.toMonoidHom.comp d.N.subtype := by
    ext x
    rfl
  have hcore : (Assembly.oddCore d.N).map f.toMonoidHom =
      Assembly.oddCore a7ThreeNormalizer := by
    rw [Assembly.Dichotomy.oddCore_eq_pPrimeCore, Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    exact CFSG.pPrimeCore_map_iso 2 f
  have hmap : (oddCoreOf d.N).map e.toMonoidHom = a7U := by
    change ((Assembly.oddCore d.N).map d.N.subtype).map e.toMonoidHom = a7U
    rw [Subgroup.map_map, ← hf, ← Subgroup.map_map, hcore,
      a7ThreeNormalizer_oddCore_map]
  have hsame : (oddCoreOf d.N).map e.toMonoidHom = d.R.map e.toMonoidHom :=
    hmap.trans (d.R_map_eq_a7U hR e ht).symm
  have h := congrArg (Subgroup.comap e.toMonoidHom) hsame
  simpa only [Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective] using h

theorem N_quotient_card_of_aligned_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) :
    Nat.card (d.N ⧸ Assembly.oddCore d.N) = 24 := by
  have hcore : Nat.card (Assembly.oddCore d.N) = 3 := by
    have h := Subgroup.card_map_of_injective (K := Assembly.oddCore d.N) d.N.subtype_injective
    change Nat.card (oddCoreOf d.N) = Nat.card (Assembly.oddCore d.N) at h
    rw [d.N_oddCore_of_aligned_aSeven_model hR e ht, d.R_card_of_aSeven_model hR e] at h
    exact h.symm
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Assembly.oddCore d.N)
  rw [d.N_card_of_aligned_aSeven_model hR e ht, hcore] at h
  omega

end CFSG.DihedralBlueprint.OriginalData
