module

public import CFSG.Dihedral.OriginalNormalizerOrientation
public import CFSG.Dihedral.PrimeClassPartition
public import CFSG.Dihedral.PrimeNormalizerQuotientAlternatives

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem primeSupport_eq_sigma_one_of_aligned_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) :
    primeSupport d.R = sigma 1 d.R := by
  ext p
  constructor
  · intro hp
    obtain ⟨P, hP⟩ := exists_isSylowIn p d.R
    have hPeq :=
      (d.original_prime_eq_three_and_sylow_eq_R_of_aSeven_model hR e p hp P hP).2
    have hstationary : IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G))) := by
      rw [hPeq]
      change IsSylowIn p d.R (oddCoreOf d.N)
      rw [d.N_oddCore_of_aligned_aSeven_model hR e ht]
      exact hPeq ▸ hP
    have hnotcomp : ¬ HasNormalTwoComplement (Subgroup.normalizer (P : Set G)) := by
      rw [hPeq]
      exact not_hasNormalTwoComplement_of_card_twentyFour d.N
        (d.N_quotient_card_of_aligned_aSeven_model hR e ht)
    exact (mem_sigma_iff_of_isSylowIn 1 p P d.R hP).mpr
      ⟨hp, hstationary, hnotcomp⟩
  · intro hp
    exact ((mem_sigma_iff 1 p d.R).mp hp).1

end CFSG.DihedralBlueprint.OriginalData
