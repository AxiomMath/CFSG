module

public import CFSG.Dihedral.OriginalASevenOddCore
public import CFSG.Dihedral.OrderTwentyFourCoordinates

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem local_index_eq_three_of_aligned_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) :
    (d.C.subgroupOf d.N).index = 3 := by
  have hC : Nat.card (d.C.subgroupOf d.N) = 24 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.centralizer_le_normalizer).toEquiv).trans
      (d.C_card_of_aSeven_model hR e)
  have h := (d.C.subgroupOf d.N).index_mul_card
  rw [hC, d.N_card_of_aligned_aSeven_model hR e ht] at h
  omega

theorem every_coordinate_of_aligned_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t)
    (w : CoordinateWitness (d.N ⧸ Assembly.oddCore d.N)) :
    w.rho.range = pGammaL2PGLRange w.K ∧
    ∀ epsilon : ℤ, (epsilon = 1 ∨ epsilon = -1) →
      (Nat.card w.K : ℤ) % 4 = epsilon % 4 →
      (Nat.card w.K : ℤ) - epsilon = (2 : ℤ) ^ (d.n - 1) ∧
      (d.C.subgroupOf d.N).index =
        ((Nat.card w.K : ℤ) * ((Nat.card w.K : ℤ) + epsilon) / 2).toNat ∧
      d.C.index = d.N.index * (d.C.subgroupOf d.N).index ∧
      (d.C.subgroupOf d.N).index ∣ d.C.index := by
  have hquot := d.N_quotient_card_of_aligned_aSeven_model hR e ht
  have hq := w.card_eq_three_of_card_twentyFour hquot
  refine ⟨w.range_eq_pgl_of_card_twentyFour hquot, ?_⟩
  intro epsilon hsign hcong
  have heps : epsilon = -1 := by
    rcases hsign with hplus | hminus
    · rw [hq, hplus] at hcong
      norm_num at hcong
    · exact hminus
  have hlocal := d.local_index_eq_three_of_aligned_aSeven_model hR e ht
  have hglobal : d.C.index = d.N.index * (d.C.subgroupOf d.N).index := by
    change d.C.index = d.N.index * d.C.relIndex d.N
    simpa only [Nat.mul_comm] using
      (Subgroup.relIndex_mul_index d.centralizer_le_normalizer).symm
  refine ⟨?_, ?_, hglobal, Subgroup.relIndex_dvd_index_of_le d.centralizer_le_normalizer⟩
  · rw [hq, heps, d.n_eq_three_of_aSeven_model e]
    norm_num
  · rw [hq, heps, hlocal]
    norm_num

end CFSG.DihedralBlueprint.OriginalData
