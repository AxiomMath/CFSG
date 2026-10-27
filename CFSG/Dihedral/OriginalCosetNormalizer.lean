module

public import CFSG.Dihedral.OriginalCosetModel

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem N_map_eq_a7ThreeNormalizer (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) :
    d.N.map e.toMonoidHom = a7ThreeNormalizer := by
  change (Subgroup.normalizer (d.R : Set G)).map e.toMonoidHom = _
  rw [Subgroup.map_normalizer_eq_of_bijective d.R e.bijective, d.R_map_eq_a7U hR e ht]
  rfl

theorem N_card_of_aligned_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) : Nat.card d.N = 72 := by
  rw [← Subgroup.card_map_of_injective (K := d.N) (f := e.toMonoidHom) e.injective,
    d.N_map_eq_a7ThreeNormalizer hR e ht, a7ThreeNormalizer_card]

theorem C_card_of_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) : Nat.card d.C = 24 := by
  rw [d.centralizer_card, d.R_card_of_aSeven_model hR e, d.n_eq_three_of_aSeven_model e]
  decide

theorem N_index_of_aligned_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) : d.N.index = 35 := by
  have h := d.N.card_mul_index
  rw [d.N_card_of_aligned_aSeven_model hR e ht, group_card_of_aSeven_model e] at h
  omega

theorem C_index_of_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) : d.C.index = 105 := by
  have h := d.C.card_mul_index
  rw [d.C_card_of_aSeven_model hR e, group_card_of_aSeven_model e] at h
  omega

theorem commonE_index_of_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) : (d.commonE.subgroupOf d.R).index = 3 := by
  rw [d.commonE_eq_bot_of_aSeven_model e, Subgroup.bot_subgroupOf, Subgroup.index_bot,
    d.R_card_of_aSeven_model hR e]

theorem quotient_card_of_aligned_aSeven_model (hp : d.PureProjectiveNormalizer)
    (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) :
    Nat.card (d.N ⧸ Assembly.oddCore d.N) = 24 := by
  have hcore : Nat.card (Assembly.oddCore d.N) = 3 := by
    have h := Subgroup.card_map_of_injective (K := Assembly.oddCore d.N) d.N.subtype_injective
    change Nat.card (oddCoreOf d.N) = Nat.card (Assembly.oddCore d.N) at h
    rw [hp.2.1, d.R_card_of_aSeven_model hR e] at h
    exact h.symm
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Assembly.oddCore d.N)
  rw [d.N_card_of_aligned_aSeven_model hR e ht, hcore] at h
  omega

theorem coordinate_card_of_aligned_aSeven_model (hp : d.PureProjectiveNormalizer)
    (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t)
    (w : CoordinateWitness (d.N ⧸ Assembly.oddCore d.N)) : Nat.card w.K = 3 := by
  have hrange : w.rho.range = pGammaL2PGLRange w.K := (hp.2.2.2.1 w).1
  let eta := (MonoidHom.ofInjective w.injective).trans
    (MulEquiv.subgroupCongr hrange) |>.trans (pGammaL2PGLRangeEquiv w.K).symm
  have h : Nat.card w.K * (Nat.card w.K ^ 2 - 1) = 24 := by
    rw [← pgl2_card_formula, ← Nat.card_congr eta.toEquiv]
    exact d.quotient_card_of_aligned_aSeven_model hp hR e ht
  generalize Nat.card w.K = q at h ⊢
  have hqle : q < 4 := by
    by_contra hn
    have h4 : 4 ≤ q := by omega
    have h16 : 16 ≤ q ^ 2 := by nlinarith
    have h60 : 60 ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h4 (by omega : 15 ≤ q ^ 2 - 1)
    omega
  interval_cases q
  all_goals try norm_num at h
  rfl

end CFSG.DihedralBlueprint.OriginalData
