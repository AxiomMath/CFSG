module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4FamModel
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint CFSG.Sporadic.Schreier

theorem Ivk93Cov.false_of_model_class {M : Type} [Group M] {P R A : Subgroup M} {tX : M}
    (hM : Ivk73Model P R A tX) {J : Type} [Group J] [Finite J] {x : J} {n : ℕ}
    {B : Subgroup J} (h : Ivk93Cov x n B) (θ : J ≃* ↥P) {g : M} (hg : g ∈ R)
    (hgt : ((θ x : ↥P) : M) = g * tX * g⁻¹) : False := by
  have hnorm : ∀ y ∈ P, g * y * g⁻¹ ∈ P := hM.autModel.conj_mem g hg
  have hnorm' : ∀ y ∈ P, g⁻¹ * y * g ∈ P := fun y hy => by
    simpa using hM.autModel.conj_mem g⁻¹ (R.inv_mem hg) y hy
  refine h.false_of_card_cent_lt ?_
  rw [GHInv.card_centralizer_eq_centralizerIn P θ x, hgt,
    GHInv.card_centralizerIn_conj_of_norm hnorm hnorm', hM.card_cent]
  norm_num

end CFSG.GH74.GLS.IVK.Proofs2
