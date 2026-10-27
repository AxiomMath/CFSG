module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Model
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4J2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor
  CFSG.GH74.GLS.IVK
open scoped commutatorElement

theorem j2_inv_cases :
    ∀ t ∈ j2P, orderOf t = 2 →
      (Group.IsPerfect ↥(centralizerIn j2P t) ∧ Nat.card ↥(centralizerIn j2P t) = 1920) ∨
        ∃ g ∈ j2R, t = g * tp 315 j2Row2B.rep * g⁻¹ := by
  intro t htP ht2
  rcases j2_cover t htP ht2 with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
  · left
    have hrA := j2_rows_spec.1 j2Row2A j2Row2A_mem
    have hCA : j2C j2Row2A = centralizerIn j2P (tp 315 j2Row2A.rep) := hrA.2.2.2.1
    have hperf : ⁅centralizerIn j2P (tp 315 j2Row2A.rep), centralizerIn j2P (tp 315 j2Row2A.rep)⁆ =
        centralizerIn j2P (tp 315 j2Row2A.rep) := by
      have hw := perfWit_of_all perfWit_j2_2A j2Row2A j2Row2A_mem j2Row2A_centOrder
      rw [← hCA]
      exact (perfWitOK_spec (by norm_num) hw).1
    have hperf' := GHInv.commutator_centralizerIn_conj hg hperf
    rw [← hgt] at hperf'
    have hcls : t ∈ CFSG.Sporadic.Schreier.conjClass j2P (tp 315 j2Row2A.rep) := ⟨g, hg, hgt⟩
    have hcard : Nat.card ↥(centralizerIn j2P t) = 1920 := by
      rw [GHInv.card_centralizerIn_eq_of_mem_conjClass j2P hcls]
      exact hrA.2.2.2.2.trans j2Row2A_centOrder
    exact ⟨Subgroup.isPerfect_iff.2 hperf', hcard⟩
  · exact Or.inr ⟨g, Subgroup.mem_sup_left hg, hgt⟩

theorem ivk95_j2 :
    Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .J2) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.J2 := e
  let θ : J ≃* ↥j2P := e'.trans j2PermEquiv
  rcases j2_inv_cases ((θ z : ↥j2P) : Equiv.Perm (Fin 315)) (θ z).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hz.ord) with
    ⟨hperf, hcard⟩ | ⟨g, hg, hgt⟩
  · have hperfJ := GHInv.isPerfect_centralizer_of_equiv j2P θ z (Subgroup.isPerfect_iff.1 hperf)
    have hc : Nat.card ↥(centralizer ({z} : Set J)) = 1920 := by
      rw [GHInv.card_centralizer_eq_centralizerIn j2P θ z]
      exact hcard
    exact hz.false_of_perfect hperfJ (Or.inl hc)
  · exact hz.false_of_model_class j2_model θ hg hgt

end CFSG.GH74.GLS.IVK.Proofs2
