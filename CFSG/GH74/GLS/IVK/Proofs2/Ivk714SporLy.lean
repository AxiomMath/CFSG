module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714SporM12J2
public import CFSG.GH74.Generic.S45.LSporLy
public import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.IVK Subgroup
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd.Spor (LyOuterTrivialInput)

theorem ivk714_layer_eq_top {M : Type*} [Group M] (hM : IsQuasisimple M) : layer M = ⊤ :=
  eq_top_iff.2 (CFSG.LocalCores.component_le_layer
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hM, Subgroup.IsSubnormal.top⟩)

theorem ivk714_ly
    (hLy : LyOuterTrivialInput) :
    Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .Ly) := by
  intro K _ _ hs hK z hz h
  obtain ⟨e⟩ := hK
  have hZ : Subgroup.center K = ⊥ := h.center_eq_bot
  obtain ⟨t, ht⟩ := CFSG.GH74.Generic.S45.mem_inner_of_inner_top e hLy z
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_conj hZ ht hz
  obtain ⟨hq, hcard2, ⟨E⟩⟩ :=
    CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ t ht2
  have hfix : fixedSubgroup K z = centralizer ({t} : Set K) := by
    subst ht
    ext x
    show MulAut.conj t x = x ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulAut.conj_apply]
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  have hqC : IsQuasisimple ↥(fixedSubgroup K z) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hfix).symm hq
  obtain ⟨o, ho, hocard⟩ := h.card_layer_eq
  rw [ivk714_layer_eq_top hqC, Subgroup.card_top,
    Nat.card_congr (MulEquiv.subgroupCongr hfix).toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(centralizer ({t} : Set K))),
    Nat.card_congr E.toEquiv, nat_card_alternatingGroup, hcard2] at hocard
  norm_num [Nat.factorial] at hocard
  obtain ⟨k, hk⟩ := ho
  omega

end CFSG.GH74.GLS.IVK.Proofs2
