module

import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.ComponentClassification.CanonicalPrimeComponentLift
import CFSG.Walter.AStar.Subnormal
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.Holt.General

open CFSG.LocalCores CFSG.ComponentClassification.CatalogueBPrimeJoin

private theorem false_of_sylow_le_center {K : Type*} [Group K] [Finite K] (hK : IsQuasisimple K)
    (T : Sylow 2 K) (hT : (T : Subgroup K) ≤ Subgroup.center K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hs, a, b, hab⟩ := hK
  have hodd : Odd (Nat.card (K ⧸ Subgroup.center K)) :=
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp T.not_dvd_index)).of_dvd_nat
      (Subgroup.index_dvd_of_le hT)
  have hsolv : Group.IsSolvable (K ⧸ Subgroup.center K) := CFSG.Milestones.odd_order_solvable hodd
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_isPComponent_of_le_centralizer {S : Sylow 2 G} {z : G}
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer {z}) {B : Subgroup G}
    (hB : IsPComponent 2 B) : z ∈ Subgroup.normalizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 G)
  obtain ⟨K, hK, hBsub, hBK, -⟩ := id hB
  let c : G ⧸ pPrimeCore 2 G ≃* G ⧸ pPrimeCore 2 G := MulAut.conj (π z)
  have hK' : IsComponent (K.map c.toMonoidHom) := isComponent_map_mulEquiv c hK
  have hcomp : π.comp (MulAut.conj z).toMonoidHom = c.toMonoidHom.comp π := by
    ext x
    simp [c, MulAut.conj_apply]
  have hmap : (B.map (MulAut.conj z).toMonoidHom).map π = K.map c.toMonoidHom := by
    rw [← hBK, Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rcases distinct_components_commute hK hK' with hKK | hcomm
  ·
    obtain ⟨-, -, hle, huniq⟩ := (canonical_prime_component_lift 2).1 K hK
    have hle' := hle _ (hBsub.map (MulAut.conj z).surjective) (hmap.trans hKK.symm)
    rw [← huniq B hB hBK] at hle'
    exact (Subgroup.eq_of_le_of_card_ge hle'
      (Subgroup.card_map_of_injective (MulAut.conj z).injective).le).symm
  ·
    exfalso
    obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hBsub
    subst hBK
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    refine false_of_sylow_le_center hK.1
      (P.mapSurjective (MonoidHom.subgroupMap_surjective π B)) ?_
    rw [Sylow.coe_mapSurjective]
    rintro _ ⟨y, hy, rfl⟩
    have hyS : (y : G) ∈ (S : Subgroup G) ⊓ B := hP ▸ Subgroup.mem_map_of_mem B.subtype hy
    have hyz : z * (y : G) * z⁻¹ = y := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hSz hyS.1), mul_inv_cancel_right]
    have hyK' : π y ∈ (B.map π).map c.toMonoidHom := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem π ⟨y, y.2, by rw [MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, hyz]⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcen g.2) _ hyK').symm

end CFSG.Holt.General
