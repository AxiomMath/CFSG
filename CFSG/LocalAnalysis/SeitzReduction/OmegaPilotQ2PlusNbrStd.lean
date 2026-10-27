module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbr
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (HasBLift)

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {m : ℕ}

theorem neighbour_data_plusAnisoTorus (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (plusAnisoQuad K m b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) {X : Subgroup G}
    (hX : X = ((plusAnisoTorus m hirr).map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((plusAnisoPerp (K := K) m b c).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ X ≤ centralizer (X : Set G) ∧ Odd (Nat.card X) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ := by
  subst hX hDe
  have hDq := isQuasisimple_plusAnisoPerp hm hirr
  obtain ⟨hodd, hXX, hXD⟩ := plusAnisoTorus_facts (m := m) hirr
  set ψ := LinearPilot.mapSymmMulEquiv e (plusAnisoPerp (K := K) m b c) with hψ
  refine ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    LinearPilot.map_symm_le_centralizer_map_symm e hXX,
    (LinearPilot.card_map_symm e _).symm ▸ hodd,
    (F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e (centralizer_plusAnisoTorus (by omega) hirr)
      hXD hXX hDq).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e (le_centralizer_iff.mp hXD))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hDq, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hx' : ψ x ∈ center (plusAnisoPerp (K := K) m b c) := by
    rw [← map_center_eq ψ]
    exact ⟨x, hx, rfl⟩
  rw [center_plusAnisoPerp hm hirr, mem_bot] at hx'
  rw [mem_bot, ← ψ.symm_apply_apply x, hx', map_one]

theorem lieModel_map_plusAnisoPerp {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (plusAnisoQuad K m b c)) {D : Subgroup G}
    (hDe : D = ((plusAnisoPerp (K := K) m b c).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Blueprint.LieModel D .POmegaMinus (m + 1) 2 f ∧ Group.IsSolvable (Outer D) := by
  subst hDe
  set ψ := LinearPilot.mapSymmMulEquiv e (plusAnisoPerp (K := K) m b c) with hψ
  exact ⟨lieModel_of_mulEquiv ψ.symm (lieModel_plusAnisoPerp hKc hm hirr),
    isSolvable_outer_of_mulEquiv_minus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc
      hirr (ψ.trans (plusAnisoPerpProjEquiv hm hirr))⟩

variable [Finite G]

theorem neighbour_standard_plusAnisoTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (plusAnisoQuad K m b c)) {X : Subgroup G}
    (hX : X = ((plusAnisoTorus m hirr).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((plusAnisoPerp (K := K) m b c).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  obtain ⟨hodd, hXX, hXD⟩ := plusAnisoTorus_facts (m := m) hirr
  exact neighbour_standard_of_mulEquiv_of_eq_conj hL htC ht hK e
    (centralizer_plusAnisoTorus (by omega) hirr) hXD hXX (isQuasisimple_plusAnisoPerp hm hirr)
    hodd (fun _ hX hD => exists_mem_plusAnisoTorus_eq_conj hm hirr hX hD) hX htX hDe

theorem bLift_inputs_plusAnisoTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (plusAnisoQuad K m b c)) {X : Subgroup G}
    (hX : X = ((plusAnisoTorus m hirr).map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((plusAnisoPerp (K := K) m b c).map e.symm.toMonoidHom).map L.subtype) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D ∧
      ∀ x ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
        Odd (orderOf x) → x ∈ X := by
  obtain ⟨hodd, hXX, hXD⟩ := plusAnisoTorus_facts (m := m) hirr
  exact bLift_inputs_of_mulEquiv hL htC ht hK e (centralizer_plusAnisoTorus (by omega) hirr) hXD
    hXX (isQuasisimple_plusAnisoPerp hm hirr) hodd
    (fun _ hX hD => exists_mem_plusAnisoTorus_eq_conj hm hirr hX hD) hX hDe

end CFSG.SeitzReduction.OmegaPilot
