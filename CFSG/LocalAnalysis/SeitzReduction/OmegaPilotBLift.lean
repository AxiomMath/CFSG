module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLift
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_pairTorus_of_odd_of_commute (hset : SeitzSetting G L) {n f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {x : G} (hx : x ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G))
    (hxo : Odd (orderOf x)) : x ∈ X := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact mem_of_odd_of_commute_pairTorus htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    (inf_centralizer_eq_zpowers_plus hset (by omega) hKc e htC ht) hq hn k e hX hDe x hx hxo

theorem mem_minusPairTorus_of_odd_of_commute (hset : SeitzSetting G L) {n f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    {x : G} (hx : x ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G))
    (hxo : Odd (orderOf x)) : x ∈ X := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact mem_of_odd_of_commute_minusPairTorus htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    (inf_centralizer_eq_zpowers_minus hset hn hKc hirr e htC ht) hq hn hirr k e hX hDe x hx hxo

theorem bLift_inputs_of_mulEquiv (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {C : Type*} [Group C] [Finite C] (e : L ≃* C) {XC DC : Subgroup C}
    (hA : centralizer (XC : Set C) = XC ⊔ DC) (hXD : XC ≤ centralizer (DC : Set C))
    (hXc : XC ≤ centralizer (XC : Set C)) (hDq : CFSG.IsQuasisimple DC)
    (hodd : Odd (Nat.card XC))
    (hC : ∀ β : MulAut C, (∀ x ∈ XC, β x = x) → (∀ x ∈ DC, β x = x) →
      ∃ x ∈ XC, β = MulAut.conj x)
    {X : Subgroup G} (hX : X = (XC.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (DC.map e.symm.toMonoidHom).map L.subtype) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D ∧
      ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
        Odd (orderOf c) → c ∈ X := by
  have hCtN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  refine ⟨hCtN, ?_, ?_, ?_⟩
  · rw [hX, F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hA hXD hXc hDq, hDe]
  · rw [hDe]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (LinearPilot.mapSymmMulEquiv e DC).symm hDq
  · rw [hX, hDe]
    exact mem_of_odd_of_commute_of_mulEquiv e hodd hC htC ht hCtN hK

section Plus

variable (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
  (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (k : Fin n)
  (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
  (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
  {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
  (htX : t ∈ centralizer (X : Set G))
  {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)

include hset hKc hq hn htC ht hX hDe

theorem bLift_inputs_pairTorus :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D ∧
      ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
        Odd (orderOf c) → c ∈ X := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, -, -, -, -, hD, -, hDq, -⟩ := neighbour_data_pairTorus hKc hq hn k e htC hX hDe
  exact ⟨CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard
    htC ht, hD, hDq, fun _ hc hco => mem_pairTorus_of_odd_of_commute hset hKc hq hn k e htC ht hX
      hDe hc hco⟩

theorem mem_center_of_mem_oddCore_of_commute_pairTorus :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) := by
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_pairTorus hset hKc hq hn k e htC ht hX hDe
  exact LinearPilot.mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem htC hLt htX hD hDq hXo

theorem hasBLift_pairTorus
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E := by
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_pairTorus hset hKc hq hn k e htC ht hX hDe
  exact LinearPilot.hasBLift_of_forall_odd_mem htC ht hLt htX hD hDq hXo hE htE hEt

theorem isComponent_oddCoreLift_pairTorus
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : CFSG.IsComponent E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (htE' : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) :
    HasBLift E ∧ CFSG.IsComponent (oddCoreLift E) ∧
      (oddCoreLift E).map (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = E ∧
      (oddCore (centralizer (X : Set G))).subgroupOf (oddCoreLift E) ≤ center (oddCoreLift E) := by
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_pairTorus hset hKc hq hn k e htC ht hX hDe
  exact LinearPilot.isComponent_oddCoreLift_of_forall_odd_mem htC ht hLt htX hD hDq hXo hE htE
    htE'

theorem hasBLift_sup_conj_pairTorus
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : ⁅Kb, Kb⁆ = Kb)
    (hcomm : ⁅Kb, Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥) :
    HasBLift (Kb ⊔ Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) ∧
      HasBLift Kb := by
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_pairTorus hset hKc hq hn k e htC ht hX hDe
  exact LinearPilot.hasBLift_sup_conj_of_forall_odd_mem htC ht hLt htX hD hDq hXo hKb hcomm

end Plus

theorem one_le_of_five_le {n : ℕ} (hn : 5 ≤ n) : 1 ≤ n := le_trans (by decide) hn

section Minus

variable (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
  (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
  (k : Fin (n - 1))
  (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_five_le hn) b c))
  {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
  (hX : X = ((minusPairTorus (K := K) (one_le_of_five_le hn) b c k).map
    e.symm.toMonoidHom).map L.subtype)
  (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
  (hDe : D = ((minusPairPerp (K := K) (one_le_of_five_le hn) b c k).map
    e.symm.toMonoidHom).map L.subtype)

include hset hKc hq hirr htC ht hX hDe

theorem bLift_inputs_minusPairTorus :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D ∧
      ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
        Odd (orderOf c) → c ∈ X := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, -, -, -, -, hD, -, hDq, -⟩ :=
    neighbour_data_minusPairTorus hKc hq hn hirr k e htC hX hDe
  exact ⟨CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard
    htC ht, hD, hDq, fun _ hc hco => mem_minusPairTorus_of_odd_of_commute hset hKc hq
      (by omega) hirr k e htC ht hX hDe hc hco⟩

theorem mem_center_of_mem_oddCore_of_commute_minusPairTorus :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) := by
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_minusPairTorus hset hKc hq hn hirr k e htC ht hX hDe
  exact LinearPilot.mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem htC hLt htX hD hDq hXo

theorem hasBLift_minusPairTorus
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E := by
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_minusPairTorus hset hKc hq hn hirr k e htC ht hX hDe
  exact LinearPilot.hasBLift_of_forall_odd_mem htC ht hLt htX hD hDq hXo hE htE hEt

theorem isComponent_oddCoreLift_minusPairTorus
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : CFSG.IsComponent E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (htE' : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) :
    HasBLift E ∧ CFSG.IsComponent (oddCoreLift E) ∧
      (oddCoreLift E).map (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = E ∧
      (oddCore (centralizer (X : Set G))).subgroupOf (oddCoreLift E) ≤ center (oddCoreLift E) := by
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_minusPairTorus hset hKc hq hn hirr k e htC ht hX hDe
  exact LinearPilot.isComponent_oddCoreLift_of_forall_odd_mem htC ht hLt htX hD hDq hXo hE htE
    htE'

theorem hasBLift_sup_conj_minusPairTorus
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : ⁅Kb, Kb⁆ = Kb)
    (hcomm : ⁅Kb, Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥) :
    HasBLift (Kb ⊔ Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) ∧
      HasBLift Kb := by
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_minusPairTorus hset hKc hq hn hirr k e htC ht hX hDe
  exact LinearPilot.hasBLift_sup_conj_of_forall_odd_mem htC ht hLt htX hD hDq hXo hKb hcomm

end Minus

end CFSG.SeitzReduction.OmegaPilot
