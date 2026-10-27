module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldSL2
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamNormalize
import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwistSp4
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR8RootTorus
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Model

variable {F : Type} [Field F] {n : ℕ}

theorem spFieldMap_simpleRootHom_sl2Upper (σ : F →+* F) (j : Fin n) (c : F) :
    spFieldMap n σ (simpleRootHom F j (sl2Upper c)) = simpleRootHom F j (sl2Upper (σ c)) := by
  rw [spFieldMap_eq_statedSpMap]
  by_cases h : j.val + 1 < n
  · rw [simpleRootHom_of_lt h, shortBlock_sl2Upper, F4Pilot.statedSpMap_elt,
      ← shortBlock_sl2Upper]
  · rw [simpleRootHom_of_not_lt h, longBlock_sl2Upper, F4Pilot.statedSpMap_elt,
      ← longBlock_sl2Upper]

theorem simpleRootHom_sl2Upper_mul_inv (j : Fin n) (a b : F) :
    simpleRootHom F j (sl2Upper a) * (simpleRootHom F j (sl2Upper b))⁻¹ =
      simpleRootHom F j (sl2Upper (a - b)) := by
  have hinv : (sl2Upper b)⁻¹ = sl2Upper (-b) :=
    inv_eq_of_mul_eq_one_right (by
      rw [← E8Pilot.sl2Upper_add, add_neg_cancel, E8Pilot.sl2Upper_zero])
  rw [← map_inv, ← map_mul, hinv, ← E8Pilot.sl2Upper_add, ← sub_eq_add_neg]

theorem orderOf_simpleRootHom_sl2Upper [CharP F 2] (j : Fin n) {c : F} (hc : c ≠ 0) :
    orderOf (simpleRootHom F j (sl2Upper c)) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_mul, ← E8Pilot.sl2Upper_add, CharTwo.add_self_eq_zero, E8Pilot.sl2Upper_zero,
      map_one]
  · intro h
    rw [← map_one (simpleRootHom F j), ← E8Pilot.sl2Upper_zero] at h
    exact hc (E8Pilot.sl2Upper_injective (simpleRootHom_injective j h))

end Model

section Commutator

theorem false_of_mk_mem_center_of_orderOf_commutator {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {t g : G} (htH : t ∈ H) (hgH : g ∈ H)
    (hord : orderOf (t * g * t⁻¹ * g⁻¹) = 2)
    (hcen : QuotientGroup.mk' (oddCore H) ⟨t, htH⟩ ∈ center (H ⧸ oddCore H)) : False := by
  set tH : H := ⟨t, htH⟩ with htHdef
  set gH : H := ⟨g, hgH⟩ with hgHdef
  have hwH : tH * gH * tH⁻¹ * gH⁻¹ ∈ oddCore H := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (oddCore H) (tH * gH * tH⁻¹ * gH⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [← mem_center_iff.1 hcen (QuotientGroup.mk' (oddCore H) gH)]
    group
  have hord' : orderOf (tH * gH * tH⁻¹ * gH⁻¹) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hord
  have hdvd := (oddCore H).orderOf_dvd_natCard hwH
  rw [hord'] at hdvd
  have hO : Odd (Nat.card (oddCore H)) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 hdvd)

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {k : Fin n}

theorem FieldNeighbourParam.false_of_mk_mem_center [CharP F 2]
    (P : FieldNeighbourParam e t ι σ k) (hK : 4 ≤ Nat.card K) (hσ : σ ≠ 1) {j : Fin n}
    (hkj : k ≠ j) (hk1 : j.val + 1 < n → k.val ≠ j.val + 1) {H : Subgroup G} (htH : t ∈ H)
    (hMH : pieceCore e ({j} : Finset (Fin n)) ≤ H)
    (hcen : QuotientGroup.mk' (oddCore H) ⟨t, htH⟩ ∈ center (H ⧸ oddCore H)) : False := by
  obtain ⟨c, hc⟩ : ∃ c : F, σ c ≠ c := by
    by_contra hall
    push Not at hall
    exact hσ (RingEquiv.ext hall)
  have hyJ : simpleRootHom F j (sl2Upper c) ∈ simpleRootSL2 F j := ⟨_, rfl⟩
  set y : spBlock F ({k}ᶜ : Finset (Fin n)) :=
    ⟨simpleRootHom F j (sl2Upper c), simpleRootSL2_le_spBlock_compl hkj hk1 hyJ⟩ with hy
  set w : spBlock F ({k}ᶜ : Finset (Fin n)) :=
    fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) y * y⁻¹ with hw
  have hwval : (w : StatedSp n F) = simpleRootHom F j (sl2Upper (σ c - c)) := by
    rw [hw, Subgroup.coe_mul, Subgroup.coe_inv, coe_fieldBlockSp_apply, hy]
    change spFieldMap n σ.toRingHom (simpleRootHom F j (sl2Upper c)) *
      (simpleRootHom F j (sl2Upper c))⁻¹ = _
    rw [spFieldMap_simpleRootHom_sl2Upper, simpleRootHom_sl2Upper_mul_inv]
    rfl
  have hw2 : orderOf w = 2 := by
    rw [← Subgroup.orderOf_coe, hwval]
    exact orderOf_simpleRootHom_sl2Upper j (sub_ne_zero.2 hc)
  have hΦw : P.Φ w = t * P.Φ y * t⁻¹ * (P.Φ y)⁻¹ := by
    rw [hw, map_mul, map_inv, ← P.N3]
  have hyM : P.Φ y ∈ pieceCore e ({j} : Finset (Fin n)) := by
    rw [P.pieceCore_singleton_eq_map hK hkj hk1]
    exact ⟨y, mem_subgroupOf.2 hyJ, rfl⟩
  refine false_of_mk_mem_center_of_orderOf_commutator htH (hMH hyM) ?_ hcen
  rw [← hΦw, orderOf_injective P.Φ P.injective w, hw2]

omit [Finite F] in
theorem SwapNeighbourParam.false_of_mk_mem_center [Finite K] [CharP K 2]
    (P : SwapNeighbourParam e t k) (hK : 4 ≤ Nat.card K) {j : Fin n} (hkj : k ≠ j)
    (hk1 : j.val + 1 < n → k.val ≠ j.val + 1) {H : Subgroup G} (htH : t ∈ H)
    (hMH : pieceCore e ({j} : Finset (Fin n)) ≤ H)
    (hcen : QuotientGroup.mk' (oddCore H) ⟨t, htH⟩ ∈ center (H ⧸ oddCore H)) : False := by
  have hyJ : simpleRootHom K j (sl2Upper 1) ∈ simpleRootSL2 K j := ⟨_, rfl⟩
  set y : spBlock K ({k}ᶜ : Finset (Fin n)) :=
    ⟨simpleRootHom K j (sl2Upper 1), simpleRootSL2_le_spBlock_compl hkj hk1 hyJ⟩ with hy
  have hy2 : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_simpleRootHom_sl2Upper j one_ne_zero
  have hyinv : y⁻¹ = y := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ← hy2, pow_orderOf_eq_one]
  have hΨw : P.Ψ (y, y) = t * P.Ψ (y, 1) * t⁻¹ * (P.Ψ (y, 1))⁻¹ := by
    rw [P.swap, ← map_inv, ← map_mul, Prod.inv_mk, inv_one, Prod.mk_mul_mk, one_mul, mul_one,
      hyinv]
  have hyM : P.Ψ (y, 1) ∈ pieceCore e ({j} : Finset (Fin n)) := by
    rw [P.pieceCore_singleton_eq_map hK hkj hk1]
    exact ⟨(y, 1), ⟨mem_subgroupOf.2 hyJ, one_mem _⟩, rfl⟩
  refine false_of_mk_mem_center_of_orderOf_commutator htH (hMH hyM) ?_ hcen
  rw [← hΨw, orderOf_injective P.Ψ P.injective (y, y), Prod.orderOf_mk, hy2, Nat.lcm_self]

end Commutator

section Siegel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ}

theorem mk_mem_center_of_siegel_normal (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (htX : t ∈ centralizer (modelToG e (siegelTorus K n) : Set G))
    (hnorm : (((modelToG e (siegelLevi K n)).subgroupOf
      (centralizer (modelToG e (siegelTorus K n) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K n) : Set G))))).Normal) :
    QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G))) ⟨t, htX⟩ ∈
      center (centralizer (modelToG e (siegelTorus K n) : Set G) ⧸
        oddCore (centralizer (modelToG e (siegelTorus K n) : Set G))) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_siegelTorus_of_seitzSetting
    (X := modelToG e (siegelTorus K n)) (D := modelToG e (siegelLevi K n)) hset hKc hq hn e
    htC ht rfl htX rfl
  have hDt : (modelToG e (siegelLevi K n)).subgroupOf
      (centralizer (modelToG e (siegelTorus K n) : Set G)) ≤
        centralizer ({⟨t, htX⟩} : Set (centralizer (modelToG e (siegelTorus K n) : Set G))) := by
    intro d hd
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hdL : (d : G) ∈ L := UnitaryPilot.modelToG_le e _ (mem_subgroupOf.1 hd)
    exact mem_centralizer_iff.1 htC _ hdL
  exact F4Pilot.mk_mem_center_of_normal_map_oddCore hDt hsyl hnorm

omit [Finite G] in
theorem pieceCore_singleton_le_centralizer_siegelTorus (e : L ≃* StatedSp n K) {j : Fin n}
    (hj : j.val + 1 < n) :
    pieceCore e ({j} : Finset (Fin n)) ≤ centralizer (modelToG e (siegelTorus K n) : Set G) :=
  (pieceCore_le_siegelCore e fun i hi => by rw [Finset.mem_singleton.1 hi]; exact hj).trans
    (F4Pilot.centralizerPerfectCore_le_centralizer _)

theorem false_of_fieldNeighbourParam_of_siegel_normal (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {ι : K →+* F} {σ : F ≃+* F}
    (hσ : σ ≠ 1) {k j : Fin n} (P : FieldNeighbourParam e t ι σ k) (hj : j.val + 1 < n)
    (hkj : k ≠ j) (hk1 : k.val ≠ j.val + 1)
    (htX : t ∈ centralizer (modelToG e (siegelTorus K n) : Set G))
    (hnorm : (((modelToG e (siegelLevi K n)).subgroupOf
      (centralizer (modelToG e (siegelTorus K n) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K n) : Set G))))).Normal) : False := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  exact P.false_of_mk_mem_center hq hσ hkj (fun _ => hk1) htX
    (pieceCore_singleton_le_centralizer_siegelTorus e hj)
    (mk_mem_center_of_siegel_normal hset hKc hf hn e htC ht htX hnorm)

theorem false_of_swapNeighbourParam_of_siegel_normal (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {k j : Fin n}
    (P : SwapNeighbourParam e t k) (hj : j.val + 1 < n) (hkj : k ≠ j) (hk1 : k.val ≠ j.val + 1)
    (htX : t ∈ centralizer (modelToG e (siegelTorus K n) : Set G))
    (hnorm : (((modelToG e (siegelLevi K n)).subgroupOf
      (centralizer (modelToG e (siegelTorus K n) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K n) : Set G))))).Normal) : False := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  exact P.false_of_mk_mem_center hq hkj (fun _ => hk1) htX
    (pieceCore_singleton_le_centralizer_siegelTorus e hj)
    (mk_mem_center_of_siegel_normal hset hKc hf hn e htC ht htX hnorm)

end Siegel

end CFSG.SeitzReduction.SymplecticPilot
