module

public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
import CFSG.ClassicalInvolution.Q3.Q3TY10

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (Frame IsFundamental)
open CFSG.LieType.Universal.Spin
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


section Quot

variable {KY X : Type} [Group KY] [Group X]

structure CentralQuot3 (π : KY →* X) (𝓕 : Set (Subgroup KY)) (𝓕' : Set (Subgroup X))
    (Z' : Subgroup X) : Prop where
  ker_le : π.ker ≤ Subgroup.center KY
  cop : ∀ z ∈ π.ker, ¬ 3 ∣ orderOf z
  center_le : ∀ z ∈ Subgroup.center KY, π z ∈ Z'
  pow3 : ∀ R ∈ 𝓕, Pow3 R
  inj : ∀ R ∈ 𝓕, ∀ r ∈ R, π r = 1 → r = 1
  map_mem : ∀ R ∈ 𝓕, R.map π ∈ 𝓕'
  surj : ∀ L ∈ 𝓕', ∃ R ∈ 𝓕, R.map π = L

variable {π : KY →* X} {𝓕 : Set (Subgroup KY)} {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

namespace CentralQuot3

theorem map_inj (h : CentralQuot3 π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (e : R.map π = R'.map π) : R = R' :=
  eq_of_map_eq_of_pow3 π h.ker_le h.cop (h.pow3 R hR) (h.pow3 R' hR') e

theorem commutes_iff (h : CentralQuot3 π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕) :
    Commutes (R.map π) (R'.map π) ↔ Commutes R R' := by
  constructor
  · intro hc a ha b hb
    exact (commutes_of_map_commute_exponent3 π h.ker_le h.cop (A := R') (L := R) (h.pow3 R hR)
      (fun a' ha' l hl => (hc _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm
  · rintro hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]

theorem invOf (h : CentralQuot3 π 𝓕 𝓕' Z') {R : Subgroup KY} (hR : R ∈ 𝓕) {r : KY}
    (hr : InvOf R r) : InvOf (R.map π) (π r) := by
  refine ⟨⟨r, hr.1, rfl⟩, ?_⟩
  have h1 : π r ≠ 1 := fun h1 => by
    have h2 := h.inj R hR r hr.1 h1
    have h3 := hr.2
    rw [h2, orderOf_one] at h3
    omega
  have h2 : π r ^ 2 = 1 := by
    rw [← map_pow, ← hr.2, pow_orderOf_eq_one, map_one]
  exact orderOf_eq_prime h2 h1

theorem modelInvComm (h : CentralQuot3 π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕)
    (hR' : R' ∈ 𝓕) (hm : ModelInvComm (Subgroup.center KY) R R') :
    ModelInvComm Z' (R.map π) (R'.map π) := by
  obtain ⟨r, r', hr, hr', hc⟩ := hm
  refine ⟨π r, π r', h.invOf hR hr, h.invOf hR' hr', ?_⟩
  rw [← map_commutatorElement]
  exact h.center_le _ hc

theorem modelAdj (h : CentralQuot3 π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (ha : ModelAdj (Subgroup.center KY) R R') : ModelAdj Z' (R.map π) (R'.map π) := by
  obtain ⟨hne, hnc, r, r', hr, hr', hc, hnorm⟩ := ha
  refine ⟨fun e => hne (h.map_inj hR hR' e), fun hc' => hnc ((h.commutes_iff hR).mp hc'), π r,
    π r', h.invOf hR hr, h.invOf hR' hr', ?_, ?_⟩
  · rw [← map_commutatorElement]
    exact h.center_le _ hc
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨r' * x * r'⁻¹, hnorm x hx, ?_⟩
    simp [map_mul, map_inv]

theorem modelIndist (h : CentralQuot3 π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕)
    (hR' : R' ∈ 𝓕) (hne : R ≠ R') (hi : ModelIndist Z' 𝓕' (R.map π) (R'.map π)) :
    ModelIndist (Subgroup.center KY) 𝓕 R R' := by
  refine ⟨hne, fun S hS hSR hSR' hI hI' => ?_⟩
  have := hi.2 (S.map π) (h.map_mem S hS) (fun e => hSR (h.map_inj hS hR e))
    (fun e => hSR' (h.map_inj hS hR' e)) (h.modelInvComm hS hR hI) (h.modelInvComm hS hR' hI')
  rwa [h.commutes_iff hS, h.commutes_iff hS] at this

end CentralQuot3

theorem exists_lin_of_map3 [Finite KY] (hC : ¬ 3 ∣ Nat.card (Subgroup.center KY)) (ψ : KY →* X)
    (hker : ψ.ker ≤ Subgroup.center KY) {R₁ R₂ : Subgroup KY} (hR₁ : Pow3 R₁) (hR₂ : Pow3 R₂)
    (h : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂ :=
  CFSG.ClassicalInvolution.Q3.Q3TY.exists_lin_of_map3' hC ψ hker hR₁ hR₂ h

namespace CentralQuot3

theorem orthGeom (h : CentralQuot3 π 𝓕 𝓕' Z') (hG : OrthGeom Z' 𝓕' (GaloisField 3 1))
    (hlift : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕,
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map π) (R₂.map π)) →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂) :
    OrthGeom (Subgroup.center KY) 𝓕 (GaloisField 3 1) where
  star := by
    intro c hc l₁ h₁ l₂ h₂ l₃ h₃ a₁ a₂ a₃ n12 n13 n23 k12 k13 k23
    have := hG.star (c.map π) (h.map_mem c hc) (l₁.map π) (h.map_mem l₁ h₁) (l₂.map π)
      (h.map_mem l₂ h₂) (l₃.map π) (h.map_mem l₃ h₃) (h.modelAdj hc h₁ a₁) (h.modelAdj hc h₂ a₂)
      (h.modelAdj hc h₃ a₃) (fun e => n12 (h.map_inj h₁ h₂ e)) (fun e => n13 (h.map_inj h₁ h₃ e))
      (fun e => n23 (h.map_inj h₂ h₃ e)) ((h.commutes_iff h₁).mpr k12)
      ((h.commutes_iff h₁).mpr k13) ((h.commutes_iff h₂).mpr k23)
    rcases this with hi | hi | hi
    · exact Or.inl (h.modelIndist h₁ h₂ n12 hi)
    · exact Or.inr (Or.inl (h.modelIndist h₁ h₃ n13 hi))
    · exact Or.inr (Or.inr (h.modelIndist h₂ h₃ n23 hi))
  sign := by
    intro R₁ h₁ R₂ h₂ R₃ h₃ a₁ a₃ k13 ⟨W, hW⟩
    obtain ⟨W', hW'⟩ := hG.sign (R₁.map π) (h.map_mem R₁ h₁) (R₂.map π) (h.map_mem R₂ h₂)
      (R₃.map π) (h.map_mem R₃ h₃) (h.modelAdj h₁ h₂ a₁) (h.modelAdj h₃ h₂ a₃)
      ((h.commutes_iff h₁).mpr k13) ⟨_, linearBlockStandardPair_map π h.ker_le hW⟩
    exact hlift R₂ h₂ R₃ h₃ ⟨W', hW'⟩
  perp2 := by
    intro R₁ h₁ R₂ h₂ ha ⟨W, hW⟩
    obtain ⟨S₁', hS₁', S₂', hS₂', hne, c₁, c₂, n₁, n₂⟩ := hG.perp2 (R₁.map π)
      (h.map_mem R₁ h₁) (R₂.map π) (h.map_mem R₂ h₂) (h.modelAdj h₁ h₂ ha)
      ⟨_, linearBlockStandardPair_map π h.ker_le hW⟩
    obtain ⟨S₁, hS₁, rfl⟩ := h.surj S₁' hS₁'
    obtain ⟨S₂, hS₂, rfl⟩ := h.surj S₂' hS₂'
    exact ⟨S₁, hS₁, S₂, hS₂, fun e => hne (by rw [e]), (h.commutes_iff h₁).mp c₁,
      (h.commutes_iff h₁).mp c₂, fun hc => n₁ ((h.commutes_iff h₂).mpr hc),
      fun hc => n₂ ((h.commutes_iff h₂).mpr hc)⟩

theorem orthFacts [Finite KY] (hC : ¬ 3 ∣ Nat.card (Subgroup.center KY))
    (h : CentralQuot3 π 𝓕 𝓕' Z') (hG : OrthGeom Z' 𝓕' (GaloisField 3 1)) :
    OrthFacts 𝓕 (GaloisField 3 1) :=
  { toOrthGeom := h.orthGeom hG fun R₁ h₁ R₂ h₂ hl =>
      exists_lin_of_map3 hC π h.ker_le (h.pow3 R₁ h₁) (h.pow3 R₂ h₂) hl
    lift := fun ψ hψ R₁ h₁ R₂ h₂ hl =>
      exists_lin_of_map3 hC ψ hψ (h.pow3 R₁ h₁) (h.pow3 R₂ h₂) hl }

end CentralQuot3

end Quot

section Plus

theorem not_three_dvd_card_center {G : Type} [Group G] [Finite G]
    (h : ∀ w ∈ Subgroup.center G, ¬ 3 ∣ orderOf w) : ¬ 3 ∣ Nat.card (Subgroup.center G) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 3 h3
  apply h (x : G) x.2
  rw [Subgroup.orderOf_coe, hx]

theorem centralQuot3_plus6 :
    CentralQuot3 (spinAction (quadPlus 6 (GaloisField 3 1)))
      (fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)))
      (fundSet (quadPlus 6 (GaloisField 3 1)))
      (scalars (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1)) := by
  have hm3 : 3 ≤ 6 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hY := yData3_D6 hadm
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3
  have hpow : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) hm3),
      Pow3 R := by
    have := hY.pow3
    rw [e] at this
    exact this
  have hcentral : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) hm3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus 6 (GaloisField 3 1))) → r = 1 := by
    have := hY.central
    rw [e] at this
    exact this
  have hsc : FundamentalSingleClass .POmegaPlus (plusDatum 6 (GaloisField 3 1) hm3) := by
    have := hY.sc
    rw [e] at this
    exact this
  have hker := ker_spinAction_le_center (quadPlus 6 (GaloisField 3 1))
  exact
    { ker_le := hker
      cop := fun z hz h3 => by
        have h2 : z ^ 2 = 1 := by
          rw [pow_two]
          exact ModelFacts.OrthAut.plus_hker2 6 z hz
        have := orderOf_dvd_of_pow_eq_one h2
        have := h3.trans this
        omega
      center_le := fun z hz => spinAction_center_mem_scalars hm3 hz
      pow3 := hpow
      inj := fun R hR r hr h1 => hcentral R hR r hr (hker h1)
      map_mem := fun R hR => map_mem_fundSet hm3 hsc hR
      surj := fun L hL => exists_map_eq hm3 odd_gf3 hL }

theorem orthFacts3_plusDatum6 :
    OrthFacts (fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)))
      (GaloisField 3 1) := by
  have hm3 : 3 ≤ 6 := by norm_num
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by
    rw [card_gf3]
    norm_num
  have hK' : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by omega)]
    norm_num
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have hG := orthGeom_model (K' := GaloisField 3 (2 * 1)) hK hK' odd_gf3
    (nondegenerate_polarBilin_quadPlus 6 (GaloisField 3 1)) hdim
  have : Finite (spinGroup (quadPlus 6 (GaloisField 3 1))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hcop : ∀ w ∈ Subgroup.center (spinGroup (quadPlus 6 (GaloisField 3 1))),
      ¬ 3 ∣ orderOf w := by
    intro w hw h3
    have h4 := pow_four_of_mem_center_spinPlus (K := GaloisField 3 1) hm3 hw
    have := h3.trans (orderOf_dvd_of_pow_eq_one h4)
    omega
  exact centralQuot3_plus6.orthFacts (not_three_dvd_card_center hcop) hG

theorem orthFacts3_plus6 :
    OrthFacts (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D) (GaloisField 3 1) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num : 3 ≤ 6)
  rw [e]
  exact orthFacts3_plusDatum6

theorem layerGeomD6_3 :
    LayerGeom (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D) (GaloisField 3 1) :=
  orthFacts3_plus6.toLayerGeom

end Plus

end CFSG.ClassicalInvolution.Q3.Q3W
