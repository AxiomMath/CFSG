module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorRightOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairOddFactor

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

variable {G : Type*} [Group G]

theorem closure_orderOf_two_eq_closure_sq_eq_one (p : G → Prop) :
    Subgroup.closure {x | p x ∧ orderOf x = 2} = Subgroup.closure {x | p x ∧ x ^ 2 = 1} := by
  apply le_antisymm
  · refine Subgroup.closure_mono fun x hx => ⟨hx.1, ?_⟩
    rw [← hx.2]
    exact pow_orderOf_eq_one x
  · rw [Subgroup.closure_le]
    rintro x ⟨hx, hx2⟩
    by_cases h1 : x = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hx, orderOf_eq_prime hx2 h1⟩

theorem map_closure_involutions {K : Subgroup G} (T : Subgroup K) :
    (Subgroup.closure {x : K | x ∈ T ∧ orderOf x = 2}).map K.subtype =
      Subgroup.closure {g : G | g ∈ T.map K.subtype ∧ orderOf g = 2} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨hxT, hxo⟩, rfl⟩
    exact ⟨⟨x, hxT, rfl⟩, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact hxo⟩
  · rintro ⟨⟨x, hxT, rfl⟩, hxo⟩
    exact ⟨x, ⟨hxT, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hxo⟩, rfl⟩

theorem map_omega_one_eq_closure {K : Subgroup G} (T : Subgroup K) :
    (CFSG.omega₁ (G := T) (p := 2)).map (K.subtype.comp T.subtype) =
      Subgroup.closure {g : G | g ∈ T.map K.subtype ∧ orderOf g = 2} := by
  change (Subgroup.closure {x : T | x ^ 2 ^ 1 = 1}).map _ = _
  rw [MonoidHom.map_closure, closure_orderOf_two_eq_closure_sq_eq_one]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, x.2, rfl⟩, ?_⟩
    have h := congrArg (fun y : T => ((y : K) : G)) hx
    simpa using h
  · rintro ⟨⟨x, hxT, rfl⟩, hx2⟩
    refine ⟨⟨x, hxT⟩, ?_, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hx2

theorem exists_sylow_of_odd_orbit [Finite G] {L H : Subgroup G}
    (hodd : Odd (Nat.card (numeratorRightOrbit H L (rightCosetMk H 1))))
    (R : Sylow 2 ↥(L ⊓ H)) :
    ∃ R' : Sylow 2 L,
      (R' : Subgroup L).map L.subtype = (R : Subgroup ↥(L ⊓ H)).map (L ⊓ H).subtype := by
  let := numeratorRightOrbitAction H L (rightCosetMk H 1)
  have := numeratorRightOrbitAction_transitive H L (rightCosetMk H 1)
  have hindex := MulAction.index_stabilizer_of_transitive L
    (⟨rightCosetMk H 1, numeratorRightOrbit_base H L _⟩ :
      numeratorRightOrbit H L (rightCosetMk H 1))
  rw [numeratorRightOrbitAction_stabilizer] at hindex
  change ((rightCosetStabilizer H (rightCosetMk H 1)).subgroupOf L).index = _ at hindex
  rw [rightCosetStabilizer_base] at hindex
  refine exists_sylow_map_eq_of_odd_relIndex inf_le_left ?_ R
  rw [Subgroup.inf_relIndex_left]
  change Odd (H.subgroupOf L).index
  rw [hindex]
  exact hodd

theorem normalizer_le_of_unique_fixed_coset {H U : Subgroup G} (hUH : U ≤ H) {z : G}
    (hzU : z ∈ U)
    (hfix : ∀ ω : pointRightCosetSpace H,
      pointRightCosetMul H ω z = ω ↔ ω = Quotient.mk (QuotientGroup.rightRel H) 1) :
    Subgroup.normalizer (U : Set G) ≤ H := by
  intro n hn
  have h1 : pointRightCosetMul H (Quotient.mk (QuotientGroup.rightRel H) n) z =
      Quotient.mk (QuotientGroup.rightRel H) n := by
    rw [pointRightCosetMul_mk]
    apply Quotient.sound
    change QuotientGroup.rightRel H (n * z) n
    rw [QuotientGroup.rightRel_apply]
    have h := hUH ((Subgroup.mem_normalizer_iff.mp hn _).mp (U.inv_mem hzU))
    simpa only [mul_inv_rev, mul_assoc] using h
  have h2 := Quotient.exact ((hfix _).mp h1)
  change QuotientGroup.rightRel H n 1 at h2
  rw [QuotientGroup.rightRel_apply, one_mul] at h2
  exact inv_inv n ▸ H.inv_mem h2

theorem inv_mul_mul_eq_iff (g x : G) : g⁻¹ * x * g = x ↔ g * x * g⁻¹ = x := by
  constructor <;> intro h
  · conv_lhs => rw [← h]
    group
  · conv_lhs => rw [← h]
    group

end CFSG.ProperTwoGeneratedCore.RankOnePair
