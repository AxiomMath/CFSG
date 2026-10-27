module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionLevi
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionOuter

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms


variable {K : Type} [Field K]

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_twoCentral_E7 {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .E7 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype)
    {g z : G} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hg : g⁻¹ * t * g = t * z) :
    ∃ g₁ : G, ∃ y ∈ ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype, y ≠ 1 ∧
      g₁⁻¹ * t * g₁ = t * y ∧ ∃ P : Subgroup G,
        P ≤ centralizer (X : Set G) ⊓ centralizer ({g₁⁻¹ * t * g₁} : Set G) ∧
          Nonempty (P ≃* EPilot.perpLevi .E7 K) :=
  exists_le_centralizer_mulEquiv_of_conj_eq_mul_twoCentral_E7_of_facts hset hq e (factO2E7 hq)
    (factF5E7 hq) htC ht hXodd hXJ hzL hz1 hzU hg

theorem exists_le_centralizer_mulEquiv_caseA_E7 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ g : G, g⁻¹ * t * g ∉ L)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype) :
    ∃ g₁ : G, ∃ y ∈ ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype, y ≠ 1 ∧
      g₁⁻¹ * t * g₁ = t * y ∧ ∃ P : Subgroup G,
        P ≤ centralizer (X : Set G) ⊓ centralizer ({g₁⁻¹ * t * g₁} : Set G) ∧
          Nonempty (P ≃* EPilot.perpLevi .E7 K) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨g, z, hzL, hgz, hz1, hzU⟩ :=
    exists_conj_eq_mul_twoCentral_E7 hset (by omega) hK e ht hKt hnot
  exact exists_le_centralizer_mulEquiv_of_conj_eq_mul_twoCentral_E7 hset hq e htK.1 ht hXodd hXJ
    hzL hz1 hzU hgz

end CFSG.SeitzReduction.E7Pilot
