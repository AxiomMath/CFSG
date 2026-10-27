module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise
open CFSG.GH74.GLS.Bg.Thompson

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowIn_normalized_of_isPGroup {p : ℕ} [Fact p.Prime] {K Q : Subgroup G}
    (hQ : IsPGroup p Q) (hQK : Q ≤ normalizer (K : Set G)) :
    ∃ P : Subgroup G, IsSylowIn p P K ∧ Q ≤ normalizer (P : Set G) ∧ Q ⊓ K ≤ P := by
  classical
  letI : MulAction Q (Sylow p K) :=
    MulAction.compHom (Sylow p K) (Subgroup.inclusion hQK)
  haveI : Finite (Sylow p K) :=
    Sylow.finite_of_finiteIndex (Classical.choice (Sylow.nonempty (p := p) (G := K)))
  obtain ⟨P₀, hP₀fix⟩ :=
    hQ.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p K)
      (not_dvd_card_sylow (p := p) (G := K))
  let P : Subgroup G := (P₀ : Subgroup K).map K.subtype
  have hPK : P ≤ K := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := P₀.isPGroup'.map K.subtype
  have hPrel : P.relIndex K = (P₀ : Subgroup K).index := by
    simpa [P, Subgroup.map_top, Subgroup.range_subtype] using
      (Subgroup.relIndex_map_map_of_injective (f := K.subtype) (P₀ : Subgroup K) ⊤
        Subtype.coe_injective)
  have hPsyl : IsSylowIn p P K :=
    ⟨hPK, hPp, by rw [hPrel]; exact P₀.not_dvd_index⟩
  have hforward : ∀ q : Q, ∀ x ∈ P, (q : G) * x * (q : G)⁻¹ ∈ P := by
    intro q x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hfix : q • P₀ = P₀ := MulAction.mem_fixedPoints.mp hP₀fix q
    have hfix' : (Subgroup.inclusion hQK q) • P₀ = P₀ := by
      simpa only [MulAction.compHom_smul_def] using hfix
    have hsm : (Subgroup.inclusion hQK q) • (P₀ : Subgroup K) = (P₀ : Subgroup K) := by
      rw [← Sylow.pointwise_smul_def, hfix']
    have hmem : (Subgroup.inclusion hQK q) • k ∈ (P₀ : Subgroup K) := by
      have h := Subgroup.smul_mem_pointwise_smul k (Subgroup.inclusion hQK q)
        (P₀ : Subgroup K) hk
      rwa [hsm] at h
    have hmemG : (((Subgroup.inclusion hQK q) • k : K) : G) ∈ P :=
      Subgroup.mem_map_of_mem K.subtype hmem
    have hcoe : (((Subgroup.inclusion hQK q) • k : K) : G) = (q : G) * (k : G) * (q : G)⁻¹ := rfl
    change (q : G) * (k : G) * (q : G)⁻¹ ∈ P
    rwa [← hcoe]
  have hQnorm : Q ≤ normalizer (P : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hforward ⟨q, hq⟩ x
    · intro hx
      have h := hforward (⟨q, hq⟩ : Q)⁻¹ (q * x * q⁻¹) hx
      simpa [mul_assoc] using h
  have hQKle : Q ⊓ K ≤ P := by
    have hsup_p : IsPGroup p (((Q ⊓ K) ⊔ P : Subgroup G)) :=
      IsPGroup.to_sup_of_normal_right' (hQ.to_le inf_le_left) hPp
        (fun x hx => hQnorm hx.1)
    have hsup_le : ((Q ⊓ K) ⊔ P : Subgroup G) ≤ K := sup_le inf_le_right hPK
    have hsubp : IsPGroup p ((((Q ⊓ K) ⊔ P : Subgroup G)).subgroupOf K) :=
      hsup_p.of_equiv (Subgroup.subgroupOfEquivOfLe hsup_le).symm
    have hle : (P₀ : Subgroup K) ≤ (((Q ⊓ K) ⊔ P : Subgroup G)).subgroupOf K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem K.subtype hx)
    have heq : (((Q ⊓ K) ⊔ P : Subgroup G)).subgroupOf K = (P₀ : Subgroup K) :=
      P₀.is_maximal' hsubp hle
    have hEq : ((Q ⊓ K) ⊔ P : Subgroup G) = P := by
      have hmap := congrArg (Subgroup.map K.subtype) heq
      rw [Subgroup.map_subgroupOf_eq_of_le hsup_le] at hmap
      simpa [P] using hmap
    calc Q ⊓ K ≤ (Q ⊓ K) ⊔ P := le_sup_left
      _ = P := hEq
  exact ⟨P, hPsyl, hQnorm, hQKle⟩

end CFSG.GroupTheory
