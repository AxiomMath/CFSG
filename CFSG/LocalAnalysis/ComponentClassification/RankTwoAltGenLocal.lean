module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenFusion2

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open scoped Pointwise

namespace AltGenCore

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenCore A R T g n Φ)
include s

theorem mem_sup_of_conj_root_mem_of
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) {ρ : alternatingGroup (Fin (n + 4))}
    (hρ : (ρ : Perm (Fin (n + 4))).cycleType = {2, 2}) {x : G}
    (hx : x * Φ ρ * x⁻¹ ∈ Φ.range ⊔ centralizer (Φ.range : Set G)) :
    x ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq (σ := rootLast n) (τ := ρ)
    (by rw [cycleType_rootLast, hρ]) rootLast_mul_rootLast rootLast_ne_one
  have h1 : x * Φ β * Φ (rootLast n) * (x * Φ β)⁻¹ = x * Φ ρ * x⁻¹ := by
    rw [← hβ, map_mul, map_mul, map_inv]
    group
  have h2 := (s.conj_rootLast_mem_iff_of hN hF (x * Φ β)).mp (by rw [h1]; exact hx)
  have h3 := mul_mem h2 (inv_mem (mem_sup_left ⟨β, rfl⟩ :
    Φ β ∈ Φ.range ⊔ centralizer (Φ.range : Set G)))
  rwa [mul_inv_cancel_right] at h3

theorem exists_isSylowOf_centralizer_le_of
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) {σ : alternatingGroup (Fin (n + 4))}
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ P : Subgroup G, IsSylowOf 2 P (centralizer ({Φ σ} : Set G)) ∧
      P ≤ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, hρ, hρσ⟩ := exists_root_commute hσ2 hσ1
  obtain ⟨hρ2, hρ1⟩ := mul_self_of_cycleType_two_two hρ
  set Yp := Φ.range ⊔ centralizer (Φ.range : Set G) with hYp
  set H := centralizer ({Φ σ} : Set G) ⊓ Yp with hH
  have huH : Φ ρ ∈ H := ⟨mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hρσ]),
    mem_sup_left ⟨ρ, rfl⟩⟩
  have hu2 : IsPGroup 2 (zpowers (Φ ρ)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ fun h => hρ1 (s.injective (by rw [h, map_one]))
    rw [sq, ← map_mul, hρ2, map_one]
  obtain ⟨P, hPH, huP⟩ := AS76b.exists_isSylowOf_le (zpowers_le.mpr huH) hu2
  refine ⟨P, ?_, hPH.le.trans inf_le_right⟩
  obtain ⟨Q, rfl⟩ := hPH
  obtain ⟨S, hS⟩ := OrderReductions.FixedPairSylow.sylow_in_subgroup_of_normalizer_intersection_le
    2 H (centralizer ({Φ σ} : Set G)) inf_le_left Q (by
      rintro y ⟨hyN, hyC⟩
      refine ⟨hyC, s.mem_sup_of_conj_root_mem_of hN hF hρ ?_⟩
      have h1 : y * Φ ρ * y⁻¹ ∈ (Q : Subgroup H).map H.subtype :=
        (mem_normalizer_iff.mp hyN (Φ ρ)).mp (huP (mem_zpowers _))
      exact (map_subtype_le _ h1).2)
  exact ⟨S, hS⟩

theorem exists_conj_eq_of_conj_eq_of
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) {π σ : alternatingGroup (Fin (n + 4))}
    (hπ2 : π * π = 1) (hπ1 : π ≠ 1) {x : G} (hx : x * Φ π * x⁻¹ = Φ σ) :
    ∃ β : alternatingGroup (Fin (n + 4)), β * π * β⁻¹ = σ := by
  have hσ2 : σ * σ = 1 := s.injective (by
    rw [map_mul, ← hx, map_one]
    calc x * Φ π * x⁻¹ * (x * Φ π * x⁻¹) = x * Φ (π * π) * x⁻¹ := by rw [map_mul]; group
      _ = 1 := by rw [hπ2, map_one, mul_one, mul_inv_cancel])
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hπ1
    apply s.injective
    rw [map_one]
    calc Φ π = x⁻¹ * (x * Φ π * x⁻¹) * x := by group
      _ = 1 := by rw [hx, map_one, mul_one, inv_mul_cancel]
  obtain ⟨ρ, hρ, hρπ⟩ := exists_root_commute hπ2 hπ1
  obtain ⟨hρ2, hρ1⟩ := mul_self_of_cycleType_two_two hρ
  obtain ⟨P, hP, hPY⟩ := s.exists_isSylowOf_centralizer_le_of hN hF hσ2 hσ1
  have hxu : x * Φ ρ * x⁻¹ ∈ centralizer ({Φ σ} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hx]
    have h1 : Φ ρ * Φ π = Φ π * Φ ρ := by rw [← map_mul, ← map_mul, hρπ]
    calc x * Φ ρ * x⁻¹ * (x * Φ π * x⁻¹) = x * (Φ ρ * Φ π) * x⁻¹ := by group
      _ = x * (Φ π * Φ ρ) * x⁻¹ := by rw [h1]
      _ = x * Φ π * x⁻¹ * (x * Φ ρ * x⁻¹) := by group
  have hord : orderOf (x * Φ ρ * x⁻¹) = 2 ^ 1 := by
    rw [pow_one]
    refine orderOf_eq_prime ?_ fun h => hρ1 (s.injective ?_)
    · rw [sq]
      calc x * Φ ρ * x⁻¹ * (x * Φ ρ * x⁻¹) = x * Φ (ρ * ρ) * x⁻¹ := by rw [map_mul]; group
        _ = 1 := by rw [hρ2, map_one, mul_one, mul_inv_cancel]
    · rw [map_one]
      calc Φ ρ = x⁻¹ * (x * Φ ρ * x⁻¹) * x := by group
        _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  obtain ⟨c, hcC, hcP⟩ := exists_conj_mem_of_isSylowOf_two hP hxu hord
  have hcx : c * x ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := by
    refine s.mem_sup_of_conj_root_mem_of hN hF hρ ?_
    have h1 : c * x * Φ ρ * (c * x)⁻¹ = c * (x * Φ ρ * x⁻¹) * c⁻¹ := by group
    rw [h1]
    exact hPY hcP
  have hle : centralizer (Φ.range : Set G) ≤ normalizer (Φ.range : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hcx' : c * x ∈ ((Φ.range : Set G) * (centralizer (Φ.range : Set G) : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hcx
  obtain ⟨_, ⟨β, rfl⟩, w, hw, hβw⟩ := Set.mem_mul.mp hcx'
  refine ⟨β, s.injective ?_⟩
  have hwπ : Φ π * w = w * Φ π := mem_centralizer_iff.mp hw (Φ π) ⟨π, rfl⟩
  have hcσ : c * Φ σ * c⁻¹ = Φ σ := by
    rw [mem_centralizer_singleton_iff.mp hcC, mul_inv_cancel_right]
  rw [map_mul, map_mul, map_inv, ← hcσ, ← hx]
  calc Φ β * Φ π * (Φ β)⁻¹ = Φ β * w * Φ π * (Φ β * w)⁻¹ := by
        rw [mul_assoc (Φ β) w, ← hwπ]
        group
    _ = c * (x * Φ π * x⁻¹) * c⁻¹ := by rw [hβw]; group

theorem typeTwoFusionAt_of
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) : TypeTwoFusionAt Φ := by
  intro π σ x hπ _ hx
  obtain ⟨hπ2, hπ1⟩ := mul_self_of_cycleType_two_four hπ
  obtain ⟨β, rfl⟩ := s.exists_conj_eq_of_conj_eq_of hN hF hπ2 hπ1 hx
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, cycleType_conj]
  exact hπ

theorem rankTwoX_eq_of_local
    (h34 : Asc08Lemma34)
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) (hF3 : TypeTwoCentralizerAt Φ) :
    rankTwoX A = A ⊔ rightConjugate A g :=
  s.rankTwoX_eq_of h34 hN hF (s.typeTwoFusionAt_of hN hF) hF3

end AltGenCore

end CFSG.ComponentClassification.RankTwoAlt
