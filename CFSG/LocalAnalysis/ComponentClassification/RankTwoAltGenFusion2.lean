module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEPerm

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools
open scoped Pointwise

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_cycleType_two_two_commute {σ : Perm α} (h1 : σ ≠ 1) (h2 : σ * σ = 1)
    (hs : sign σ = 1) : ∃ ρ : Perm α, ρ.cycleType = {2, 2} ∧ sign ρ = 1 ∧ ρ * σ = σ * ρ := by
  have hσσ : ∀ x, σ (σ x) = x := fun x => by rw [← Perm.mul_apply, h2, Perm.one_apply]
  have h4 := four_le_card_support_of_mul_self_eq_one h1 h2 hs
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact h1 (Equiv.ext h)
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c, σ c ≠ c ∧ c ≠ a ∧ c ≠ σ a := by
    by_contra h
    push Not at h
    have hsub : σ.support ⊆ {a, σ a} := fun c hc' => by
      rw [mem_support] at hc'
      by_cases hca : c = a
      · simp [hca]
      · simp [h c hc' hca]
    have h3 := Finset.card_le_card hsub
    have h5 := Finset.card_insert_le a {σ a}
    rw [Finset.card_singleton] at h5
    omega
  have hab : a ≠ σ a := Ne.symm ha
  have hcd : c ≠ σ c := Ne.symm hc
  have hda : σ c ≠ a := fun h => hcb (by rw [← h, hσσ])
  have hdb : σ c ≠ σ a := fun h => hca (σ.injective h)
  have hdisj : Perm.Disjoint (swap a (σ a)) (swap c (σ c)) := by
    rw [disjoint_iff_disjoint_support, support_swap hab, support_swap hcd]
    simp only [Finset.disjoint_insert_left, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨swap a (σ a) * swap c (σ c), ?_, ?_, ?_⟩
  · rw [hdisj.cycleType_mul, (isCycle_swap hab).cycleType, (isCycle_swap hcd).cycleType,
      card_support_swap hab, card_support_swap hcd]
    rfl
  · rw [Perm.sign_mul, sign_swap hab, sign_swap hcd]
    rfl
  · symm
    calc σ * (swap a (σ a) * swap c (σ c)) = σ * swap a (σ a) * swap c (σ c) :=
          (mul_assoc _ _ _).symm
      _ = swap (σ a) (σ (σ a)) * (σ * swap c (σ c)) := by
          rw [mul_swap_eq_swap_mul σ a (σ a), mul_assoc]
      _ = swap (σ a) (σ (σ a)) * (swap (σ c) (σ (σ c)) * σ) := by
          rw [mul_swap_eq_swap_mul σ c (σ c)]
      _ = swap a (σ a) * swap c (σ c) * σ := by
          rw [hσσ, hσσ, swap_comm (σ a), swap_comm (σ c), mul_assoc]

end Perm

theorem exists_root_commute {n : ℕ} {σ : alternatingGroup (Fin (n + 4))} (h2 : σ * σ = 1)
    (h1 : σ ≠ 1) : ∃ ρ : alternatingGroup (Fin (n + 4)),
      (ρ : Perm (Fin (n + 4))).cycleType = {2, 2} ∧ ρ * σ = σ * ρ := by
  have h2' : (σ : Perm (Fin (n + 4))) * σ = 1 := by
    rw [← Subgroup.coe_mul, h2]
    rfl
  obtain ⟨ρ, hρ, hρs, hρσ⟩ := exists_cycleType_two_two_commute (fun h => h1 (Subtype.ext h)) h2'
    (mem_alternatingGroup.mp σ.2)
  exact ⟨⟨ρ, hρs⟩, hρ, Subtype.ext hρσ⟩

theorem mul_self_of_cycleType_two_two {n : ℕ} {ρ : alternatingGroup (Fin (n + 4))}
    (hρ : (ρ : Perm (Fin (n + 4))).cycleType = {2, 2}) : ρ * ρ = 1 ∧ ρ ≠ 1 := by
  refine ⟨Subtype.ext ?_, fun h1 => ?_⟩
  · have hord : orderOf (ρ : Perm (Fin (n + 4))) = 2 := by
      rw [← lcm_cycleType, hρ]
      rfl
    rw [Subgroup.coe_mul, ← sq, ← hord, pow_orderOf_eq_one]
    rfl
  · rw [h1] at hρ
    simp at hρ

namespace AltGenSetting

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenSetting A R T g n Φ)
include s

theorem mem_sup_of_conj_root_mem (hF : AltRootFusion) (hn : 9 ≤ n)
    (IH : ∀ m, 5 ≤ m → m < n → AltChildAt m) {ρ : alternatingGroup (Fin (n + 4))}
    (hρ : (ρ : Perm (Fin (n + 4))).cycleType = {2, 2}) {x : G}
    (hx : x * Φ ρ * x⁻¹ ∈ Φ.range ⊔ centralizer (Φ.range : Set G)) :
    x ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq (σ := rootLast n) (τ := ρ)
    (by rw [cycleType_rootLast, hρ]) rootLast_mul_rootLast rootLast_ne_one
  have h1 : x * Φ β * Φ (rootLast n) * (x * Φ β)⁻¹ = x * Φ ρ * x⁻¹ := by
    rw [← hβ, map_mul, map_mul, map_inv]
    group
  have h2 := (s.conj_rootLast_mem_iff hF hn IH (x * Φ β)).mp (by rw [h1]; exact hx)
  have h3 := mul_mem h2 (inv_mem (mem_sup_left ⟨β, rfl⟩ :
    Φ β ∈ Φ.range ⊔ centralizer (Φ.range : Set G)))
  rwa [mul_inv_cancel_right] at h3

theorem exists_isSylowOf_centralizer_le (hF : AltRootFusion) (hn : 9 ≤ n)
    (IH : ∀ m, 5 ≤ m → m < n → AltChildAt m) {σ : alternatingGroup (Fin (n + 4))}
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
      refine ⟨hyC, s.mem_sup_of_conj_root_mem hF hn IH hρ ?_⟩
      have h1 : y * Φ ρ * y⁻¹ ∈ (Q : Subgroup H).map H.subtype :=
        (mem_normalizer_iff.mp hyN (Φ ρ)).mp (huP (mem_zpowers _))
      exact (map_subtype_le _ h1).2)
  exact ⟨S, hS⟩

theorem exists_conj_eq_of_conj_eq (hF : AltRootFusion) (hn : 9 ≤ n)
    (IH : ∀ m, 5 ≤ m → m < n → AltChildAt m) {π σ : alternatingGroup (Fin (n + 4))}
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
  obtain ⟨P, hP, hPY⟩ := s.exists_isSylowOf_centralizer_le hF hn IH hσ2 hσ1
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
    refine s.mem_sup_of_conj_root_mem hF hn IH hρ ?_
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

end AltGenSetting

theorem altTypeTwoFusion_of_rootFusion (hF : AltRootFusion) : AltTypeTwoFusion := by
  intro G _ _ A R T g n Φ s hn IH π σ x hπ _ hx
  obtain ⟨hπ2, hπ1⟩ := mul_self_of_cycleType_two_four hπ
  obtain ⟨β, rfl⟩ := s.exists_conj_eq_of_conj_eq hF hn IH hπ2 hπ1 hx
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, cycleType_conj]
  exact hπ

end CFSG.ComponentClassification.RankTwoAlt
