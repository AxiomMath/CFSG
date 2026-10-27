module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedReps
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6Reps

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open scoped commutatorElement

variable {K : Type} [Field K]

abbrev rtT₁ : Fin TwistTag.E6.tag.rank → ℤ := (![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ)

abbrev rtT₂ : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)

abbrev rtU₁ : Fin TwistTag.E6.tag.rank → ℤ := (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ)

abbrev rtU₂ : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ)

abbrev rtV₁ : Fin TwistTag.E6.tag.rank → ℤ := (![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ)

abbrev rtV₂ : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)

abbrev rtV₃ : Fin TwistTag.E6.tag.rank → ℤ := (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ)

abbrev rtV₄ : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)

theorem isRoot_rt :
    IsRoot TwistTag.E6.tag rtT₁ ∧ IsRoot TwistTag.E6.tag rtT₂ ∧ IsRoot TwistTag.E6.tag rtU₁ ∧
      IsRoot TwistTag.E6.tag rtU₂ ∧ IsRoot TwistTag.E6.tag rtV₁ ∧ IsRoot TwistTag.E6.tag rtV₂ ∧
        IsRoot TwistTag.E6.tag rtV₃ ∧ IsRoot TwistTag.E6.tag rtV₄ := by
  simp only [isRoot_iff_twistedE6TwoRootB]
  decide +kernel

theorem pos_perm
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (hp : 0 < height δ) :
    IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm δ) ∧
      0 < height (permLattice TwistTag.E6.perm δ) :=
  ⟨hδ.permLattice TwistTag.E6.cartan_perm, by rw [height_permLattice]; exact hp⟩

theorem pinnedX_mem_posUnipotent
    {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) (hp : 0 < height δ) (c : K) :
    pinnedX TwistTag.E6.tag K δ c ∈ posUnipotent TwistTag.E6.tag K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α}) ⟨hδ, hp⟩ c

theorem twistedE6PairX_mem_posUnipotent
    (σ : K →+* K) {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) (hp : 0 < height δ) (s : K) :
    twistedE6PairX σ δ s ∈ posUnipotent TwistTag.E6.tag K :=
  mul_mem (pinnedX_mem_posUnipotent hδ hp s)
    (pinnedX_mem_posUnipotent (pos_perm hδ hp).1 (pos_perm hδ hp).2 (σ s))

theorem residualMem_conj_of_gens
    [Finite K] [CharP K 2] {σ : K →+* K}
    {s : graphFixedRootGroup TwistTag.E6 K σ} (S : Set (graphFixedRootGroup TwistTag.E6 K σ))
    (hS : ∀ c ∈ S, (c : ModGL TwistTag.E6.tag K) ∈ posUnipotent TwistTag.E6.tag K)
    (hSo : ∀ c ∈ S, c ∈ closure {c | c * s = s * c ∧ Odd (orderOf c)})
    (hs : s ∈ ⁅closure S, closure S⁆) (g : graphFixedRootGroup TwistTag.E6 K σ) :
    ResidualMem (g * s * g⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine E6Sec8.residualMem_conj_of ?_ ((closure_le _).2 hSo) hs g
  refine ((isPGroup_posUnipotent (K := K) 2 TwistTag.E6.tag).comap_subtype
    (K := graphFixedRootGroup TwistTag.E6 K σ)).to_le ?_
  rw [closure_le]
  exact fun c hc => hS c hc

theorem exists_add_sigma_eq_one [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c) :
    ∃ t₀ : K, t₀ + σ.toRingHom t₀ = 1 := by
  obtain ⟨d₀, hd₀⟩ := exists_twistedE6_sigma_ne hf hK hσ
  have hτ : d₀ + σ.toRingHom d₀ ≠ 0 := by
    intro h
    apply hd₀
    have e : σ.toRingHom d₀ = -d₀ := by linear_combination h
    rw [show σ d₀ = σ.toRingHom d₀ from rfl, e, CharTwo.neg_eq]
  have hστ : σ.toRingHom (d₀ + σ.toRingHom d₀) = d₀ + σ.toRingHom d₀ := by
    rw [map_add, hσσ, add_comm]
  exact ⟨d₀ * (d₀ + σ.toRingHom d₀)⁻¹, by
    rw [map_mul, map_inv₀, hστ, ← add_mul, mul_inv_cancel₀ hτ]⟩

theorem residualMem_conj_t
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    (g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ResidualMem (g * t * g⁻¹) := by
  obtain ⟨h₁, h₂, -⟩ := isRoot_rt
  have hρ₁ : permLattice TwistTag.E6.perm rtT₁ = rtT₁ := by decide
  have hρ₂ : permLattice TwistTag.E6.perm rtT₂ = rtT₂ := by decide
  have hp₁ : 0 < height rtT₁ := by decide
  have hp₂ : 0 < height rtT₂ := by decide
  set x₁ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, pinnedX_mem_graphFixedRootGroup_of_fixed σ.toRingHom h₁ hρ₁ (map_one _)⟩
  set x₂ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, pinnedX_mem_graphFixedRootGroup_of_fixed σ.toRingHom h₂ hρ₂ (map_one _)⟩
  have hU : ∀ c ∈ ({x₁, x₂} : Set (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      (c : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom := by
    rintro c (rfl | rfl)
    · exact pinnedX_mem_graphFixedPosUnipotent σ.toRingHom h₁ hp₁ hρ₁ (map_one _)
    · exact pinnedX_mem_graphFixedPosUnipotent σ.toRingHom h₂ hp₂ hρ₂ (map_one _)
  refine residualMem_conj_of_gens {x₁, x₂} (fun c hc => (Subgroup.mem_inf.1 (hU c hc)).1)
    (fun c hc => ?_) ?_ g
  · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · exact graphFixedPosUnipotent_le_closure_odd_two (by rw [hK]; norm_num)
        (fun c => by rw [hσ]; norm_num) ht (hU c hc)
    · exact graphFixedPosUnipotent_le_closure_odd hf2 hK hσ ht (hU c hc)
  · have e : t = ⁅x₁, x₂⁆ := by
      refine Subtype.ext ?_
      rw [coe_commutatorElement_twistedE6Classes, ht]
      change _ = ⁅pinnedX TwistTag.E6.tag K rtT₁ 1, pinnedX TwistTag.E6.tag K rtT₂ 1⁆
      rw [commutator_pinnedX_of_isRoot_add_E6 h₁ h₂ (by decide)
        (by rw [show rtT₁ + rtT₂ = e6HighestRoot by decide]; exact isRoot_e6HighestRoot),
        mul_one, show rtT₁ + rtT₂ = e6HighestRoot by decide]
    rw [e]
    exact commutator_mem_commutator (subset_closure (Set.mem_insert _ _))
      (subset_closure (Set.mem_insert_of_mem _ rfl))

theorem residualMem_conj_u
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c)
    {u : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hu : (u : ModGL TwistTag.E6.tag K) = twistedE6ClassU K)
    (g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ResidualMem (g * u * g⁻¹) := by
  obtain ⟨-, -, h₁, h₂, -⟩ := isRoot_rt
  obtain ⟨t₀, ht₀⟩ := exists_add_sigma_eq_one hf hK hσ hσσ
  have hp₁ : 0 < height rtU₁ := by decide
  have hp₂ : 0 < height rtU₂ := by decide
  set y₁ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, twistedE6PairX_mem_graphFixedRootGroup hσσ h₁ 1⟩
  set y₂ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, twistedE6PairX_mem_graphFixedRootGroup hσσ h₂ 1⟩
  have hu' : (u : ModGL TwistTag.E6.tag K) =
      (twistedE6ClassURoots.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod := by
    rw [hu]
    simp [twistedE6ClassU, twistedE6ClassURoots]
  have hH : ∀ {δ : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag δ → 4 ≤ height δ →
      twistedE6PairX σ.toRingHom δ 1 ∈ heightSeries TwistTag.E6.tag K 4 := by
    intro δ hδ h4
    have h4' : 4 ≤ height (permLattice TwistTag.E6.perm δ) := by
      rw [height_permLattice]
      exact h4
    exact mul_mem
      (pinnedX_mem_rootSpan
        (S := {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ 4 ≤ height α}) ⟨hδ, by omega, h4⟩ 1)
      (pinnedX_mem_rootSpan
        (S := {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ 4 ≤ height α})
        ⟨hδ.permLattice TwistTag.E6.cartan_perm, by omega, h4'⟩ _)
  refine residualMem_conj_of_gens {y₁, y₂} ?_ ?_ ?_ g
  · rintro c (rfl | rfl)
    · exact twistedE6PairX_mem_posUnipotent σ.toRingHom h₁ hp₁ 1
    · exact twistedE6PairX_mem_posUnipotent σ.toRingHom h₂ hp₂ 1
  · rintro c (rfl | rfl)
    · exact fixedHeightSeries_le_closure_odd_of_classCheck σ.surjective hσσ ht₀
        twistedE6ClassCheck_U hu' _ (hH h₁ (by decide))
    · exact fixedHeightSeries_le_closure_odd_of_classCheck σ.surjective hσσ ht₀
        twistedE6ClassCheck_U hu' _ (hH h₂ (by decide))
  · have e : u = ⁅y₁, y₂⁆ := by
      refine Subtype.ext ?_
      rw [coe_commutatorElement_twistedE6Classes, hu,
        twistedE6ClassU_eq_twistedE6PairX σ.toRingHom]
      change _ = ⁅twistedE6PairX σ.toRingHom rtU₁ 1, twistedE6PairX σ.toRingHom rtU₂ 1⁆
      rw [commutator_twistedE6PairX_pairSum σ.toRingHom h₁ h₂
        (by rw [show rtU₁ + rtU₂ = twistedE6ClassRootU by decide]
            exact isRoot_twistedE6ClassRoots.1)
        (by decide) (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide)
        (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide)
        (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide),
        mul_one, show rtU₁ + rtU₂ = twistedE6ClassRootU by decide]
    rw [e]
    exact commutator_mem_commutator (subset_closure (Set.mem_insert _ _))
      (subset_closure (Set.mem_insert_of_mem _ rfl))

theorem residualMem_conj_v
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c)
    {v : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hv : (v : ModGL TwistTag.E6.tag K) = twistedE6ClassV K)
    (g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ResidualMem (g * v * g⁻¹) := by
  obtain ⟨-, -, -, -, h₁, h₂, h₃, h₄⟩ := isRoot_rt
  obtain ⟨t₀, ht₀⟩ := exists_add_sigma_eq_one hf hK hσ hσσ
  have hρ₃ : permLattice TwistTag.E6.perm rtV₃ = rtV₃ := by decide
  have hρ₄ : permLattice TwistTag.E6.perm rtV₄ = rtV₄ := by decide
  set y₁ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, twistedE6PairX_mem_graphFixedRootGroup hσσ h₁ 1⟩
  set y₂ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, twistedE6PairX_mem_graphFixedRootGroup hσσ h₂ 1⟩
  set x₃ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, pinnedX_mem_graphFixedRootGroup_of_fixed σ.toRingHom h₃ hρ₃ (map_one _)⟩
  set x₄ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨_, pinnedX_mem_graphFixedRootGroup_of_fixed σ.toRingHom h₄ hρ₄ (map_one _)⟩
  have hv' : (v : ModGL TwistTag.E6.tag K) =
      (twistedE6ClassVRoots.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod := by
    rw [hv]
    simp [twistedE6ClassV, twistedE6ClassVRoots, mul_assoc]
  have hA := twistedE6OrbitClosure_le_closure_odd hσσ ht₀ twistedE6ClassCheck_V hv'
  have hD : rtV₁ ∈ twistedE6ClassTargets twistedE6ClassVTable ∧
      rtV₂ ∈ twistedE6ClassTargets twistedE6ClassVTable ∧
      rtV₃ ∈ twistedE6ClassTargets twistedE6ClassVTable ∧
      rtV₄ ∈ twistedE6ClassTargets twistedE6ClassVTable := by decide
  refine residualMem_conj_of_gens {y₁, y₂, x₃, x₄} ?_ ?_ ?_ g
  · rintro c (rfl | rfl | rfl | rfl)
    · exact twistedE6PairX_mem_posUnipotent σ.toRingHom h₁ (by decide) 1
    · exact twistedE6PairX_mem_posUnipotent σ.toRingHom h₂ (by decide) 1
    · exact pinnedX_mem_posUnipotent h₃ (by decide) 1
    · exact pinnedX_mem_posUnipotent h₄ (by decide) 1
  · rintro c (rfl | rfl | rfl | rfl)
    · exact hA (subset_closure ⟨_, hD.1, twistedE6PairX_mem_orbitGroup hσσ h₁ 1⟩)
    · exact hA (subset_closure ⟨_, hD.2.1, twistedE6PairX_mem_orbitGroup hσσ h₂ 1⟩)
    · exact hA (subset_closure ⟨_, hD.2.2.1,
        pinnedX_mem_orbitGroup_of_fixed σ.toRingHom h₃ hρ₃ (map_one _)⟩)
    · exact hA (subset_closure ⟨_, hD.2.2.2,
        pinnedX_mem_orbitGroup_of_fixed σ.toRingHom h₄ hρ₄ (map_one _)⟩)
  · have e : v = ⁅y₁, y₂⁆ * ⁅x₃, x₄⁆ := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, coe_commutatorElement_twistedE6Classes,
        coe_commutatorElement_twistedE6Classes, hv,
        twistedE6ClassV_eq_twistedE6PairX σ.toRingHom]
      change _ = ⁅twistedE6PairX σ.toRingHom rtV₁ 1, twistedE6PairX σ.toRingHom rtV₂ 1⁆ *
        ⁅pinnedX TwistTag.E6.tag K rtV₃ 1, pinnedX TwistTag.E6.tag K rtV₄ 1⁆
      rw [commutator_twistedE6PairX_pairSum σ.toRingHom h₁ h₂
        (by rw [show rtV₁ + rtV₂ = twistedE6ClassRootA by decide]
            exact isRoot_twistedE6ClassRoots.2.2.1)
        (by decide) (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide)
        (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide)
        (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide),
        commutator_pinnedX_of_isRoot_add_E6 h₃ h₄ (by decide)
        (by rw [show rtV₃ + rtV₄ = twistedE6ClassRootB by decide]
            exact isRoot_twistedE6ClassRoots.2.2.2.2),
        mul_one, show rtV₁ + rtV₂ = twistedE6ClassRootA by decide,
        show rtV₃ + rtV₄ = twistedE6ClassRootB by decide]
    rw [e]
    refine mul_mem (commutator_mem_commutator (subset_closure (Set.mem_insert _ _))
      (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) ?_
    exact commutator_mem_commutator
      (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl))))

theorem residualMem_twReps
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c) :
    ∀ x ∈ twReps σ.toRingHom hσσ, ResidualMem x := by
  have key : ∀ (ω : List (Fin TwistTag.E6.foldedTag.rank))
      (x s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      twistedE6RelWeyl K ω * (x : ModGL TwistTag.E6.tag K) * (twistedE6RelWeyl K ω)⁻¹ = s →
        ∃ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, x = g * s * g⁻¹ := by
    intro ω x s h
    refine ⟨(⟨_, twistedE6RelWeyl_mem σ.toRingHom ω⟩ : graphFixedRootGroup _ _ _)⁻¹,
      Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, ← h]
    group
  intro x hx
  simp only [twReps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx
  · obtain ⟨g, hg⟩ := key wordT x ⟨_, pinnedX_e6HighestRoot_mem_graphFixedRootGroup σ.toRingHom 1
      (map_one _)⟩ (by rw [hx]; exact conj_frT)
    rw [hg]
    exact residualMem_conj_t hf hK hσ (by rfl) g
  · obtain ⟨g, hg⟩ := key wordU x ⟨_, twistedE6ClassU_mem_graphFixedRootGroup hσσ⟩
      (by rw [hx]; exact conj_frU)
    rw [hg]
    exact residualMem_conj_u hf hK hσ hσσ (by rfl) g
  · obtain ⟨g, hg⟩ := key wordV x ⟨_, twistedE6ClassV_mem_graphFixedRootGroup hσσ⟩
      (by rw [hx]; exact conj_frV)
    rw [hg]
    exact residualMem_conj_v hf hK hσ hσσ (by rfl) g

end CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
