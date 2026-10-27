module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open scoped MatrixGroups commutatorElement

section Gen3

variable {K G : Type*} [Group K] [Group G]

@[expose] def Gen3 (P : Subgroup K) : Prop :=
  ∃ S : Set K, S ⊆ P ∧ (∀ s ∈ S, s ^ 3 = 1) ∧ P ≤ Subgroup.closure S

theorem Gen3.map {P : Subgroup K} (h : Gen3 P) (f : K →* G) : Gen3 (P.map f) := by
  obtain ⟨S, hS, h3, hP⟩ := h
  refine ⟨f '' S, Set.image_subset_iff.2 fun s hs => Subgroup.mem_map_of_mem f (hS hs), ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [← map_pow, h3 s hs, map_one]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have := Subgroup.mem_map_of_mem f (hP hx)
    rwa [MonoidHom.map_closure] at this

theorem gen3_top_sl2 {F : Type} [Field F] [CharP F 3] : Gen3 (⊤ : Subgroup SL(2, F)) := by
  have h3 : (3 : F) = 0 := by
    have := CharP.cast_eq_zero F 3
    simpa using this
  refine ⟨Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F) ∪
    Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F), fun _ _ => trivial, ?_,
    CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := F) ▸ le_rfl⟩
  rintro s (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · rw [pow_succ, pow_two, ← CFSG.LocalAnalysis.ComponentInitial.sl2Upper_add,
      ← CFSG.LocalAnalysis.ComponentInitial.sl2Upper_add]
    have : c + c + c = 0 := by linear_combination c * h3
    rw [this, CFSG.LocalAnalysis.ComponentInitial.sl2Upper_zero]
  · rw [pow_succ, pow_two, ← CFSG.LocalAnalysis.ComponentInitial.sl2Lower_add,
      ← CFSG.LocalAnalysis.ComponentInitial.sl2Lower_add]
    have : c + c + c = 0 := by linear_combination c * h3
    rw [this, CFSG.LocalAnalysis.ComponentInitial.sl2Lower_zero]

theorem gen3_of_equiv_sl2 {F : Type} [Field F] [CharP F 3] {R : Subgroup K}
    (e : R ≃* SL(2, F)) : Gen3 R := by
  have h1 : Gen3 (⊤ : Subgroup ↥R) := by
    have := (gen3_top_sl2 (F := F)).map e.symm.toMonoidHom
    rwa [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.symm.surjective] at this
  have h2 := h1.map R.subtype
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2

theorem commutator_pow_three_eq_one {s b : K} (hs : s ^ 3 = 1)
    (hc : ⁅s, b⁆ ∈ Subgroup.center K) : ⁅s, b⁆ ^ 3 = 1 := by
  set κ : K := ⁅s, b⁆ with hκ
  have hcc : ∀ y : K, y * κ = κ * y := fun y => Subgroup.mem_center_iff.mp hc y
  have e1 : s * b * s⁻¹ = κ * b := by
    rw [hκ, commutatorElement_def]
    group
  have hsκ : s * κ * s⁻¹ = κ := by
    rw [hcc s]
    group
  have c2 : s * (κ * b) * s⁻¹ = κ * (κ * b) := by
    calc s * (κ * b) * s⁻¹ = (s * κ * s⁻¹) * (s * b * s⁻¹) := by group
      _ = κ * (κ * b) := by rw [hsκ, e1]
  have c3 : s * (κ * (κ * b)) * s⁻¹ = κ * (κ * (κ * b)) := by
    calc s * (κ * (κ * b)) * s⁻¹ = (s * κ * s⁻¹) * (s * (κ * b) * s⁻¹) := by group
      _ = κ * (κ * (κ * b)) := by rw [hsκ, c2]
  have h3 : s * s * s = 1 := by rw [← pow_three']; exact hs
  have e4 : κ * (κ * (κ * b)) = b := by
    calc κ * (κ * (κ * b)) = s * (s * (s * b * s⁻¹) * s⁻¹) * s⁻¹ := by rw [e1, c2, c3]
      _ = (s * s * s) * b * (s * s * s)⁻¹ := by group
      _ = b := by rw [h3]; group
  have e5 : κ * κ * κ * b = 1 * b := by
    calc κ * κ * κ * b = κ * (κ * (κ * b)) := by group
      _ = 1 * b := by rw [e4, one_mul]
  rw [pow_three']
  exact mul_right_cancel e5

theorem commute_of_map_commute_of_gen3 (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1) {R : Subgroup K} (hR : Gen3 R) {b : K}
    (h : ∀ a ∈ R, ψ a * ψ b = ψ b * ψ a) : ∀ a ∈ R, a * b = b * a := by
  obtain ⟨S, hSR, hS3, hRS⟩ := hR
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({b} : Set K) := by
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hk : ⁅s, b⁆ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h s (hSR hs)
    have hκ1 : ⁅s, b⁆ = 1 := hk3 _ hk (commutator_pow_three_eq_one (hS3 s hs) (hker hk))
    exact commutatorElement_eq_one_iff_mul_comm.1 hκ1
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hRS ha))

theorem mem_centralizer_of_map_gen3 (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1) {R : Subgroup K} (hR : Gen3 R) {g : K}
    (hg : ψ g ∈ Subgroup.centralizer ((R.map ψ : Subgroup G) : Set G)) :
    g ∈ Subgroup.centralizer (R : Set K) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact commute_of_map_commute_of_gen3 ψ hker hk3 hR (b := g)
    (fun a' ha' => Subgroup.mem_centralizer_iff.mp hg (ψ a') ⟨a', ha', rfl⟩) a ha

end Gen3

end CFSG.ClassicalInvolution.ModelFacts
