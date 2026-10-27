module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearRigid
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.ComponentClassification.RankTwoHypIISymplectic

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)

variable {K : Type} [Field K] {r : ℕ}

theorem isSimpleGroup_and_perfect [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hr : 1 ≤ r)
    (hcond : 2 ≤ f ∨ 3 ≤ r) (hf : 1 ≤ f) :
    IsSimpleGroup (StatedProj (StatedSp r K)) ∧ Group.IsPerfect (StatedProj (StatedSp r K)) := by
  have hc : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
      (Nat.card K = 2 ∧ 3 ≤ r) := by
    rcases hcond with h2 | h3
    · left
      right
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
    · by_cases hf1 : f = 1
      · right
        right
        exact ⟨by rw [hK, hf1]; norm_num, h3⟩
      · left
        right
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r hr hc,
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect r K ?_⟩
  rcases hc with (hinf | h4) | h3 | h2
  · exact absurd hinf (not_infinite_iff_finite.mpr inferInstance)
  · left
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ : Finset K).card by
        rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
    exact ⟨s, hs⟩
  · right
    left
    exact h3
  · right
    right
    exact h2

theorem center_eq_bot [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hr : 1 ≤ r)
    (hcond : 2 ≤ f ∨ 3 ≤ r) (hf : 1 ≤ f) : center (StatedProj (StatedSp r K)) = ⊥ := by
  obtain ⟨hs, hp⟩ := isSimpleGroup_and_perfect hK hr hcond hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (StatedProj (StatedSp r K))) with h | h
  · exact h
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top (StatedProj (StatedSp r K))).2 h
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_ne_bot h1

section Field

variable [Finite K]

omit [Finite K] in
theorem range_eq_inner_inf_centralizer {f : ℕ} (hr : 2 ≤ r) (hf : 2 ≤ f) (hfe : Even f)
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) (hσ : ∀ t, σ t = t ^ 2 ^ (f / 2)) :
    ((spInner r K).comp (subfieldSpHom r (descentField σ))).range =
      inner (StatedProj (StatedSp r K)) ⊓ centralizer {fieldAut r K σ} := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hNI, -, -, ⟨act, -, Θ, hΘ⟩, -, -⟩ :=
    even_symplectic_field_centralizers_and_intermediate_odd_cores hr hf hfe hK σ hσ
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    refine ⟨hNI ⟨g, rfl⟩, ?_⟩
    have h1 := (Θ ⟨g, 1⟩).2
    rw [hΘ g 1, map_one, mul_one] at h1
    exact h1.2
  · rintro x ⟨hxI, hxC⟩
    have hxE : x ∈ spSemilinearAutGroup r K ⊓ centralizer {fieldAut r K σ} :=
      ⟨inner_le_spSemilinearAutGroup hxI, hxC⟩
    obtain ⟨⟨g, φ⟩, hy⟩ := Θ.surjective ⟨x, hxE⟩
    have hx : x = spInner r K (subfieldSpHom r (descentField σ) g) * fieldAut r K φ := by
      rw [← hΘ, hy]
    rw [← range_spInner] at hxI
    obtain ⟨h, rfl⟩ := hxI
    have h1 : spInner r K h * fieldAut r K 1 =
        spInner r K (subfieldSpHom r (descentField σ) g) * fieldAut r K φ := by
      rw [map_one, mul_one, hx]
    obtain ⟨rfl, -⟩ := spInner_mul_fieldAut_inj h1
    exact ⟨g, rfl⟩

theorem rigidInvolution_fieldAut_sp {f : ℕ} (hr : 2 ≤ r) (hf : 2 ≤ f) (hfe : Even f)
    (hK : Nat.card K = 2 ^ f) (hsmall : 3 ≤ r ∨ 4 ≤ f) (σ : K ≃+* K)
    (hσ : ∀ t, σ t = t ^ 2 ^ (f / 2))
    (hout : ∀ s : MulAut (StatedProj (StatedSp r K)), s ∉ spSemilinearAutGroup r K →
      s ∉ centralizer ((((spInner r K).comp (subfieldSpHom r (descentField σ))).range :
        Subgroup (MulAut (StatedProj (StatedSp r K)))) : Set (MulAut (StatedProj (StatedSp r K)))))
    (hX : fieldAut r K σ ∉ inner (StatedProj (StatedSp r K)))
    (h2 : fieldAut r K σ ^ 2 = 1) :
    RigidInvolution (inner (StatedProj (StatedSp r K))) (fieldAut r K σ) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : NeZero r := ⟨by omega⟩
  have : Finite (MulAut (StatedProj (StatedSp r K))) := Finite.of_injective
    (fun e : MulAut (StatedProj (StatedSp r K)) => (e : StatedProj (StatedSp r K) →
      StatedProj (StatedSp r K))) fun _ _ hab => MulEquiv.ext (congrFun hab)
  set k := descentField σ with hk
  set N := ((spInner r K).comp (subfieldSpHom r k)).range with hN
  obtain ⟨hNI, -, hιjinj, -, hCEN, -⟩ :=
    even_symplectic_field_centralizers_and_intermediate_odd_cores hr hf hfe hK σ hσ
  have hNeq := range_eq_inner_inf_centralizer hr hf hfe hK σ hσ
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hX (by rw [map_one]; exact one_mem _)
  obtain ⟨-, -, hkcard, -⟩ := even_symplectic_quadratic_involution_descent (by omega)
    (by omega) hK (a := fieldAut r K σ) (by rw [← sq, h2]) 1 σ
    (by rw [show (⟨(1 : StatedSp r K), statedSp_le_gsp (1 : StatedSp r K).2⟩ : gsp r K) = 1 from
      rfl, map_one, one_mul]) hσ1
  have eN : N ≃* StatedSp r k := (MonoidHom.ofInjective hιjinj).symm
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ := small_standard_source_even_simple_symplectic_parameters_stated
    (X := StatedSp r k) hkcard (by omega) ⟨MulEquiv.refl _⟩
  have hcond : 2 ≤ f / 2 ∨ 3 ≤ r := by
    rcases hsmall with h | h
    · exact Or.inr h
    · exact Or.inl (by omega)
  have := (isSimpleGroup_and_perfect hkcard (by omega) hcond (by omega)).1
  have hsimple : IsSimpleGroup N := (eN.trans eProj.symm).isSimpleGroup
  have heven : Even (Nat.card N) := by
    rw [Nat.card_congr eN.toEquiv]
    exact RankTwoHypIILinear.even_card_statedSp (by omega) hkcard (by omega)
  have hNC : N ≤ centralizer {fieldAut r K σ} := by
    rw [hN, hNeq]
    exact inf_le_right
  refine RigidInvolution.of_isSimpleGroup_of_le_zpowers hX h2 hNI hNC ?_ hsimple heven ?_
  ·
    intro c hc
    rw [mem_normalizer_iff]
    intro y
    rw [hNeq]
    constructor
    · intro hy
      obtain ⟨hyI, hyC⟩ := mem_inf.mp hy
      exact mem_inf.mpr ⟨(inner_normal _).conj_mem y hyI c, mul_mem (mul_mem hc hyC) (inv_mem hc)⟩
    · intro hy
      obtain ⟨hyI, hyC⟩ := mem_inf.mp hy
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have := (inner_normal _).conj_mem _ hyI c⁻¹
        simpa [mul_assoc] using this
      · have := mul_mem (mul_mem (inv_mem hc) hyC) hc
        simpa [mul_assoc] using this
  ·
    rintro s ⟨-, hsN⟩
    by_cases hsE : s ∈ spSemilinearAutGroup r K
    · rw [← hCEN]
      exact ⟨hsE, hsN⟩
    · exact absurd hsN (hout s hsE)

end Field

end CFSG.ComponentClassification.RankTwoHypIISymplectic
