module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ModelTwoAF

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open

variable {G : Type} [Group G] [Finite G] {S M : Subgroup G}

theorem le_theta_S_of_normal_two (hA : Asc81bHyp M S) (hSM : S ≤ M) {Ω : Type*}
    (θ : ↥M →* Perm Ω) (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S) (W : Subgroup (Perm Ω))
    (hW : ((thompsonJ S).subgroupOf M).map θ = W) (U : Subgroup (Perm Ω))
    (hUN : U ≤ Subgroup.normalizer (W : Set (Perm Ω))) (hU2 : IsPGroup 2 U)
    (hUr : U ≤ θ.range)
    (hUnorm : ∀ h ∈ Subgroup.normalizer (W : Set (Perm Ω)), h ∈ θ.range →
      ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    U ≤ (S.subgroupOf M).map θ := by
  classical
  have hnormS : ∀ m : ↥M,
      θ m ∈ Subgroup.normalizer (W : Set (Perm Ω)) →
      (m : G) ∈ Subgroup.normalizer (S : Set G) := fun m hm =>
    mem_normalizer_of_theta_normalizes hA le_rfl hSM θ hker m (by rw [hW]; exact hm)
  have hθN : ∀ m : ↥M, (m : G) ∈ Subgroup.normalizer (S : Set G) →
      θ m ∈ Subgroup.normalizer (W : Set (Perm Ω)) := fun m hm => by
    rw [← hW]; exact theta_mem_normalizer_W θ m hm
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  intro u hu
  obtain ⟨m, rfl⟩ : u ∈ θ.range := hUr hu
  set T : Subgroup (↥M) := U.comap θ with hT
  set T' : Subgroup G := T.map M.subtype with hT'
  have hTN : ∀ t ∈ T, (t : G) ∈ Subgroup.normalizer (S : Set G) := fun t ht =>
    hnormS t (hUN ht)
  have hT'le : T' ≤ M ⊓ Subgroup.normalizer (S : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t.2, hTN t ht⟩
  have hT'norm : (T'.subgroupOf (M ⊓ Subgroup.normalizer (S : Set G))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨t, ht, htx⟩ : (x : G) ∈ T' := Subgroup.mem_subgroupOf.1 hx
    have hgN : (g : G) ∈ Subgroup.normalizer (S : Set G) := g.2.2
    have hgM : (g : G) ∈ M := g.2.1
    have hθg := hθN ⟨g, hgM⟩ hgN
    refine Subgroup.mem_subgroupOf.2 ⟨⟨g, hgM⟩ * t * ⟨g, hgM⟩⁻¹, ?_, ?_⟩
    · show θ (⟨g, hgM⟩ * t * ⟨g, hgM⟩⁻¹) ∈ U
      have := hUnorm (θ ⟨g, hgM⟩) hθg ⟨_, rfl⟩ (θ t) ht
      simpa [map_mul, map_inv] using this
    · simp [← htx]
  have hT'p : IsPGroup 2 T' := by
    rintro ⟨_, t, ht, rfl⟩
    obtain ⟨k, hk⟩ := hU2 ⟨θ t, ht⟩
    have hk' : (θ t) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : t ^ 2 ^ k ∈ θ.ker := by rw [MonoidHom.mem_ker, map_pow, hk']
    obtain ⟨j, hj⟩ := hS2 ⟨(t ^ 2 ^ k : ↥M), hker _ h1⟩
    have hj' : ((t ^ 2 ^ k : ↥M) : G) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    refine ⟨k + j, Subtype.ext ?_⟩
    show ((t : G)) ^ 2 ^ (k + j) = 1
    rw [pow_add, pow_mul]
    simpa using hj'
  have hmem : (m : G) ∈ pCoreOf 2 (M ⊓ Subgroup.normalizer (S : Set G)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 T'
      (M ⊓ Subgroup.normalizer (S : Set G)) hT'le hT'norm hT'p ⟨m, hu, rfl⟩
  have hmS : (m : G) ∈ S := by rw [hA.twoRadical.2.2]; exact hmem
  exact ⟨m, Subgroup.mem_subgroupOf.2 hmS, rfl⟩

theorem theta_S_le_normalizer (hA : Asc81bHyp M S) (hSM : S ≤ M) {Ω : Type*}
    (θ : ↥M →* Perm Ω) (W : Subgroup (Perm Ω))
    (hW : ((thompsonJ S).subgroupOf M).map θ = W) :
    (S.subgroupOf M).map θ ≤ Subgroup.normalizer (W : Set (Perm Ω)) := by
  rintro _ ⟨n, hn, rfl⟩
  rw [← hW]
  exact theta_mem_normalizer_W θ n (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hn))

theorem theta_S_conj_mem (hA : Asc81bHyp M S) (hSM : S ≤ M) {Ω : Type*}
    (θ : ↥M →* Perm Ω) (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S) (W : Subgroup (Perm Ω))
    (hW : ((thompsonJ S).subgroupOf M).map θ = W) {h : Perm Ω}
    (hN : h ∈ Subgroup.normalizer (W : Set (Perm Ω))) (hr : h ∈ θ.range)
    {u : Perm Ω} (hu : u ∈ (S.subgroupOf M).map θ) : h * u * h⁻¹ ∈ (S.subgroupOf M).map θ := by
  obtain ⟨m, rfl⟩ := hr
  obtain ⟨n, hn, rfl⟩ := hu
  have hmN : (m : G) ∈ Subgroup.normalizer (S : Set G) :=
    mem_normalizer_of_theta_normalizes hA le_rfl hSM θ hker m (by rw [hW]; exact hN)
  refine ⟨m * n * m⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
  have hnS : (n : G) ∈ S := Subgroup.mem_subgroupOf.1 hn
  have := (Subgroup.mem_normalizer_iff.1 hmN (n : G)).1 hnS
  simpa using this

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
