module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SylowEqS

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open

variable {G : Type} [Group G] [Finite G] {S M : Subgroup G} {r s : ℕ}

omit [Finite G] in
theorem theta_range_eq_top (θ : ↥M →* Perm (OmegaE r s))
    (hAlt : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ m : ↥M, θ m = x)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r s) (hr1 : 1 ≤ r) :
    θ.range = ⊤ := by
  classical
  let i₀ : Fin r := ⟨0, hr1⟩
  have hWR : Wr r s ≤ θ.range := by
    rw [← hW]
    rintro _ ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  have hAltR : alternatingGroup (OmegaE r s) ≤ θ.range := fun x hx => by
    obtain ⟨m, hm⟩ := hAlt x hx
    exact ⟨m, hm⟩
  have htW : swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inl (i₀, true)) ∈ Wr r s := by
    have h := embL_blockTransp r s i₀ false
    simp only [Bool.not_false] at h
    rw [h]
    exact ⟨blockTransp i₀, swap_mem_blockFix rfl, rfl⟩
  exact eq_top_of_alt_odd hAltR (hWR htW) (sign_swap (by simp))

theorem theta_S_normal_pCore (hA : Asc81bHyp M S) (hSM : S ≤ M) (θ : ↥M →* Perm (OmegaE r s))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAlt : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ m : ↥M, θ m = x)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r s) (hr1 : 1 ≤ r) :
    ((S.subgroupOf M).map θ ≤ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s)))) ∧
    IsPGroup 2 ((S.subgroupOf M).map θ) ∧
    (∀ h ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))),
      ∀ u ∈ (S.subgroupOf M).map θ, h * u * h⁻¹ ∈ (S.subgroupOf M).map θ) ∧
    (∀ U : Subgroup (Perm (OmegaE r s)),
      U ≤ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) → IsPGroup 2 U →
      (∀ h ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))), ∀ u ∈ U, h * u * h⁻¹ ∈ U) →
      U ≤ (S.subgroupOf M).map θ) := by
  classical
  have hrange := theta_range_eq_top θ hAlt hW hr1
  have hnormS : ∀ m : ↥M,
      θ m ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) →
      (m : G) ∈ Subgroup.normalizer (S : Set G) := fun m hm =>
    mem_normalizer_of_theta_normalizes hA le_rfl hSM θ hker m (by rw [hW]; exact hm)
  have hθN : ∀ m : ↥M, (m : G) ∈ Subgroup.normalizer (S : Set G) →
      θ m ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := fun m hm => by
    rw [← hW]; exact theta_mem_normalizer_W θ m hm
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact hθN n (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hn))
  · exact (hS2.comap_subtype (K := M)).map θ
  · intro h hh u hu
    obtain ⟨m, rfl⟩ : h ∈ θ.range := by rw [hrange]; trivial
    obtain ⟨n, hn, rfl⟩ := hu
    have hmN : (m : G) ∈ Subgroup.normalizer (S : Set G) := hnormS m hh
    refine ⟨m * n * m⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
    have hnS : (n : G) ∈ S := Subgroup.mem_subgroupOf.1 hn
    have := (Subgroup.mem_normalizer_iff.1 hmN (n : G)).1 hnS
    simpa using this
  · intro U hUN hU2 hUnorm u hu
    obtain ⟨m, rfl⟩ : u ∈ θ.range := by rw [hrange]; trivial
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
        have := hUnorm (θ ⟨g, hgM⟩) hθg (θ t) ht
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

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
