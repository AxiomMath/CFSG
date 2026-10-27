module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinCase

open Subgroup CFSG.LocalAnalysis.EvenBN.LinearThree

theorem radicals_conj_sq_mem {A : Type*} [Group A] {Q₁ Q₂ : Subgroup A} {q : ℕ} (hq : 2 ≤ q)
    (hQ : Radicals (⊤ : Subgroup A) Q₁ Q₂ q) (ψ : A ≃* A) {y : A} (hy : y ∈ Q₁) :
    ψ (ψ y) ∈ Q₁ := by
  have h := Radicals.map (φ := ψ.toMonoidHom) ψ.injective hQ
  rw [Subgroup.map_top_of_surjective _ ψ.surjective] at h
  have step : ∀ {Z : Subgroup A} {z : A}, z ∈ Z → ψ z ∈ Z.map ψ.toMonoidHom :=
    fun hz => Subgroup.mem_map_of_mem ψ.toMonoidHom hz
  rcases hQ.eq_or_eq hq h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1.le (step (h1.le (step hy)))
  · exact h2.le (step (h1.le (step hy)))

theorem exists_conjQuot {G : Type*} [Group G] {S E : Subgroup G} [(E.subgroupOf S).Normal] {u : G}
    (hu : u ∈ normalizer (S : Set G)) (hue : u ∈ normalizer (E : Set G)) :
    ∃ ψ : (↥S ⧸ E.subgroupOf S) ≃* (↥S ⧸ E.subgroupOf S), ∀ (s : G) (hs : s ∈ S),
      ∃ hs' : u * s * u⁻¹ ∈ S, ψ (QuotientGroup.mk' (E.subgroupOf S) ⟨s, hs⟩) =
        QuotientGroup.mk' (E.subgroupOf S) ⟨u * s * u⁻¹, hs'⟩ := by
  have hu' : u⁻¹ ∈ normalizer (S : Set G) := inv_mem hu
  have hue' : u⁻¹ ∈ normalizer (E : Set G) := inv_mem hue
  let e : ↥S ≃* ↥S :=
    { toFun := fun s => ⟨u * s * u⁻¹, (mem_normalizer_iff.1 hu s).1 s.2⟩
      invFun := fun s => ⟨u⁻¹ * s * u, by simpa using (mem_normalizer_iff.1 hu' s).1 s.2⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have he : (E.subgroupOf S).map e.toMonoidHom = E.subgroupOf S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ E := mem_subgroupOf.1 hy
      exact mem_subgroupOf.2 ((mem_normalizer_iff.1 hue y).1 hy')
    · intro hx
      have hx' : (x : G) ∈ E := mem_subgroupOf.1 hx
      refine ⟨e.symm x, mem_subgroupOf.2 ?_, e.apply_symm_apply x⟩
      have := (mem_normalizer_iff.1 hue' (x : G)).1 hx'
      rw [inv_inv] at this
      exact this
  exact ⟨QuotientGroup.congr _ _ e he, fun s hs => ⟨(mem_normalizer_iff.1 hu s).1 hs, rfl⟩⟩

theorem odd_conj_mem_radical {G : Type*} [Group G] {S E : Subgroup G} [(E.subgroupOf S).Normal]
    {Q₁ Q₂ : Subgroup (↥S ⧸ E.subgroupOf S)} {q : ℕ} (hq : 2 ≤ q)
    (hQ : Radicals (⊤ : Subgroup (↥S ⧸ E.subgroupOf S)) Q₁ Q₂ q) {J : Subgroup G}
    (hJ : Odd (Nat.card J)) (hJS : J ≤ normalizer (S : Set G)) (hJE : J ≤ normalizer (E : Set G))
    {j : G} (hj : j ∈ J) {s : G} (hs : s ∈ S)
    (hsQ : QuotientGroup.mk' (E.subgroupOf S) ⟨s, hs⟩ ∈ Q₁) :
    ∃ hs' : j * s * j⁻¹ ∈ S, QuotientGroup.mk' (E.subgroupOf S) ⟨j * s * j⁻¹, hs'⟩ ∈ Q₁ := by
  have hcop : (Nat.card J).Coprime 2 := Nat.coprime_two_right.2 hJ
  obtain ⟨u, hu⟩ := (powCoprime hcop).surjective (⟨j, hj⟩ : J)
  have huj : (u : G) * (u : G) = j := by
    have := congrArg Subtype.val hu
    simpa [powCoprime_apply, pow_two] using this
  obtain ⟨ψ, hψ⟩ := exists_conjQuot (hJS u.2) (hJE u.2)
  obtain ⟨hs₁, h₁⟩ := hψ s hs
  obtain ⟨hs₂, h₂⟩ := hψ ((u : G) * s * (u : G)⁻¹) hs₁
  have hjs : j * s * j⁻¹ = (u : G) * ((u : G) * s * (u : G)⁻¹) * (u : G)⁻¹ := by
    rw [← huj]
    group
  have hmem : j * s * j⁻¹ ∈ S := by
    rw [hjs]
    exact hs₂
  refine ⟨hmem, ?_⟩
  have hsub : (⟨j * s * j⁻¹, hmem⟩ : ↥S) = ⟨(u : G) * ((u : G) * s * (u : G)⁻¹) * (u : G)⁻¹, hs₂⟩ :=
    Subtype.ext hjs
  rw [hsub, ← h₂, ← h₁]
  exact radicals_conj_sq_mem hq hQ ψ hsQ

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
