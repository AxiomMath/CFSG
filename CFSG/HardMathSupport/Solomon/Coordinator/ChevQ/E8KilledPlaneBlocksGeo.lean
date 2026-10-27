module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralDefs
public import CFSG.RankThree.E6.RootLatticeTools

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.E6


set_option linter.unusedSectionVars false

theorem trace_conj {τ : Tag} (t w : WeylGroup τ) :
    ∑ j, ((t * w * t⁻¹) • (Pi.single j 1 : Fin τ.rank → ℤ)) j =
      ∑ j, (w • (Pi.single j 1 : Fin τ.rank → ℤ)) j := by
  have h : ∀ x : WeylGroup τ,
      ∑ j, (x • (Pi.single j 1 : Fin τ.rank → ℤ)) j = Matrix.trace (weylMatrix x) :=
    fun x => rfl
  rw [h, h, weylMatrix_mul, weylMatrix_mul, Matrix.trace_mul_comm, ← mul_assoc,
    ← weylMatrix_mul, inv_mul_cancel, weylMatrix_one, one_mul]

theorem e8D4Triangles_conj {t w' : WeylGroup Tag.E8} (h : E8NonToral.E8D4Triangles w') :
    E8NonToral.E8D4Triangles (t * w' * t⁻¹) := by
  refine ⟨fun α hα hfix => ?_, by rw [trace_conj]; exact h.2⟩
  apply h.1 (t⁻¹ • α) (IsRoot.smul hα t⁻¹)
  have h1 : t • (w' • (t⁻¹ • α)) = t • (t⁻¹ • α) := by
    rw [smul_inv_smul, ← mul_smul, ← mul_smul]
    exact hfix
  exact MulAction.injective t h1

theorem ncard_eq_of_mem_iff_inv_smul {τ : Tag} {S S' : Set (Fin τ.rank → ℤ)} {t : WeylGroup τ}
    (hS : ∀ α, α ∈ S ↔ t⁻¹ • α ∈ S') : S.ncard = S'.ncard := by
  have hSimg : S = (fun α => t • α) '' S' := by
    ext α
    rw [hS]
    constructor
    · intro h
      exact ⟨t⁻¹ • α, h, smul_inv_smul t α⟩
    · rintro ⟨β, hβ, rfl⟩
      rwa [inv_smul_smul]
  rw [hSimg]
  exact Set.ncard_image_of_injective S' (MulAction.injective t)

theorem orthOrbit_conj {τ : Tag} {S S' : Set (Fin τ.rank → ℤ)} {t w' : WeylGroup τ}
    (hS : ∀ α, α ∈ S ↔ t⁻¹ • α ∈ S')
    (hfix : ∀ γ ∈ S', w' • γ = γ ∨ iform γ (w' • γ) = 0)
    (horb : ∃ d ∈ S', iform d (w' • d) = 0 ∧ iform d (w' ^ 2 • d) = 0 ∧
      iform (w' • d) (w' ^ 2 • d) = 0) :
    (∀ γ ∈ S, (t * w' * t⁻¹) • γ = γ ∨ iform γ ((t * w' * t⁻¹) • γ) = 0) ∧
      ∃ d ∈ S, iform d ((t * w' * t⁻¹) • d) = 0 ∧ iform d ((t * w' * t⁻¹) ^ 2 • d) = 0 ∧
        iform ((t * w' * t⁻¹) • d) ((t * w' * t⁻¹) ^ 2 • d) = 0 := by
  have hconj : ∀ (u : WeylGroup τ) (x : Fin τ.rank → ℤ),
      (t * u * t⁻¹) • (t • x) = t • (u • x) := by
    intro u x
    rw [mul_smul, mul_smul, inv_smul_smul]
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ : ∃ x ∈ S', t • x = γ := ⟨t⁻¹ • γ, (hS γ).1 hγ, smul_inv_smul t γ⟩
    rw [hconj]
    rcases hfix x hx with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [iform_smul]; exact h)
  · obtain ⟨d, hd, h1, h2, h3⟩ := horb
    refine ⟨t • d, (hS _).2 (by rwa [inv_smul_smul]), ?_, ?_, ?_⟩
    · rw [hconj, iform_smul]
      exact h1
    · rw [conj_pow, hconj, iform_smul]
      exact h2
    · rw [conj_pow, hconj w' d, hconj (w' ^ 2) d, iform_smul]
      exact h3

private theorem iform_self_nonneg_gram {τ : Tag} (x : Fin τ.rank → ℤ) : 0 ≤ iform x x := by
  by_cases hx : x = 0
  · subst hx
    simp [iform]
  · exact (iform_self_pos hx).le

private theorem iform_neg_left_gram {τ : Tag} (x y : Fin τ.rank → ℤ) :
    iform (-x) y = -iform x y := by
  have h := iform_smul_left (-1) x y
  rwa [neg_one_smul, neg_one_mul] at h

theorem iform_self_eq_two_of_isRoot_simplyLaced {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    iform α α = 2 := by
  rw [← dotProduct_mulVec_eq_iform]
  exact rootForm_self hτ hα

theorem abs_iform_le_two_of_isRoot_simplyLaced {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α δ : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hδ : IsRoot τ δ) : |iform α δ| ≤ 2 := by
  have hαα := iform_self_eq_two_of_isRoot_simplyLaced hτ hα
  have hδδ := iform_self_eq_two_of_isRoot_simplyLaced hτ hδ
  have h1 := iform_self_nonneg_gram (α + δ)
  have h2 := iform_self_nonneg_gram (α - δ)
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm δ α, hαα, hδδ] at h1
  rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm δ α, hαα, hδδ] at h2
  rw [abs_le]
  constructor <;> linarith

theorem exists_mem_closure_smul_eq_of_iform_ne_zero_simplyLaced {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {α δ : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots χ) (hδ : δ ∈ kernelRoots χ) (h : iform α δ ≠ 0) :
    ∃ x ∈ Subgroup.closure (rootReflection '' kernelRoots χ), x • α = δ := by
  have hrefl : ∀ β ∈ kernelRoots χ,
      rootReflection β ∈ Subgroup.closure (rootReflection '' kernelRoots χ) :=
    fun β hβ => Subgroup.subset_closure ⟨β, hβ, rfl⟩
  obtain ⟨hαr, hαχ⟩ := hα
  obtain ⟨hδr, hδχ⟩ := hδ
  have hαα := iform_self_eq_two_of_isRoot_simplyLaced hτ hαr
  have hδδ := iform_self_eq_two_of_isRoot_simplyLaced hτ hδr
  have hb := abs_iform_le_two_of_isRoot_simplyLaced hτ hαr hδr
  have hsub : iform (α - δ) (α - δ) = 4 - 2 * iform α δ := by
    rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm δ α, hαα, hδδ]
    ring
  have hadd : iform (α + δ) (α + δ) = 4 + 2 * iform α δ := by
    rw [iform_add_left, iform_add_right, iform_add_right, iform_comm δ α, hαα, hδδ]
    ring
  have hsubα : iform (α - δ) α = 2 - iform α δ := by
    rw [iform_sub_left, hαα, iform_comm δ α]
  have haddα : iform (α + δ) α = 2 + iform α δ := by
    rw [iform_add_left, hαα, iform_comm δ α]
  have hcases : iform α δ = -2 ∨ iform α δ = -1 ∨ iform α δ = 1 ∨ iform α δ = 2 := by
    obtain ⟨h1, h2⟩ := abs_le.1 hb
    omega
  rcases hcases with hn | hn | hn | hn
  ·
    have h0 : α + δ = 0 := by
      by_contra hne
      have := iform_self_pos hne
      omega
    refine ⟨rootReflection α, hrefl α ⟨hαr, hαχ⟩, ?_⟩
    rw [rootReflection_smul_self hαr, eq_neg_of_add_eq_zero_right h0]
  ·
    have hne : α ≠ -δ := by
      intro e
      rw [e, iform_neg_left_gram, hδδ] at hn
      omega
    have hβ : IsRoot τ (α + δ) := isRoot_add_of_iform_neg hαr hδr hne (by omega)
    have hβχ : α + δ ∈ kernelRoots χ :=
      ⟨hβ, by rw [ofAdd_add, map_mul, hαχ, hδχ, one_mul]⟩
    have hcp : corootPair (α + δ) α = 1 := by
      have := corootPair_mul hβ α
      rw [hadd, haddα, hn] at this
      omega
    refine ⟨rootReflection δ * rootReflection (α + δ),
      mul_mem (hrefl δ ⟨hδr, hδχ⟩) (hrefl _ hβχ), ?_⟩
    rw [mul_smul, rootReflection_smul hβ, hcp, one_smul]
    have e : α - (α + δ) = -δ := by abel
    rw [e, smul_neg, rootReflection_smul_self hδr, neg_neg]
  ·
    have hne : α ≠ δ := by
      intro e
      rw [e, hδδ] at hn
      omega
    have hβ : IsRoot τ (α - δ) := isRoot_sub_of_iform_pos hαr hδr hne (by omega)
    have hβχ : α - δ ∈ kernelRoots χ :=
      ⟨hβ, by rw [ofAdd_sub, map_div, hαχ, hδχ, div_one]⟩
    have hcp : corootPair (α - δ) α = 1 := by
      have := corootPair_mul hβ α
      rw [hsub, hsubα, hn] at this
      omega
    refine ⟨rootReflection (α - δ), hrefl _ hβχ, ?_⟩
    rw [rootReflection_smul hβ, hcp, one_smul]
    abel
  ·
    have h0 : α - δ = 0 := by
      by_contra hne
      have := iform_self_pos hne
      omega
    exact ⟨1, one_mem _, by rw [one_smul, sub_eq_zero.1 h0]⟩

theorem exists_mem_closure_smul_eq_of_iform_ne_zero {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* M} {α δ : Fin Tag.E8.rank → ℤ}
    (hα : α ∈ kernelRoots χ) (hδ : δ ∈ kernelRoots χ) (h : iform α δ ≠ 0) :
    ∃ x ∈ Subgroup.closure (rootReflection '' kernelRoots χ), x • α = δ :=
  exists_mem_closure_smul_eq_of_iform_ne_zero_simplyLaced (Or.inr (Or.inr (Or.inr rfl))) hα hδ h

theorem image_gramBlock {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {γ : Fin 3 → Fin τ.rank → ℤ}
    (hγ : ∀ j, γ j ∈ S)
    (hsame : ∀ α ∈ S, ∀ δ ∈ S, ∀ j, iform α (γ j) ≠ 0 → (iform δ (γ j) ≠ 0 ↔ iform α δ ≠ 0))
    {x : WeylGroup τ} (hx : (fun α => x • α) '' S = S) {j j' : Fin 3}
    (h : iform (x • γ j) (γ j') ≠ 0) :
    (fun α => x • α) '' {α | α ∈ S ∧ iform α (γ j) ≠ 0} =
      {α | α ∈ S ∧ iform α (γ j') ≠ 0} := by
  have hxS : ∀ α ∈ S, x • α ∈ S := fun α hα => hx ▸ Set.mem_image_of_mem _ hα
  ext β
  constructor
  · rintro ⟨α, ⟨hαS, hα⟩, rfl⟩
    refine ⟨hxS α hαS, (hsame (x • γ j) (hxS _ (hγ j)) (x • α) (hxS α hαS) j' h).2 ?_⟩
    rw [iform_smul, iform_comm]
    exact hα
  · rintro ⟨hβS, hβ⟩
    rw [← hx] at hβS
    obtain ⟨α, hαS, rfl⟩ := hβS
    refine ⟨α, ⟨hαS, ?_⟩, rfl⟩
    have := (hsame (x • γ j) (hxS _ (hγ j)) (x • α) (hxS α hαS) j' h).1 hβ
    rw [iform_smul, iform_comm] at this
    exact this

theorem kernelBlocks_of_gram {τ : Tag} {S : Set (Fin τ.rank → ℤ)} (γ : Fin 3 → Fin τ.rank → ℤ)
    (hroot : ∀ α ∈ S, IsRoot τ α) (hγ : ∀ j, γ j ∈ S) (hneg : ∀ α ∈ S, -α ∈ S)
    (huniq : ∀ α ∈ S, ∃! j, iform α (γ j) ≠ 0)
    (hsame : ∀ α ∈ S, ∀ δ ∈ S, ∀ j, iform α (γ j) ≠ 0 → (iform δ (γ j) ≠ 0 ↔ iform α δ ≠ 0))
    (htrans : ∀ α ∈ S, ∀ δ ∈ S, iform α δ ≠ 0 →
      ∃ x ∈ Subgroup.closure (rootReflection '' S), x • α = δ)
    {w : WeylGroup τ} (hw : (fun α => w • α) '' S = S)
    (hcyc : ∀ j : Fin 3, iform (w • γ j) (γ (j + 1)) ≠ 0) :
    ∃ B : KernelBlocks τ S, ∀ j : Fin 3, (fun α => w • α) '' B.blk j = B.blk (j + 1) := by
  have hself : ∀ j, iform (γ j) (γ j) ≠ 0 := fun j =>
    (iform_self_pos (hroot _ (hγ j)).ne_zero).ne'
  refine ⟨{ blk := fun j => {α | α ∈ S ∧ iform α (γ j) ≠ 0}
            nonempty := fun j => ⟨γ j, hγ j, hself j⟩
            sub := fun j α hα => hα.1
            cover := fun α hα => ?_
            neg := fun j α hα => ?_
            disj := fun j j' hjj' => ?_
            orth := fun j j' hjj' α hα δ hδ => ?_
            trans := fun j α hα δ hδ => ?_
            perm := fun x hx j => ?_ }, fun j => ?_⟩
  · obtain ⟨j, hj, -⟩ := huniq α hα
    exact ⟨j, hα, hj⟩
  · refine ⟨hneg α hα.1, ?_⟩
    rw [iform_neg_left_gram]
    exact neg_ne_zero.2 hα.2
  · refine Set.disjoint_left.2 fun α hα hα' => hjj' ?_
    exact (huniq α hα.1).unique hα.2 hα'.2
  · by_contra h
    exact hjj' ((huniq δ hδ.1).unique ((hsame α hα.1 δ hδ.1 j hα.2).2 h) hδ.2)
  · exact htrans α hα.1 δ hδ.1 ((hsame α hα.1 δ hδ.1 j hα.2).1 hδ.2)
  · have hxγ : x • γ j ∈ S := hx ▸ Set.mem_image_of_mem _ (hγ j)
    obtain ⟨j', hj', -⟩ := huniq _ hxγ
    exact ⟨j', image_gramBlock hγ hsame hx hj'⟩
  · exact image_gramBlock hγ hsame hw (hcyc j)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
