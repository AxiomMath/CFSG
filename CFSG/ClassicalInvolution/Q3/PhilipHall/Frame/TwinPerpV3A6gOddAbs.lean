module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S
public import CFSG.ClassicalInvolution.Asc77.AscSixBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 (mem_normalizer_iff_conjSub_eq)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S (ae6L ae6Vc)

section Odd

variable {G : Type} [Group G] [Finite G]

theorem odd_fixes_all {S : Set (Subgroup G)} (hS : S.ncard ≤ 3) {c : G} (hodd : Odd (orderOf c))
    (hmaps : ∀ Q ∈ S, conjSub c Q ∈ S) {A : Subgroup G} (hA : A ∈ S) (hfix : conjSub c A = A) :
    ∀ Q ∈ S, conjSub c Q = Q := by
  classical
  intro Q hQ
  by_contra hne
  have hQ' : conjSub c Q ∈ S := hmaps Q hQ
  have hQ'' : conjSub c (conjSub c Q) ∈ S := hmaps _ hQ'
  have hAinv : conjSub c⁻¹ A = A := by
    calc conjSub c⁻¹ A = conjSub c⁻¹ (conjSub c A) := by rw [hfix]
      _ = A := conjSub_inv_conjSub c A
  have hAQ : A ≠ Q := fun h => hne (by rw [← h]; exact hfix)
  have hAQ' : A ≠ conjSub c Q := fun h => hAQ (by
    have := congrArg (conjSub c⁻¹) h
    rw [hAinv, conjSub_inv_conjSub] at this
    exact this)
  have hQQ' : Q ≠ conjSub c Q := fun h => hne h.symm
  have hQ'Q'' : conjSub c Q ≠ conjSub c (conjSub c Q) := fun h => by
    have h' : Q = conjSub c Q := conjSub_injective c h
    exact hQQ' h'
  have hAQ'' : A ≠ conjSub c (conjSub c Q) := fun h => hAQ' (by
    have := congrArg (conjSub c⁻¹) h
    rw [hAinv, conjSub_inv_conjSub] at this
    exact this)
  by_cases hQQ'' : Q = conjSub c (conjSub c Q)
  ·
    obtain ⟨k, hk⟩ := hodd
    have hc2 : c * c ∈ Subgroup.normalizer (Q : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul]
      exact hQQ''.symm
    have hck : c = (c * c) ^ (k + 1) := by
      have h1 : c ^ (orderOf c) = 1 := pow_orderOf_eq_one c
      rw [hk] at h1
      calc c = c ^ (2 * k + 1) * c := by rw [h1, one_mul]
        _ = (c * c) ^ (k + 1) := by
          rw [← pow_succ, ← pow_two, ← pow_mul]
          congr 1
    have : c ∈ Subgroup.normalizer (Q : Set G) := by
      rw [hck]
      exact Subgroup.pow_mem _ hc2 _
    exact hne (mem_normalizer_iff_conjSub_eq.mp this)
  ·
    have hsub : (({A, Q, conjSub c Q, conjSub c (conjSub c Q)} : Finset (Subgroup G)) :
        Set (Subgroup G)) ⊆ S := by
      intro R hR
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hR
      rcases hR with rfl | rfl | rfl | rfl <;> assumption
    have hcard : ({A, Q, conjSub c Q, conjSub c (conjSub c Q)} : Finset (Subgroup G)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hAQ, hAQ', hAQ'']),
        Finset.card_insert_of_notMem (by simp [hQQ', hQQ'']),
        Finset.card_insert_of_notMem (by simp [hQ'Q'']), Finset.card_singleton]
    have h4 := Set.ncard_le_ncard hsub (Set.toFinite S)
    rw [Set.ncard_coe_finset, hcard] at h4
    omega

end Odd

section LGroup

variable {Y : Type} [Group Y]

theorem conjSub_biSup_le (c : Y) (s : Set (Subgroup Y)) (T : Subgroup Y)
    (h : ∀ J ∈ s, conjSub c J ≤ T) : conjSub c (⨆ J ∈ s, J) ≤ T := by
  unfold conjSub
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun J hJ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact h J hJ

theorem conjSub_ae6L_le {Ω : Set (Subgroup Y)} (hinv : ConjInvariant Ω) {c t τ x : Y}
    (hct : c * t * c⁻¹ = t) (hcτ : c * τ * c⁻¹ = τ) (hcx : c * x * c⁻¹ = x) :
    conjSub c (ae6L Ω t τ x) ≤ ae6L Ω t τ x := by
  unfold ae6L
  refine conjSub_biSup_le c _ _ fun J hJ => ?_
  have hJ' : conjSub c J ∈ ae6Vc Ω t ∪ ae6Vc Ω τ ∪ ae6Vc Ω x := by
    rcases hJ with (hJ | hJ) | hJ
    · refine Or.inl (Or.inl ⟨hinv c J hJ.1, ?_⟩)
      have := hJ.2.conj c
      rwa [hct] at this
    · refine Or.inl (Or.inr ⟨hinv c J hJ.1, ?_⟩)
      have := hJ.2.conj c
      rwa [hcτ] at this
    · refine Or.inr ⟨hinv c J hJ.1, ?_⟩
      have := hJ.2.conj c
      rwa [hcx] at this
  exact le_iSup₂_of_le (f := fun J (_ : J ∈ ae6Vc Ω t ∪ ae6Vc Ω τ ∪ ae6Vc Ω x) => J) (conjSub c J) hJ'
    le_rfl

theorem conjSub_ae6L_eq {Ω : Set (Subgroup Y)} (hinv : ConjInvariant Ω) {c t τ x : Y}
    (hct : c * t * c⁻¹ = t) (hcτ : c * τ * c⁻¹ = τ) (hcx : c * x * c⁻¹ = x) :
    conjSub c (ae6L Ω t τ x) = ae6L Ω t τ x := by
  refine le_antisymm (conjSub_ae6L_le hinv hct hcτ hcx) ?_
  have h1 : c⁻¹ * t * c⁻¹⁻¹ = t := by
    calc c⁻¹ * t * c⁻¹⁻¹ = c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ := by rw [hct]
      _ = t := by group
  have h2 : c⁻¹ * τ * c⁻¹⁻¹ = τ := by
    calc c⁻¹ * τ * c⁻¹⁻¹ = c⁻¹ * (c * τ * c⁻¹) * c⁻¹⁻¹ := by rw [hcτ]
      _ = τ := by group
  have h3 : c⁻¹ * x * c⁻¹⁻¹ = x := by
    calc c⁻¹ * x * c⁻¹⁻¹ = c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ := by rw [hcx]
      _ = x := by group
  have h4 := conjSub_mono (n := c) (conjSub_ae6L_le hinv h1 h2 h3 : conjSub c⁻¹ (ae6L Ω t τ x) ≤ _)
  rwa [conjSub_conjSub_inv] at h4

end LGroup

section Fix

variable {G : Type} [Group G]

@[expose] def fixSub (C₁ : Subgroup G) (𝒪 : Set (Subgroup G)) : Subgroup G :=
  C₁ ⊓ ⨅ (Q : Subgroup G) (_ : Q ∈ 𝒪), Subgroup.normalizer (Q : Set G)

theorem mem_fixSub {C₁ : Subgroup G} {𝒪 : Set (Subgroup G)} {c : G} :
    c ∈ fixSub C₁ 𝒪 ↔ c ∈ C₁ ∧ ∀ Q ∈ 𝒪, conjSub c Q = Q := by
  unfold fixSub
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, mem_normalizer_iff_conjSub_eq]

theorem fixSub_le (C₁ : Subgroup G) (𝒪 : Set (Subgroup G)) : fixSub C₁ 𝒪 ≤ C₁ := inf_le_left

theorem conjSub_fixSub {C₁ : Subgroup G} {𝒪 : Set (Subgroup G)}
    (hmaps : ∀ g ∈ C₁, ∀ Q ∈ 𝒪, conjSub g Q ∈ 𝒪) {g : G} (hg : g ∈ C₁) :
    conjSub g (fixSub C₁ 𝒪) = fixSub C₁ 𝒪 := by
  have hle : ∀ g ∈ C₁, conjSub g (fixSub C₁ 𝒪) ≤ fixSub C₁ 𝒪 := by
    intro g hg y hy
    rw [mem_conjSub_iff] at hy
    obtain ⟨hyC, hyQ⟩ := mem_fixSub.mp hy
    refine mem_fixSub.mpr ⟨?_, fun Q hQ => ?_⟩
    · have : g * (g⁻¹ * y * g) * g⁻¹ ∈ C₁ := C₁.mul_mem (C₁.mul_mem hg hyC) (C₁.inv_mem hg)
      simpa [mul_assoc] using this
    · calc conjSub y Q = conjSub g (conjSub (g⁻¹ * y * g) (conjSub g⁻¹ Q)) := by
            rw [← conjSub_mul, ← conjSub_mul]; congr 1; group
        _ = Q := by
          have h3 := hyQ (conjSub g⁻¹ Q) (hmaps g⁻¹ (C₁.inv_mem hg) Q hQ)
          rw [h3, conjSub_conjSub_inv]
  refine le_antisymm (hle g hg) ?_
  have h2 := conjSub_mono (n := g) (hle g⁻¹ (C₁.inv_mem hg))
  rwa [conjSub_conjSub_inv] at h2

end Fix

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
