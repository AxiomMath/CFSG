module

public import CFSG.CGT.Timmesfeld75.Sec5FiveBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Conj

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem MaxPair.conjSubgroup_pair (hP : MaxPair T T₁) (c : G) :
    MaxPair (conjSubgroup c T) (conjSubgroup c T₁) where
  wc := hP.wc.conj c
  conj := by
    obtain ⟨x, hx⟩ := hP.conj
    refine ⟨c * x * c⁻¹, ?_⟩
    rw [hx, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  ne := fun h => hP.ne (conjSubgroup_inj.1 h)
  nontriv := by
    rw [normIn_conj]
    exact fun h => hP.nontriv (conjSubgroup_eq_bot_iff.1 h)
  maximal := by
    intro g hg
    have e : conjSubgroup g (conjSubgroup c T) =
        conjSubgroup c (conjSubgroup (c⁻¹ * g * c) T) := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [e] at hg ⊢
    have hne : conjSubgroup (c⁻¹ * g * c) T ≠ T := fun h => hg (by rw [h])
    rw [normIn_conj, normIn_conj, card_conjSubgroup, card_conjSubgroup]
    exact hP.maximal _ hne

theorem secA_conjSubgroup_eq (c : G) (T T₁ : Subgroup G) :
    secA (conjSubgroup c T) (conjSubgroup c T₁) = conjSubgroup c (secA T T₁) := by
  ext x
  rw [mem_secA, mem_conjSubgroup, mem_secA]
  constructor
  · intro h g hg
    have hg' : c * g * c⁻¹ ∈ Subgroup.normalizer ((conjSubgroup c T : Subgroup G) : Set G) := by
      rw [mem_normalizer_conjSubgroup_iff]
      simpa [mul_assoc] using hg
    have := h _ hg'
    rw [normIn_conj, conjSubgroup_conjSubgroup, mem_conjSubgroup] at this
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using this
  · intro h g' hg'
    have hg : c⁻¹ * g' * c ∈ Subgroup.normalizer (T : Set G) :=
      mem_normalizer_conjSubgroup_iff.1 hg'
    have := h _ hg
    rw [mem_conjSubgroup] at this
    rw [normIn_conj, conjSubgroup_conjSubgroup, mem_conjSubgroup]
    simpa [mul_assoc] using this

section Pair

variable [Finite G]

theorem commutator_secA_conj_pair (hP : MaxPair T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    {c h : G} {S B S₂ : Subgroup G} (hSc : S = conjSubgroup c T)
    (hB : B = conjSubgroup c (secA T T₁)) (hS₂ : S₂ = conjSubgroup h S) (hne : S₂ ≠ S)
    (hL : normIn S₂ S ≠ ⊥) : ∀ x ∈ conjSubgroup h B, ∀ t ∈ S, ⁅x, t⁆ ∈ B := by
  subst hSc hB hS₂
  have := commutator_conj_secA_le_of_ne (hP.conjSubgroup_pair c) (hS.conj c) (hI.conj c) hne hL
  rwa [secA_conjSubgroup_eq] at this

end Pair

theorem conj_mem_secA_conj_pair {c : G} {S B : Subgroup G} (hSc : S = conjSubgroup c T)
    (hB : B = conjSubgroup c (secA T T₁)) {t : G} (ht : t ∈ S) {x : G} (hx : x ∈ B) :
    t * x * t⁻¹ ∈ B := by
  subst hSc hB
  have h1 := conjSubgroup_secA (T := conjSubgroup c T) (T₁ := conjSubgroup c T₁)
    (Subgroup.le_normalizer ht)
  rw [secA_conjSubgroup_eq] at h1
  have := conj_mem_conjSubgroup t hx
  rwa [h1] at this

theorem conj_mem_of_commutator_mem {N : Subgroup G} {t u : G} (hu : u ∈ N) (hc : ⁅u, t⁆ ∈ N) :
    t * u * t⁻¹ ∈ N := by
  have e : t * u * t⁻¹ = ⁅u, t⁆⁻¹ * u := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact N.mul_mem (N.inv_mem hc) hu

theorem mem_normalizer_sup₃ [Finite G] {P₁ P₂ P₃ : Subgroup G} {s : G}
    (h₁ : ∀ x ∈ P₁, s * x * s⁻¹ ∈ P₁ ⊔ P₂ ⊔ P₃) (h₂ : ∀ x ∈ P₂, s * x * s⁻¹ ∈ P₁ ⊔ P₂ ⊔ P₃)
    (h₃ : ∀ x ∈ P₃, s * x * s⁻¹ ∈ P₁ ⊔ P₂ ⊔ P₃) :
    s ∈ Subgroup.normalizer ((P₁ ⊔ P₂ ⊔ P₃ : Subgroup G) : Set G) := by
  have hle : ∀ P : Subgroup G, (∀ x ∈ P, s * x * s⁻¹ ∈ P₁ ⊔ P₂ ⊔ P₃) →
      conjSubgroup s P ≤ P₁ ⊔ P₂ ⊔ P₃ := by
    intro P hP y hy
    have := hP (s⁻¹ * y * s) (mem_conjSubgroup.1 hy)
    simpa [mul_assoc] using this
  rw [mem_normalizer_iff_conjSubgroup_eq]
  refine conjSubgroup_eq_of_le ?_
  rw [conjSubgroup_sup_eq_sup, conjSubgroup_sup_eq_sup]
  exact sup_le (sup_le (hle _ h₁) (hle _ h₂)) (hle _ h₃)

end Conj

end CFSG.CGT.Timmesfeld75
