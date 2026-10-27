module

public import CFSG.CGT.Timmesfeld75.Sec57Conj

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem normalizer_sup_secA_triple (hP : MaxPair T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    {g₂ g₃ : G} (h₂ : conjSubgroup g₂ T ≠ T) (h₃ : conjSubgroup g₃ T ≠ T)
    (h₂₃ : conjSubgroup g₂ T ≠ conjSubgroup g₃ T)
    (hL₂ : normIn (conjSubgroup g₂ T) T ≠ ⊥) (hL₃ : normIn (conjSubgroup g₃ T) T ≠ ⊥)
    (hL₂₃ : normIn (conjSubgroup g₂ T) (conjSubgroup g₃ T) ≠ ⊥)
    (hL₃₂ : normIn (conjSubgroup g₃ T) (conjSubgroup g₂ T) ≠ ⊥) :
    T ⊔ conjSubgroup g₂ T ⊔ conjSubgroup g₃ T ≤ Subgroup.normalizer
      ((secA T T₁ ⊔ conjSubgroup g₂ (secA T T₁) ⊔ conjSubgroup g₃ (secA T T₁) : Subgroup G) :
        Set G) := by
  have hT₂ne : normIn T (conjSubgroup g₂ T) ≠ ⊥ := normIn_ne_bot_of_conj hP.wc h₂ hL₂
  have hT₃ne : normIn T (conjSubgroup g₃ T) ≠ ⊥ := normIn_ne_bot_of_conj hP.wc h₃ hL₃
  set A := secA T T₁ with hA
  have hA₀ : A ≤ A ⊔ conjSubgroup g₂ A ⊔ conjSubgroup g₃ A := le_sup_left.trans le_sup_left
  have hA₂ : conjSubgroup g₂ A ≤ A ⊔ conjSubgroup g₂ A ⊔ conjSubgroup g₃ A :=
    le_sup_right.trans le_sup_left
  have hA₃ : conjSubgroup g₃ A ≤ A ⊔ conjSubgroup g₂ A ⊔ conjSubgroup g₃ A := le_sup_right
  have hgenT : T ≤ Subgroup.normalizer
      ((A ⊔ conjSubgroup g₂ A ⊔ conjSubgroup g₃ A : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup₃ (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · have h1 : conjSubgroup t A = A := conjSubgroup_secA (T := T) (T₁ := T₁)
        (Subgroup.le_normalizer ht)
      have := conj_mem_conjSubgroup t hx
      rw [h1] at this
      exact hA₀ this
    · have hc := commutator_conj_secA_le_of_ne hP hS hI (h := g₂) h₂ hL₂ x hx t ht
      exact conj_mem_of_commutator_mem (hA₂ hx) (hA₀ hc)
    · have hc := commutator_conj_secA_le_of_ne hP hS hI (h := g₃) h₃ hL₃ x hx t ht
      exact conj_mem_of_commutator_mem (hA₃ hx) (hA₀ hc)
  have hgenT₂ : conjSubgroup g₂ T ≤ Subgroup.normalizer
      ((A ⊔ conjSubgroup g₂ A ⊔ conjSubgroup g₃ A : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup₃ (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · have hxA : x ∈ conjSubgroup g₂⁻¹ (conjSubgroup g₂ A) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
        exact hx
      have hc := commutator_secA_conj_pair hP hS hI (c := g₂) (h := g₂⁻¹) (S₂ := T) rfl rfl
        (by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]) h₂.symm hT₂ne
        x hxA t ht
      exact conj_mem_of_commutator_mem (hA₀ hx) (hA₂ hc)
    · exact hA₂ (conj_mem_secA_conj_pair (c := g₂) (T := T) (T₁ := T₁) rfl rfl ht hx)
    · have hxA : x ∈ conjSubgroup (g₃ * g₂⁻¹) (conjSubgroup g₂ A) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
        exact hx
      have hc := commutator_secA_conj_pair hP hS hI (c := g₂) (h := g₃ * g₂⁻¹)
        (S₂ := conjSubgroup g₃ T) rfl rfl
        (by rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]) h₂₃.symm hL₃₂ x hxA t ht
      exact conj_mem_of_commutator_mem (hA₃ hx) (hA₂ hc)
  have hgenT₃ : conjSubgroup g₃ T ≤ Subgroup.normalizer
      ((A ⊔ conjSubgroup g₂ A ⊔ conjSubgroup g₃ A : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup₃ (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · have hxA : x ∈ conjSubgroup g₃⁻¹ (conjSubgroup g₃ A) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
        exact hx
      have hc := commutator_secA_conj_pair hP hS hI (c := g₃) (h := g₃⁻¹) (S₂ := T) rfl rfl
        (by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]) h₃.symm hT₃ne
        x hxA t ht
      exact conj_mem_of_commutator_mem (hA₀ hx) (hA₃ hc)
    · have hxA : x ∈ conjSubgroup (g₂ * g₃⁻¹) (conjSubgroup g₃ A) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
        exact hx
      have hc := commutator_secA_conj_pair hP hS hI (c := g₃) (h := g₂ * g₃⁻¹)
        (S₂ := conjSubgroup g₂ T) rfl rfl
        (by rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]) h₂₃ hL₂₃ x hxA t ht
      exact conj_mem_of_commutator_mem (hA₂ hx) (hA₃ hc)
    · exact hA₃ (conj_mem_secA_conj_pair (c := g₃) (T := T) (T₁ := T₁) rfl rfl ht hx)
  exact sup_le (sup_le hgenT hgenT₂) hgenT₃

end CFSG.CGT.Timmesfeld75
