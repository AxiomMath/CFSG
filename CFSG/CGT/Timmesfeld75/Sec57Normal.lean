module

public import CFSG.CGT.Timmesfeld75.Sec57Basic
public import CFSG.CGT.Timmesfeld75.Sec57Conj

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Prelim

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {g x₁ : G}

theorem Sec57Cfg.normIn_ne_bot_mid (c : Sec57Cfg T T₁ g) (hx₁ : T₁ = conjSubgroup x₁ T) :
    normIn (conjSubgroup g T) T₁ ≠ ⊥ ∧ normIn T₁ (conjSubgroup g T) ≠ ⊥ := by
  have hP := c.hy.pair
  have hS₁ : Sec3 T T₁ := hP.sec3 c.hS
  have hu : IsUIdx T T₁ x₁ :=
    ⟨by rw [← hx₁]; exact hP.ne, by rw [← hx₁, hS₁.card_normIn_swap]⟩
  have hcomm := c.hcomm x₁ hu
  have hA₁ne : conjSubgroup x₁ (secA T T₁) ≠ ⊥ := fun h => c.hA (conjSubgroup_eq_bot_iff.1 h)
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA₁ne
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.conj_secA_ne_bot
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have haT₁ : a ∈ T₁ := hx₁ ▸ conjSubgroup_mono secA_le_left ha
  have hbT₃ : b ∈ conjSubgroup g T := conjSubgroup_mono secA_le_left hb
  have hab : a * b = b * a := hcomm a ha b hb
  have hwc₁ : IsWC T₁ := hx₁ ▸ c.hy.pair.wc.conj x₁
  have hwc₃ : IsWC (conjSubgroup g T) := c.hy.pair.wc.conj g
  refine ⟨Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨b, mem_normIn.2 ⟨hbT₃, ?_⟩⟩,
    fun h => hb1' (congrArg Subtype.val h)⟩,
    Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨a, mem_normIn.2 ⟨haT₁, ?_⟩⟩,
    fun h => ha1' (congrArg Subtype.val h)⟩⟩
  · exact hwc₁.centralizer_le_normalizer haT₁ ha1'
      (Subgroup.mem_centralizer_singleton_iff.2 hab.symm)
  · exact hwc₃.centralizer_le_normalizer hbT₃ hb1' (Subgroup.mem_centralizer_singleton_iff.2 hab)

end Prelim

theorem sec57Prelim :
    ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (g : G), Sec57Cfg T T₁ g →
      ∀ x₁ : G, T₁ = conjSubgroup x₁ T →
        ∀ y ∈ T ⊔ T₁ ⊔ conjSubgroup g T,
          conjSubgroup y (secA T T₁ ⊔ conjSubgroup x₁ (secA T T₁) ⊔ conjSubgroup g (secA T T₁)) =
            secA T T₁ ⊔ conjSubgroup x₁ (secA T T₁) ⊔ conjSubgroup g (secA T T₁) := by
  intro G _ T T₁ g c x₁ hx₁ y hy
  have : Finite G := c.hy.finite
  have hP := c.hy.pair
  have hne₁ : T₁ ≠ T := hP.ne
  have hL₁ : normIn T₁ T ≠ ⊥ := (hP.sec3 c.hS).cfg.ne₁
  have hL₃ : normIn T (conjSubgroup g T) ≠ ⊥ := normIn_ne_bot_of_conj hP.wc c.hgT c.normIn_ne_bot
  obtain ⟨hL₃₁, hL₁₃⟩ := c.normIn_ne_bot_mid hx₁
  set A := secA T T₁ with hA
  have hA₀ : A ≤ A ⊔ conjSubgroup x₁ A ⊔ conjSubgroup g A := le_sup_left.trans le_sup_left
  have hA₁ : conjSubgroup x₁ A ≤ A ⊔ conjSubgroup x₁ A ⊔ conjSubgroup g A :=
    le_sup_right.trans le_sup_left
  have hA₃ : conjSubgroup g A ≤ A ⊔ conjSubgroup x₁ A ⊔ conjSubgroup g A := le_sup_right
  have hgenT : T ≤ Subgroup.normalizer
      ((A ⊔ conjSubgroup x₁ A ⊔ conjSubgroup g A : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup₃ (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · have h1 : conjSubgroup t A = A := conjSubgroup_secA (T := T) (T₁ := T₁)
        (Subgroup.le_normalizer ht)
      have := conj_mem_conjSubgroup t hx
      rw [h1] at this
      exact hA₀ this
    · have hc := commutator_conj_secA_le_of_ne hP c.hS c.hI (h := x₁)
        (by rw [← hx₁]; exact hne₁) (by rw [← hx₁]; exact hL₁) x hx t ht
      exact conj_mem_of_commutator_mem (hA₁ hx) (hA₀ hc)
    · have hc := commutator_conj_secA_le_of_ne hP c.hS c.hI (h := g) c.hgT c.normIn_ne_bot x hx t ht
      exact conj_mem_of_commutator_mem (hA₃ hx) (hA₀ hc)
  have hgenT₁ : T₁ ≤ Subgroup.normalizer
      ((A ⊔ conjSubgroup x₁ A ⊔ conjSubgroup g A : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup₃ (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · have hxA : x ∈ conjSubgroup x₁⁻¹ (conjSubgroup x₁ A) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
        exact hx
      have hc := commutator_secA_conj_pair hP c.hS c.hI (c := x₁) (h := x₁⁻¹) (S₂ := T) hx₁ rfl
        (by rw [hx₁, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]) hne₁.symm
        hP.nontriv x hxA t ht
      exact conj_mem_of_commutator_mem (hA₀ hx) (hA₁ hc)
    · exact hA₁ (conj_mem_secA_conj_pair (c := x₁) (T := T) (T₁ := T₁) hx₁ rfl ht hx)
    · have hxA : x ∈ conjSubgroup (g * x₁⁻¹) (conjSubgroup x₁ A) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
        exact hx
      have hc := commutator_secA_conj_pair hP c.hS c.hI (c := x₁) (h := g * x₁⁻¹)
        (S₂ := conjSubgroup g T) hx₁ rfl
        (by rw [hx₁, conjSubgroup_conjSubgroup, inv_mul_cancel_right]) c.ne_mid hL₃₁ x hxA t ht
      exact conj_mem_of_commutator_mem (hA₃ hx) (hA₁ hc)
  have hgenT₃ : conjSubgroup g T ≤ Subgroup.normalizer
      ((A ⊔ conjSubgroup x₁ A ⊔ conjSubgroup g A : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup₃ (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · have hxA : x ∈ conjSubgroup g⁻¹ (conjSubgroup g A) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
        exact hx
      have hc := commutator_secA_conj_pair hP c.hS c.hI (c := g) (h := g⁻¹) (S₂ := T) rfl rfl
        (by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]) c.hgT.symm hL₃
        x hxA t ht
      exact conj_mem_of_commutator_mem (hA₀ hx) (hA₃ hc)
    · have hxA : x ∈ conjSubgroup (x₁ * g⁻¹) (conjSubgroup g A) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
        exact hx
      have hc := commutator_secA_conj_pair hP c.hS c.hI (c := g) (h := x₁ * g⁻¹) (S₂ := T₁) rfl rfl
        (by rw [hx₁, conjSubgroup_conjSubgroup, inv_mul_cancel_right]) c.ne_mid.symm hL₁₃
        x hxA t ht
      exact conj_mem_of_commutator_mem (hA₁ hx) (hA₃ hc)
    · exact hA₃ (conj_mem_secA_conj_pair (c := g) (T := T) (T₁ := T₁) rfl rfl ht hx)
  have hY : T ⊔ T₁ ⊔ conjSubgroup g T ≤ Subgroup.normalizer
      ((A ⊔ conjSubgroup x₁ A ⊔ conjSubgroup g A : Subgroup G) : Set G) :=
    sup_le (sup_le hgenT hgenT₁) hgenT₃
  exact mem_normalizer_iff_conjSubgroup_eq.1 (hY hy)

end CFSG.CGT.Timmesfeld75
