module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON

open Subgroup

theorem exists_step {E : Type*} [Group E] [Finite E] (H : Subgroup E) :
    ∃ a : E, H = ⊤ ∨ (a ∉ H ∧ 2 * Nat.card H ≤ Nat.card (H ⊔ zpowers a : Subgroup E)) := by
  by_cases hH : H = ⊤
  · exact ⟨1, Or.inl hH⟩
  · obtain ⟨a, ha⟩ : ∃ a : E, a ∉ H := by
      by_contra hcon
      push Not at hcon
      exact hH (eq_top_iff.2 fun x _ => hcon x)
    refine ⟨a, Or.inr ⟨ha, ?_⟩⟩
    have hle : H ≤ H ⊔ zpowers a := le_sup_left
    have hne : H ≠ H ⊔ zpowers a := fun h =>
      ha (h ▸ (le_sup_right : zpowers a ≤ H ⊔ zpowers a) (mem_zpowers a))
    have hdvd : Nat.card H ∣ Nat.card (H ⊔ zpowers a : Subgroup E) := Subgroup.card_dvd_of_le hle
    have hlt : Nat.card H < Nat.card (H ⊔ zpowers a : Subgroup E) := by
      refine lt_of_le_of_ne (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle))
        fun h => hne ?_
      exact Subgroup.eq_of_le_of_card_ge hle h.symm.le
    obtain ⟨k, hk⟩ := hdvd
    have hpos : 0 < Nat.card H := Nat.card_pos
    rw [hk] at hlt ⊢
    have : 1 < k := by
      by_contra hk1
      push Not at hk1
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with rfl | rfl <;> simp at hlt
    calc 2 * Nat.card H ≤ k * Nat.card H := Nat.mul_le_mul_right _ this
      _ = Nat.card H * k := mul_comm _ _

theorem exists_gen_three {E : Type*} [Group E] [Finite E] (hcard : Nat.card E ≤ 8) :
    ∃ a b c : E, closure ({a, b, c} : Set E) = ⊤ := by
  obtain ⟨a, ha⟩ := exists_step (⊥ : Subgroup E)
  obtain ⟨b, hb⟩ := exists_step (zpowers a : Subgroup E)
  obtain ⟨c, hc⟩ := exists_step ((zpowers a : Subgroup E) ⊔ zpowers b)
  refine ⟨a, b, c, ?_⟩
  have e1 : closure ({a, b, c} : Set E) = zpowers a ⊔ zpowers b ⊔ zpowers c := by
    apply le_antisymm
    · rw [closure_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact mem_sup_left (mem_sup_left (mem_zpowers _))
      · exact mem_sup_left (mem_sup_right (mem_zpowers _))
      · exact mem_sup_right (mem_zpowers _)
    · refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le] <;> apply subset_closure <;> simp
  rw [e1]
  have hsup : ∀ H K : Subgroup E, H = ⊤ → H ≤ H ⊔ K := fun H K _ => le_sup_left
  rcases ha with ha | ⟨-, ha⟩
  · rw [eq_top_iff]
    intro x _
    have : x ∈ (⊥ : Subgroup E) := by rw [ha]; trivial
    rw [Subgroup.mem_bot] at this
    subst this
    exact one_mem _
  · rw [bot_sup_eq, Subgroup.card_bot] at ha
    rcases hb with hb | ⟨-, hb⟩
    · rw [eq_top_iff]
      intro x _
      have : x ∈ (zpowers a : Subgroup E) := by rw [hb]; trivial
      exact mem_sup_left (mem_sup_left this)
    · rcases hc with hc | ⟨-, hc⟩
      · rw [eq_top_iff]
        intro x _
        have : x ∈ (zpowers a ⊔ zpowers b : Subgroup E) := by rw [hc]; trivial
        exact mem_sup_left this
      · apply Subgroup.eq_top_of_le_card
        calc Nat.card E ≤ 8 := hcard
          _ ≤ Nat.card (zpowers a ⊔ zpowers b ⊔ zpowers c : Subgroup E) := by
            have h1 : 2 * 1 ≤ Nat.card (zpowers a : Subgroup E) := ha
            have h2 : 2 * Nat.card (zpowers a : Subgroup E) ≤
                Nat.card (zpowers a ⊔ zpowers b : Subgroup E) := hb
            have h3 := hc
            omega

theorem card_mulAut_le {E : Type*} [Group E] [Finite E] (hcard : Nat.card E ≤ 8) :
    Nat.card (MulAut E) ≤ 512 := by
  obtain ⟨a, b, c, hcl⟩ := exists_gen_three hcard
  let F : MulAut E → E × E × E := fun σ => (σ a, σ b, σ c)
  have hF : Function.Injective F := by
    intro σ τ h
    have h1 : σ a = τ a := congrArg Prod.fst h
    have h2 : σ b = τ b := congrArg (fun p => p.2.1) h
    have h3 : σ c = τ c := congrArg (fun p => p.2.2) h
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ closure ({a, b, c} : Set E) := by rw [hcl]; trivial
    have := MonoidHom.eqOn_closure (f := (σ : E →* E)) (g := (τ : E →* E))
      (s := ({a, b, c} : Set E)) (by
        intro y hy
        rcases hy with rfl | rfl | rfl
        · exact h1
        · exact h2
        · exact h3) hx
    exact this
  have hcardE : Nat.card (E × E × E) ≤ 512 := by
    rw [Nat.card_prod, Nat.card_prod]
    calc Nat.card E * (Nat.card E * Nat.card E) ≤ 8 * (8 * 8) :=
          Nat.mul_le_mul hcard (Nat.mul_le_mul hcard hcard)
      _ = 512 := by decide
  exact (Nat.card_le_card_of_injective F hF).trans hcardE

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON
