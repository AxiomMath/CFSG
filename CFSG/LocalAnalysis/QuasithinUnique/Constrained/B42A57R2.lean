module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Rho
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Fam

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Equiv

variable {S : Type} [CommGroup S] [Finite S]

structure MinOffData (ρ : Perm (Fin 7) →* MulAut S) (E₀ : Subgroup (Perm (Fin 7))) : Prop where
  inj : Function.Injective ρ
  irr : ∀ U : Subgroup S, (∀ σ ∈ alternatingGroup (Fin 7), ∀ u ∈ U, ρ σ u ∈ U) → U = ⊥ ∨ U = ⊤
  card_S : Nat.card S ≤ Nat.card E₀ * Nat.card (Cs ρ E₀)
  big : 32 ≤ Nat.card S
  max : ∀ (σ : Perm (Fin 7)) (B : Subgroup (Perm (Fin 7))), B ≤ conjE σ E₀ → B ≠ ⊥ →
    Nat.card (conjE σ E₀) = 2 * Nat.card B → Cs ρ B = Cs ρ (conjE σ E₀)

variable {ρ : Perm (Fin 7) →* MulAut S} {E₀ : Subgroup (Perm (Fin 7))}

theorem swap_mul_self' (a b : Fin 7) : swap a b * swap a b = 1 := Equiv.swap_mul_self a b

theorem swap_ne_one' {a b : Fin 7} (h : a ≠ b) : swap a b ≠ 1 := by
  intro h1
  have := congrArg (fun f : Perm (Fin 7) => f a) h1
  simp [Equiv.swap_apply_left] at this
  exact h this.symm

theorem swap_mem_conjE {σ : Perm (Fin 7)} {a b a' b' : Fin 7} (ha : σ a = a') (hb : σ b = b')
    (h : swap a b ∈ E₀) : swap a' b' ∈ conjE σ E₀ := by
  rw [mem_conjE]
  have : σ⁻¹ * swap a' b' * σ = swap a b := by
    have e := Equiv.swap_apply_apply σ a b
    rw [← ha, ← hb, e]
    group
  rw [this]
  exact h

theorem exists_third (a b c d : Fin 7) :
    ∃ e f : Fin 7, e ≠ f ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧ f ≠ a ∧ f ≠ b ∧ f ≠ c ∧ f ≠ d := by
  revert a b c d
  decide +kernel

theorem R2_false (D : MinOffData ρ E₀) (hcard : Nat.card E₀ = 4) {a b c d : Fin 7}
    (hnd : [a, b, c, d].Nodup) (h1 : swap a b ∈ E₀) (h2 : swap c d ∈ E₀) : False := by
  have hab : a ≠ b := by simp at hnd; exact hnd.1.1
  have hcd : c ≠ d := by simp at hnd; exact hnd.2.2
  have hpair : ∀ a' b' c' d' : Fin 7, [a', b', c', d'].Nodup →
      Cs ρ (Subgroup.closure ({swap a' b'} : Set (Perm (Fin 7)))) =
        Cs ρ (Subgroup.closure ({swap c' d'} : Set (Perm (Fin 7)))) := by
    intro a' b' c' d' hnd'
    obtain ⟨σ, hσ⟩ := exists_perm_list [a, b, c, d] [a', b', c', d'] hnd hnd' rfl
    have e0 : σ a = a' := hσ 0 (by simp)
    have e1 : σ b = b' := hσ 1 (by simp)
    have e2 : σ c = c' := hσ 2 (by simp)
    have e3 : σ d = d' := hσ 3 (by simp)
    have ha'b' : a' ≠ b' := by simp at hnd'; exact hnd'.1.1
    have hc'd' : c' ≠ d' := by simp at hnd'; exact hnd'.2.2
    have hm1 := swap_mem_conjE e0 e1 h1
    have hm2 := swap_mem_conjE e2 e3 h2
    have hc4 : Nat.card (conjE σ E₀) = 2 * 2 := by rw [card_conjE, hcard]
    have k1 : Cs ρ (Subgroup.closure ({swap a' b'} : Set (Perm (Fin 7)))) = Cs ρ (conjE σ E₀) := by
      apply D.max σ
      · exact (Subgroup.closure_le _).2 (by simpa using hm1)
      · intro h
        have := card_closure_single (swap_mul_self' a' b') (swap_ne_one' ha'b')
        rw [h] at this
        simp at this
      · rw [hc4, card_closure_single (swap_mul_self' a' b') (swap_ne_one' ha'b')]
    have k2 : Cs ρ (Subgroup.closure ({swap c' d'} : Set (Perm (Fin 7)))) = Cs ρ (conjE σ E₀) := by
      apply D.max σ
      · exact (Subgroup.closure_le _).2 (by simpa using hm2)
      · intro h
        have := card_closure_single (swap_mul_self' c' d') (swap_ne_one' hc'd')
        rw [h] at this
        simp at this
      · rw [hc4, card_closure_single (swap_mul_self' c' d') (swap_ne_one' hc'd')]
    rw [k1, k2]
  have hall : ∀ a' b' c' d' : Fin 7, a' ≠ b' → c' ≠ d' →
      Cs ρ (Subgroup.closure ({swap a' b'} : Set (Perm (Fin 7)))) =
        Cs ρ (Subgroup.closure ({swap c' d'} : Set (Perm (Fin 7)))) := by
    intro a' b' c' d' hab' hcd'
    obtain ⟨e, f, hef, hea, heb, hec, hed, hfa, hfb, hfc, hfd⟩ := exists_third a' b' c' d'
    have h1' := hpair a' b' e f (by simp [hab', hef, hea.symm, heb.symm, hfa.symm, hfb.symm])
    have h2' := hpair e f c' d' (by simp [hef, hcd', hec, hed, hfc, hfd])
    rw [h1', h2']
  set F : Subgroup S := Cs ρ (Subgroup.closure ({swap 0 1} : Set (Perm (Fin 7)))) with hF
  have hFinv : ∀ σ ∈ alternatingGroup (Fin 7), ∀ u ∈ F, ρ σ u ∈ F := by
    intro σ _ u hu
    rw [hF, mem_Cs_closure]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hτ : σ⁻¹ * swap 0 1 * σ = swap (σ⁻¹ 0) (σ⁻¹ 1) := by
      rw [Equiv.swap_apply_apply]
      simp
    have hne : σ⁻¹ 0 ≠ σ⁻¹ 1 := fun h => by simpa using σ⁻¹.injective h
    have hu' : u ∈ Cs ρ (Subgroup.closure ({swap (σ⁻¹ 0) (σ⁻¹ 1)} : Set (Perm (Fin 7)))) := by
      rw [← hall 0 1 (σ⁻¹ 0) (σ⁻¹ 1) (by decide) hne]
      exact hu
    have hfix := (mem_Cs_closure ρ).1 hu' (swap (σ⁻¹ 0) (σ⁻¹ 1)) rfl
    have e : swap 0 1 = σ * swap (σ⁻¹ 0) (σ⁻¹ 1) * σ⁻¹ := by
      rw [← hτ]; group
    rw [e, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_inv]
    have : (ρ σ)⁻¹ (ρ σ u) = u := by simp
    rw [this, hfix]
  rcases D.irr F hFinv with hbot | htop
  ·
    have hle : Cs ρ E₀ ≤ F := by
      have : Cs ρ E₀ ≤ Cs ρ (Subgroup.closure ({swap a b} : Set (Perm (Fin 7)))) :=
        Cs_anti ρ ((Subgroup.closure_le _).2 (by simpa using h1))
      rwa [hall a b 0 1 hab (by decide)] at this
    rw [hbot] at hle
    have h1' : Nat.card (Cs ρ E₀) = 1 := by
      have := Subgroup.card_le_of_le hle
      simp only [Subgroup.card_bot] at this
      have hpos : 0 < Nat.card (Cs ρ E₀) := Nat.card_pos
      omega
    have := D.card_S
    rw [hcard, h1'] at this
    have := D.big
    omega
  ·
    have : ρ (swap 0 1) = 1 := by
      apply MulEquiv.ext
      intro v
      have hv : v ∈ F := by rw [htop]; trivial
      exact (mem_Cs_closure ρ).1 hv (swap 0 1) rfl
    exact swap_ne_one' (by decide : (0 : Fin 7) ≠ 1) (D.inj (by rw [this, map_one]))

end CFSG.QuasithinUnique.B42A57
