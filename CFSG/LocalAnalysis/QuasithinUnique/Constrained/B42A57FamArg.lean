module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57R2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57GenCore

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Equiv

variable {S : Type} [CommGroup S] [Finite S] {ρ : Perm (Fin 7) →* MulAut S}
  {E₀ : Subgroup (Perm (Fin 7))}

@[expose] def famSub (ρ : Perm (Fin 7) →* MulAut S) (F₀ : Subgroup S) (σ : Perm (Fin 7)) :
    Subgroup S :=
  F₀.map (ρ σ).toMonoidHom

omit [Finite S] in
theorem mem_famSub {F₀ : Subgroup S} {σ : Perm (Fin 7)} {v : S} :
    v ∈ famSub ρ F₀ σ ↔ (ρ σ)⁻¹ v ∈ F₀ := by
  unfold famSub
  rw [Subgroup.mem_map_equiv]
  rfl

omit [Finite S] in
theorem card_famSub (F₀ : Subgroup S) (σ : Perm (Fin 7)) :
    Nat.card (famSub ρ F₀ σ) = Nat.card F₀ :=
  Subgroup.card_map_of_injective (ρ σ).injective

omit [Finite S] in
theorem famSub_fixed {F₀ : Subgroup S} {X : List (Perm (Fin 7))}
    (hF : ∀ x ∈ X, ∀ w ∈ F₀, ρ x w = w) {σ : Perm (Fin 7)} {v : S} (hv : v ∈ famSub ρ F₀ σ) :
    ∀ x ∈ X, ρ (σ * x * σ⁻¹) v = v := by
  intro x hx
  have hw : (ρ σ)⁻¹ v ∈ F₀ := mem_famSub.1 hv
  have := hF x hx _ hw
  rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, this]
  simp

omit [Finite S] in
theorem fixed_alt (D : MinOffData ρ E₀) {v : S}
    (hv : ∀ σ ∈ alternatingGroup (Fin 7), ρ σ v = v) : v = 1 := by
  set U : Subgroup S := Cs ρ (alternatingGroup (Fin 7)) with hU
  have hUinv : ∀ σ ∈ alternatingGroup (Fin 7), ∀ u ∈ U, ρ σ u ∈ U := by
    intro σ hσ u hu
    have := (mem_Cs ρ).1 hu σ hσ
    rw [this]
    exact hu
  rcases D.irr U hUinv with hbot | htop
  · have : v ∈ U := (mem_Cs ρ).2 hv
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  · exfalso
    have h3 : swap (0 : Fin 7) 1 * swap 0 2 ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      decide
    have : ρ (swap (0 : Fin 7) 1 * swap 0 2) = 1 := by
      apply MulEquiv.ext
      intro u
      have hu : u ∈ U := by rw [htop]; trivial
      exact (mem_Cs ρ).1 hu _ h3
    have h4 : swap (0 : Fin 7) 1 * swap 0 2 = 1 := D.inj (by rw [this, map_one])
    exact absurd h4 (by decide +kernel)

omit [Finite S] in
theorem famSub_inter_bot (D : MinOffData ρ E₀) {F₀ : Subgroup S} {X : List (Perm (Fin 7))}
    (hF : ∀ x ∈ X, ∀ w ∈ F₀, ρ x w = w) {σ τ : Perm (Fin 7)} (e : GenEntry 7) (he : e.Ok)
    (hT : e.T = X) (hcs : e.conjugators = [σ, τ]) :
    famSub ρ F₀ σ ⊓ famSub ρ F₀ τ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  apply fixed_alt D
  intro g hg
  have hcl := e.alt_le_closure (by norm_num) he hg
  have hmem : v ∈ Cs ρ (Subgroup.closure {x | ∃ c ∈ e.conjugators, ∃ t ∈ e.T, x = c * t * c⁻¹}) := by
    rw [mem_Cs_closure]
    rintro _ ⟨c, hc, t, ht, rfl⟩
    rw [hcs] at hc
    rw [hT] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact famSub_fixed hF hv.1 t ht
    · exact famSub_fixed hF hv.2 t ht
  exact (mem_Cs ρ).1 hmem g hcl

theorem family_false (D : MinOffData ρ E₀) {F₀ : Subgroup S} {X : List (Perm (Fin 7))}
    (hF : ∀ x ∈ X, ∀ w ∈ F₀, ρ x w = w) (Xt : List (List ℕ))
    (cj : List (List (Fin 7 × Fin 7))) (tb : List (ℕ × ℕ × List (List ℕ)))
    (hok : ∀ e ∈ tb.map (fun t => (⟨X, Xt, [cj.getD t.1 [], cj.getD t.2.1 []], t.2.2⟩ : GenEntry 7)),
      e.Ok)
    (hcov : ∀ i j : Fin 11, i < j → ∃ t ∈ tb, t.1 = i.val ∧ t.2.1 = j.val)
    (hc4 : 4 ≤ Nat.card F₀) (hS : Nat.card S ≤ 8 * Nat.card F₀) : False := by
  let σ : Fin 11 → Perm (Fin 7) := fun i => GenEntry.swapProd (cj.getD i.val [])
  have hd : ∀ i j : Fin 11, i < j → famSub ρ F₀ (σ i) ⊓ famSub ρ F₀ (σ j) = ⊥ := by
    intro i j hij
    obtain ⟨t, ht, h1, h2⟩ := hcov i j hij
    have heok := hok (⟨X, Xt, [cj.getD t.1 [], cj.getD t.2.1 []], t.2.2⟩ : GenEntry 7)
      (List.mem_map.2 ⟨t, ht, rfl⟩)
    refine famSub_inter_bot D hF (σ := σ i) (τ := σ j)
      (⟨X, Xt, [cj.getD t.1 [], cj.getD t.2.1 []], t.2.2⟩ : GenEntry 7) heok rfl ?_
    show [cj.getD t.1 [], cj.getD t.2.1 []].map GenEntry.swapProd = [σ i, σ j]
    rw [h1, h2]
    rfl
  refine family_contradiction (fun i : Fin 11 => famSub ρ F₀ (σ i)) (c := Nat.card F₀)
    (fun i => card_famSub F₀ _) ?_ le_rfl hc4 hS
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hd i j h
  · rw [inf_comm]
    exact hd j i h

end CFSG.QuasithinUnique.B42A57
