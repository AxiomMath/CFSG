module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Subs5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS5

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv

@[expose] def evenSet : Finset (Perm (Fin 5)) := Finset.univ.filter fun σ => Perm.sign σ = 1

@[expose] def threeSet : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun σ => σ ≠ 1 ∧ σ ^ 3 = 1 ∧ (Finset.univ.filter fun i => σ i = i).card = 2

theorem mem_threeSet_of {σ : Perm (Fin 5)} (h : σ.IsThreeCycle) : σ ∈ threeSet := by
  have hord : orderOf σ = 3 := h.orderOf
  have h3 : σ ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one σ
  have h1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hsupp : σ.support.card = 3 := Equiv.Perm.IsThreeCycle.card_support h
  have hcard : (Finset.univ.filter fun i => σ i = i).card + σ.support.card = 5 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 5)))
      (fun i => σ i = i)
    simpa [Equiv.Perm.support] using this
  simp only [threeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨h1, h3, by omega⟩

theorem mem_evenSet {σ : Perm (Fin 5)} : σ ∈ evenSet ↔ Perm.sign σ = 1 := by
  simp [evenSet]

theorem three_from_V : ∀ σ ∈ evenSet, σ 4 = 0 → ∀ c ∈ threeSet,
    ∃ v₀ ∈ Vset, ∃ v₁ ∈ Vset, ∃ v₂ ∈ Vset, ∃ v₃ ∈ Vset,
      c = v₀ * σ * v₁ * σ * v₂ * σ * v₃ := by
  decide +kernel

theorem exists_V_to_zero : ∀ σ ∈ evenSet, σ 4 ≠ 4 → ∃ v ∈ Vset, (v * σ) 4 = 0 := by
  decide +kernel

theorem alt_le_of_V (Λ : Subgroup (Perm (Fin 5))) (hV : Vstd ≤ Λ) {σ : Perm (Fin 5)}
    (hσΛ : σ ∈ Λ) (hσ : σ 4 ≠ 4) (hev : Perm.sign σ = 1) : alternatingGroup (Fin 5) ≤ Λ := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro c hc
  obtain ⟨v, hv, hv0⟩ := exists_V_to_zero σ (mem_evenSet.2 hev) hσ
  have hvΛ : v ∈ Λ := hV hv
  have hσ'Λ : v * σ ∈ Λ := Λ.mul_mem hvΛ hσΛ
  have hσ'ev : v * σ ∈ evenSet := by
    rw [mem_evenSet, map_mul, hev, mul_one]
    have := Vset_sub_A4 v hv
    simpa [mem_A4set] using (mem_A4set v).1 this |>.2
  obtain ⟨v₀, h₀, v₁, h₁, v₂, h₂, v₃, h₃, e⟩ := three_from_V (v * σ) hσ'ev hv0 c
    (mem_threeSet_of hc)
  rw [e]
  exact Λ.mul_mem (Λ.mul_mem (Λ.mul_mem (Λ.mul_mem (Λ.mul_mem (Λ.mul_mem (hV h₀) hσ'Λ) (hV h₁))
    hσ'Λ) (hV h₂)) hσ'Λ) (hV h₃)

theorem Eset_sq : ∀ a ∈ Eset, a * a = 1 := by decide +kernel

theorem Eset_comm : ∀ a ∈ Eset, ∀ b ∈ Eset, a * b = b * a := by decide +kernel

theorem table_dec : ∀ a ∈ Eset, ∀ b ∈ Eset,
    16 ≤ (four a b).card * (fixOf a b).card → (four a b).card * (fixOf a b).card = 16 := by
  decide +kernel

theorem card_mul_fix_eq_of_le_Estd (P : Subgroup (Perm (Fin 5))) (hP : P ≤ Estd)
    (hff : 16 ≤ Nat.card P * Nat.card (FixΔ P)) : Nat.card P * Nat.card (FixΔ P) = 16 := by
  have hsq : ∀ a ∈ P, a * a = 1 := fun a ha => Eset_sq a (hP ha)
  have hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb => Eset_comm a (hP ha) b (hP hb)
  obtain ⟨a, haP, b, hbP, -, hcardP, hfix⟩ := exists_four_card P hsq hc
  rw [hcardP, hfix] at hff ⊢
  exact table_dec a (hP haP) b (hP hbP) hff

end CFSG.QuasithinUnique.A5.S2
