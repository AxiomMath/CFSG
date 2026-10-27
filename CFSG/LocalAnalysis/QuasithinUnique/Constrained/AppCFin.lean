module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem Eset_sq : ∀ a ∈ Eset, a * a = 1 := by decide +kernel

theorem Eset_comm : ∀ a ∈ Eset, ∀ b ∈ Eset, a * b = b * a := by decide +kernel

theorem four_eq_Eset : ∀ a ∈ Eset, ∀ b ∈ Eset, (four a b).card * (fixOf a b).card = 16 →
    four a b ≠ {1} → (∀ d ∈ Dset, ∀ g ∈ four a b, d * g * d⁻¹ ∈ four a b) →
      four a b = Eset := by
  decide +kernel

theorem fix_four_Eset : ∀ a ∈ Eset, ∀ b ∈ Eset, four a b = Eset → (fixOf a b).card = 4 := by
  decide +kernel

theorem fix_comm : ∀ f : Fin 5 → ZMod 2, isEven f → (∀ σ ∈ Eset, pact σ f = f) →
    ∃ t ∈ Eset, ∃ w : Fin 5 → ZMod 2, isEven w ∧ pact t w + w = f := by
  decide +kernel

theorem fin_E (K : Subgroup (Perm (Fin 5))) (hK : K ≤ Estd) (hne : K ≠ ⊥)
    (hnorm : ∀ d ∈ Dstd, ∀ g ∈ K, d * g * d⁻¹ ∈ K)
    (hcard : Nat.card K * Nat.card (FixΔ K) = 16) : K = Estd := by
  have hsq : ∀ a ∈ K, a * a = 1 := fun a ha => Eset_sq a ((mem_Estd a).1 (hK ha))
  have hcm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    Eset_comm a ((mem_Estd a).1 (hK ha)) b ((mem_Estd b).1 (hK hb))
  obtain ⟨a, haK, b, hbK, hab, hcP, hfix⟩ := exists_four_card K hsq hcm
  rw [hcP, hfix] at hcard
  have haE := (mem_Estd a).1 (hK haK)
  have hbE := (mem_Estd b).1 (hK hbK)
  have h1 : four a b ≠ {1} := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro g hg
    have := (hab g).1 hg
    rw [h, Finset.mem_singleton] at this
    simp [this]
  have h2 : ∀ d ∈ Dset, ∀ g ∈ four a b, d * g * d⁻¹ ∈ four a b := by
    intro d hd g hg
    exact (hab _).1 (hnorm d ((mem_Dstd d).2 hd) g ((hab g).2 hg))
  have h3 := four_eq_Eset a haE b hbE hcard h1 h2
  ext g
  rw [hab g, h3, mem_Estd]

theorem card_fix_Estd : Nat.card (FixΔ Estd) = 4 := by
  have hsq : ∀ a ∈ Estd, a * a = 1 := fun a ha => Eset_sq a ((mem_Estd a).1 ha)
  have hcm : ∀ a ∈ Estd, ∀ b ∈ Estd, a * b = b * a := fun a ha b hb =>
    Eset_comm a ((mem_Estd a).1 ha) b ((mem_Estd b).1 hb)
  obtain ⟨a, haK, b, hbK, hab, hcP, hfix⟩ := exists_four_card Estd hsq hcm
  have h3 : four a b = Eset := Finset.ext fun g => by rw [← hab g, mem_Estd]
  rw [hfix]
  exact fix_four_Eset a ((mem_Estd a).1 haK) b ((mem_Estd b).1 hbK) h3

theorem ff_classify : ∀ a ∈ Dset, ∀ b ∈ Dset, a * a = 1 → b * b = 1 → a * b = b * a →
    (four a b).card * (fixOf a b).card = 16 →
      four a b = {1} ∨ four a b = {1, swap 0 1} ∨ four a b = {1, swap 2 3} ∨ four a b = Eset := by
  decide +kernel

theorem classify_P (P : Subgroup (Perm (Fin 5))) (hP : P ≤ Dstd) (hsq : ∀ a ∈ P, a * a = 1)
    (hcm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hcard : Nat.card P * Nat.card (FixΔ P) = 16) :
    (∀ g, g ∈ P ↔ g = 1) ∨ (∀ g, g ∈ P ↔ g = 1 ∨ g = swap 0 1) ∨
      (∀ g, g ∈ P ↔ g = 1 ∨ g = swap 2 3) ∨ (∀ g, g ∈ P ↔ g ∈ Eset) := by
  obtain ⟨a, haP, b, hbP, hab, hcP, hfix⟩ := exists_four_card P hsq hcm
  rw [hcP, hfix] at hcard
  have h := ff_classify a ((mem_Dstd a).1 (hP haP)) b ((mem_Dstd b).1 (hP hbP)) (hsq a haP)
    (hsq b hbP) (hcm a haP b hbP) hcard
  rcases h with h | h | h | h
  · left
    intro g
    rw [hab g, h, Finset.mem_singleton]
  · right; left
    intro g
    rw [hab g, h, Finset.mem_insert, Finset.mem_singleton]
  · right; right; left
    intro g
    rw [hab g, h, Finset.mem_insert, Finset.mem_singleton]
  · right; right; right
    intro g
    rw [hab g, h]

theorem swap_sq01 : swap (0 : Fin 5) 1 * swap 0 1 = 1 := by decide +kernel

theorem swap_sq23 : swap (2 : Fin 5) 3 * swap 2 3 = 1 := by decide +kernel

theorem swap_comm_01_23 : swap (0 : Fin 5) 1 * swap 2 3 = swap 2 3 * swap 0 1 := by
  decide +kernel

theorem t1_mem_Eset : swap (0 : Fin 5) 1 ∈ Eset := by decide +kernel

theorem t2_mem_Eset : swap (2 : Fin 5) 3 ∈ Eset := by decide +kernel

theorem mem_Eset_iff (g : Perm (Fin 5)) :
    g ∈ Eset ↔ g = 1 ∨ g = swap 0 1 ∨ g = swap 2 3 ∨ g = swap 0 1 * swap 2 3 := by
  simp [Eset]

theorem E_comm : ∀ w₁ w₂ : Fin 5 → ZMod 2,
    pact (swap 2 3) w₁ + w₂ = pact (swap 0 1) w₂ + w₁ →
      pact (swap 2 3) w₁ = w₁ ∧ pact (swap 0 1) w₂ = w₂ := by
  decide +kernel

theorem fixE_of : ∀ w : Fin 5 → ZMod 2, pact (swap 0 1) w = w → pact (swap 2 3) w = w →
    ∀ σ ∈ Eset, pact σ w = w := by
  decide +kernel

theorem conj_swap_of : ∀ σ ∈ Dset, Perm.sign σ = 1 → σ ∉ Eset →
    σ⁻¹ * swap 0 1 * σ = swap 2 3 ∧ σ⁻¹ * swap 2 3 * σ = swap 0 1 := by
  decide +kernel

end CFSG.QuasithinUnique.AppC
