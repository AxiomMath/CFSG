module

public import CFSG.CGT.Foote81L6.Normalizer.SymFacts

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Equiv

private theorem mem_range_of_fix {σ : Perm (Fin 5)} (hσ : σ 4 = 4) :
    σ ∈ (Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 4 ↪ Fin 5)).range := by
  classical
  set ι := Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 4 ↪ Fin 5) with hι
  have hinj : Function.Injective ι := Perm.viaEmbeddingHom_injective _
  have hfix : ∀ τ : Perm (Fin 4), ι τ 4 = 4 := by
    intro τ
    rw [hι, Perm.viaEmbeddingHom_apply]
    apply Perm.viaEmbedding_apply_of_notMem
    rintro ⟨i, hi⟩
    fin_cases i <;> simp at hi
  set S := Finset.univ.filter fun σ : Perm (Fin 5) => σ 4 = 4
  set T := Finset.univ.image ι
  have hTS : T ⊆ S := by
    intro σ hσ
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hσ
    simp [S, hfix τ]
  have hcard : S.card ≤ T.card := by
    rw [perm_five_card_fix, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin]
    decide
  have hST := Finset.eq_of_subset_of_card_le hTS hcard
  have hσS : σ ∈ S := by simp [S, hσ]
  rw [← hST] at hσS
  obtain ⟨τ, -, hτ⟩ := Finset.mem_image.mp hσS
  exact ⟨τ, hτ⟩

namespace IsSymDirect

variable {X : Type*} [Group X] [Finite X] {d₀ d₁ : X} {φ : X →* Perm (Fin 5)}

theorem exists_sym_four (hφ : IsSymDirect d₀ d₁ φ) {D : Subgroup X} (hD : IsPGroup 2 D)
    (hDz : ∀ e ∈ D, e * (d₀ * d₁) = d₀ * d₁ * e) :
    ∃ M : Subgroup X, M ≤ Subgroup.normalClosure ({d₀} : Set X) ∧ D ≤ M ∧ d₀ ∈ M ∧ d₁ ∈ M ∧
      Nonempty (M ≃* Perm (Fin 4)) := by
  classical
  set X₀ := Subgroup.normalClosure ({d₀} : Set X)
  set ι := Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 4 ↪ Fin 5) with hι
  have hinj : Function.Injective ι := Perm.viaEmbeddingHom_injective _
  set φ₀ := hφ.normalClosureEquiv
  set M : Subgroup X := (ι.range.map φ₀.symm.toMonoidHom).map X₀.subtype with hM
  obtain ⟨-, -, -, -, -, hfix4⟩ := perm_five_cycle
  have hmem : ∀ g ∈ X₀, φ g 4 = 4 → g ∈ M := by
    intro g hg hg4
    refine ⟨⟨g, hg⟩, ⟨φ₀ ⟨g, hg⟩, mem_range_of_fix hg4, ?_⟩, rfl⟩
    simp
  have e : Perm (Fin 4) ≃* M :=
    ((MonoidHom.ofInjective hinj).trans (ι.range.equivMapOfInjective _ φ₀.symm.injective)).trans
      ((ι.range.map φ₀.symm.toMonoidHom).equivMapOfInjective _ X₀.subtype_injective)
  refine ⟨M, Subgroup.map_subtype_le _, fun g hg => hmem g (hφ.le_normalClosure_of_isPGroup hD hg)
    (hfix4 _ ?_), hmem d₀ hφ.mem₀ (by rw [hφ.map₀]; decide),
    hmem d₁ hφ.mem₁ (by rw [hφ.map₁]; decide), ⟨e.symm⟩⟩
  rw [← hφ.map₀, ← hφ.map₁, ← map_mul, ← map_mul, ← map_mul, hDz g hg]

theorem exists_not_mem (hφ : IsSymDirect d₀ d₁ φ) {M : Subgroup X}
    (hMX₀ : M ≤ Subgroup.normalClosure ({d₀} : Set X)) (hM₀ : d₀ ∈ M) (hM₁ : d₁ ∈ M)
    (ψ : M ≃* Perm (Fin 4)) {H : Subgroup X} (hMH : M ≤ H)
    (hX₀H : ¬ Subgroup.normalClosure ({d₀} : Set X) ≤ H) :
    ∃ x₀ ∈ Subgroup.normalClosure ({d₀} : Set X), x₀ ∉ H ∧ orderOf x₀ = 3 ∧
      x₀ * d₁ = d₁ * x₀ ∧ d₀ * x₀ * d₀⁻¹ = x₀⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set X₀ := Subgroup.normalClosure ({d₀} : Set X) with hX₀
  have hn : (5 : ℕ) = 4 ∨ (5 : ℕ) = 5 := Or.inr rfl
  set φ₀ := hφ.normalClosureEquiv
  obtain ⟨ht3, ht1, htc, htinv, hts, -⟩ := perm_five_cycle
  set t : Perm (Fin 5) := swap 0 4 * swap 0 1 with ht
  set x₀ : X := (φ₀.symm t : X) with hx₀
  have hx₀X₀ : x₀ ∈ X₀ := (φ₀.symm t).2
  have hφx₀ : φ x₀ = t := by
    rw [hx₀, ← hφ.normalClosureEquiv_apply, MulEquiv.apply_symm_apply]
  have hord : orderOf x₀ = 3 := by
    rw [hx₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime ht3 ht1
  have hcomm₁ : x₀ * d₁ = d₁ * x₀ :=
    hφ.injOn (Subgroup.mul_mem _ hx₀X₀ hφ.mem₁) (Subgroup.mul_mem _ hφ.mem₁ hx₀X₀)
      (by rw [map_mul, map_mul, hφx₀, hφ.map₁, htc])
  have hinv₀ : d₀ * x₀ * d₀⁻¹ = x₀⁻¹ :=
    hφ.injOn (Subgroup.mul_mem _ (Subgroup.mul_mem _ hφ.mem₀ hx₀X₀) (Subgroup.inv_mem _ hφ.mem₀))
      (Subgroup.inv_mem _ hx₀X₀)
      (by rw [map_mul, map_mul, map_inv, map_inv, hφx₀, hφ.map₀, htinv])
  have hcardM : Nat.card M = 24 := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hx₀M : x₀ ∉ M := by
    intro hxM
    obtain ⟨ψ', hψ₀, hψ₁⟩ := hφ.exists_normalized_four hn hM₀ hM₁ ψ
    obtain ⟨-, hucomm, hu2, -, hu01, -⟩ := perm_four_klein
    set χ : Perm (Fin 4) →* Perm (Fin 5) := φ.comp (M.subtype.comp ψ'.symm.toMonoidHom) with hχ
    have hχ₀ : χ (swap 0 1) = swap 0 1 := by
      rw [hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hψ₀]
      simp [hφ.map₀]
    have hχ₁ : χ (swap 2 3) = swap 2 3 := by
      rw [hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hψ₁]
      simp [hφ.map₁]
    set u : Perm (Fin 4) := swap 0 2 * swap 1 3
    set e : X := (ψ'.symm u : X) with he
    have heM : e ∈ M := (ψ'.symm u).2
    have hφe : φ e = χ u := rfl
    have hs := hts (χ u) (by rw [← map_mul, hu2, map_one])
      (by rw [← hχ₀, ← hχ₁, ← map_mul, ← map_mul, ← map_mul, hucomm])
      (by rw [← hχ₀, ← hχ₁, ← map_inv, ← map_mul, ← map_mul, hu01])
    have h5 : orderOf (φ (x₀ * e)) = 5 := by
      rw [map_mul, hφx₀, hφe]
      exact orderOf_eq_prime hs.1 hs.2
    have hdvd : orderOf (x₀ * e) ∣ 24 := by
      have h1 := orderOf_dvd_natCard (⟨x₀ * e, M.mul_mem hxM heM⟩ : M)
      rw [← Subgroup.orderOf_coe, hcardM] at h1
      exact h1
    have := (h5 ▸ orderOf_map_dvd φ (x₀ * e)).trans hdvd
    norm_num at this
  have hcardX₀ : Nat.card X₀ = 120 := by
    rw [Nat.card_congr φ₀.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  refine ⟨x₀, hx₀X₀, fun hx₀H => ?_, hord, hcomm₁, hinv₀⟩
  set H' := H ⊓ X₀
  have hMH' : M ≤ H' := le_inf hMH hMX₀
  have h1 : Nat.card H' ∣ 120 := hcardX₀ ▸ Subgroup.card_dvd_of_le inf_le_right
  have h2 : 24 ∣ Nat.card H' := hcardM ▸ Subgroup.card_dvd_of_le hMH'
  obtain ⟨k, hk⟩ := h2
  have hk5 : k ∣ 5 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 24)
    (by rw [← hk]; exact h1.trans (by norm_num))
  rcases (Nat.dvd_prime Nat.prime_five).mp hk5 with rfl | rfl
  · have : M = H' := Subgroup.eq_of_le_of_card_ge hMH' (by rw [hk, hcardM])
    exact hx₀M (this ▸ ⟨hx₀H, hx₀X₀⟩)
  · have : H' = X₀ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk, hcardX₀])
    exact hX₀H (this ▸ inf_le_left)

end IsSymDirect

end CFSG.CGT.Foote81L6.Normalizer
