module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

theorem isPGroup_zpowers_of_pow_three {C : Type*} [Group C] {p : C} (h : p ^ 3 = 1) :
    IsPGroup 3 ↥(Subgroup.zpowers p) := by
  rintro ⟨_, m, rfl⟩
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem card_le_of_sylow_conj {C : Type*} [Group C] [Finite C] {p₁ p₂ : C} (h1 : p₁ ^ 3 = 1)
    (h2 : p₂ ^ 3 = 1) (hc : p₁ * p₂ = p₂ * p₁) (P : Sylow 3 C) (A : Subgroup C)
    (hA2 : ∀ e ∈ A, e * e = 1) (hAc : ∀ e ∈ A, ∀ f ∈ A, e * f = f * e)
    (hAP : ∀ t ∈ P, ∀ x ∈ A, t * x * t⁻¹ ∈ A) {n : ℕ}
    (hY : {u : C | u * u = 1 ∧ u ≠ 1 ∧ ∀ i < 3, ∀ j < 3,
        u * (p₁ ^ i * p₂ ^ j * u * (p₁ ^ i * p₂ ^ j)⁻¹) =
          (p₁ ^ i * p₂ ^ j * u * (p₁ ^ i * p₂ ^ j)⁻¹) * u}.ncard ≤ n) :
    Nat.card ↥A ≤ n + 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 := isPGroup_zpowers_of_pow_three h1
  have hz2 := isPGroup_zpowers_of_pow_three h2
  have hnorm : Subgroup.zpowers p₁ ≤ Subgroup.normalizer (Subgroup.zpowers p₂ : Set C) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hcomm : Commute p₁ p₂ := hc
    exact (hcomm.symm.zpow_left m).eq
  have hM := hz1.to_sup_of_normal_right' hz2 hnorm
  obtain ⟨Q, hQ⟩ := hM.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q P
  have hgmem : ∀ x : C, x ∈ (P : Subgroup C) ↔ g⁻¹ * x * g ∈ (Q : Subgroup C) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply]
  have hq : ∀ i j : ℕ, p₁ ^ i * p₂ ^ j ∈ (Q : Subgroup C) := by
    intro i j
    refine Subgroup.mul_mem _ (hQ ?_) (hQ ?_)
    · exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    · exact Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  have hθ : ∀ a ∈ A, g⁻¹ * a * g ∈ insert (1 : C) {u : C | u * u = 1 ∧ u ≠ 1 ∧
      ∀ i < 3, ∀ j < 3, u * (p₁ ^ i * p₂ ^ j * u * (p₁ ^ i * p₂ ^ j)⁻¹) =
        (p₁ ^ i * p₂ ^ j * u * (p₁ ^ i * p₂ ^ j)⁻¹) * u} := by
    intro a ha
    by_cases hu : g⁻¹ * a * g = 1
    · rw [hu]
      exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ⟨?_, hu, ?_⟩
      · calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
          _ = 1 := by rw [hA2 a ha]; group
      · intro i _ j _
        set q := p₁ ^ i * p₂ ^ j with hqdef
        have ht : g * q * g⁻¹ ∈ (P : Subgroup C) := by
          rw [hgmem]
          have : g⁻¹ * (g * q * g⁻¹) * g = q := by group
          rw [this]
          exact hq i j
        have h3 := hAP _ ht a ha
        have h4 := hAc a ha _ h3
        calc g⁻¹ * a * g * (q * (g⁻¹ * a * g) * q⁻¹)
            = g⁻¹ * (a * (g * q * g⁻¹ * a * (g * q * g⁻¹)⁻¹)) * g := by group
          _ = g⁻¹ * ((g * q * g⁻¹ * a * (g * q * g⁻¹)⁻¹) * a) * g := by rw [h4]
          _ = (q * (g⁻¹ * a * g) * q⁻¹) * (g⁻¹ * a * g) := by group
  have hle : Nat.card ↥A ≤ Nat.card ↥(insert (1 : C) {u : C | u * u = 1 ∧ u ≠ 1 ∧
      ∀ i < 3, ∀ j < 3, u * (p₁ ^ i * p₂ ^ j * u * (p₁ ^ i * p₂ ^ j)⁻¹) =
        (p₁ ^ i * p₂ ^ j * u * (p₁ ^ i * p₂ ^ j)⁻¹) * u}) := by
    refine Nat.card_le_card_of_injective (fun a => ⟨g⁻¹ * (a : C) * g, hθ a a.2⟩) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  rw [Nat.card_coe_set_eq] at hle
  exact hle.trans ((Set.ncard_insert_le _ _).trans (by omega))

theorem card_le_of_mulEquiv_of_sylow {G G' : Type*} [Group G] [Finite G] [Group G']
    (ε : G ≃* G') {n : ℕ}
    (h' : ∀ (P : Sylow 3 G') (A : Subgroup G'), (∀ e ∈ A, e * e = 1) →
      (∀ e ∈ A, ∀ f ∈ A, e * f = f * e) → (∀ t ∈ P, ∀ x ∈ A, t * x * t⁻¹ ∈ A) →
      Nat.card ↥A ≤ n)
    (P : Sylow 3 G) (A : Subgroup G) (hA2 : ∀ e ∈ A, e * e = 1)
    (hAc : ∀ e ∈ A, ∀ f ∈ A, e * f = f * e) (hAP : ∀ t ∈ P, ∀ x ∈ A, t * x * t⁻¹ ∈ A) :
    Nat.card ↥A ≤ n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective ε.toMonoidHom := ε.surjective
  set P' : Sylow 3 G' := Sylow.mapSurjective (f := ε.toMonoidHom) hsurj P with hP'
  have hmem : ∀ t' ∈ P', ∃ t ∈ P, ε t = t' := by
    intro t' ht'
    have ht'' : t' ∈ (P : Subgroup G).map ε.toMonoidHom := ht'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ht''
    exact ⟨t, ht, rfl⟩
  have key := h' P' (A.map ε.toMonoidHom) (by
      rintro _ ⟨e, he, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, hA2 e he, map_one]) (by
      rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hAc e he f hf]) (by
      intro t' ht' x' hx'
      obtain ⟨t, ht, rfl⟩ := hmem t' ht'
      obtain ⟨x, hx, rfl⟩ := hx'
      refine ⟨t * x * t⁻¹, hAP t ht x hx, ?_⟩
      simp [map_mul, map_inv])
  rwa [Subgroup.card_map_of_injective ε.injective] at key

end CFSG.GroupTheory
