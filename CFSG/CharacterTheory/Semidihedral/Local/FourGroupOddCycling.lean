module

public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport

public section

namespace CFSG.Semidihedral.Local

theorem perm_three_commutator : ∀ τ σ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 →
    σ * σ * σ = 1 → σ ≠ 1 → σ * τ * σ⁻¹ * τ = σ * σ := by
  decide

theorem perm_three_fixed_free : ∀ σ : Equiv.Perm (Fin 3), σ * σ * σ = 1 → σ ≠ 1 →
    ∀ i, σ i ≠ i := by
  decide

theorem perm_three_generation : ∀ τ σ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 →
    σ * σ * σ = 1 → σ ≠ 1 → ∀ g : Equiv.Perm (Fin 3),
      g = 1 ∨ g = σ ∨ g = σ * σ ∨ g = τ ∨ g = τ * σ ∨ g = τ * (σ * σ) := by
  decide

theorem perm_three_exists_cycle : ∃ σ : Equiv.Perm (Fin 3), σ * σ * σ = 1 ∧ σ ≠ 1 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide⟩

theorem full_four_group_action_has_an_odd_cycling_element_inverted_by_each_outer_involution
    {M : Type*} [Group M] [Finite M] (V : Subgroup M) [V.Normal] [IsKleinFour V]
    (K : Subgroup M) [K.Normal] (hK : Odd (Nat.card K))
    (hCV : Subgroup.centralizer (V : Set M) = V ⊔ K)
    (hsurj : Function.Surjective (MulAut.conjNormal : M →* MulAut V))
    (k : M) (hk : orderOf k = 2) (hkV : ∃ v ∈ V, k * v * k⁻¹ ≠ v) :
    ∃ b : ℕ, 1 ≤ b ∧ ∃ a : M, orderOf a = 3 ^ b ∧
      (∀ v ∈ V, v ≠ 1 → a * v * a⁻¹ ≠ v) ∧ (∀ v ∈ V, a ^ 3 * v * (a ^ 3)⁻¹ = v) ∧
      k * a * k⁻¹ = a⁻¹ ∧
      Subgroup.closure ((Subgroup.centralizer (V : Set M) : Set M) ∪ {k, a}) = ⊤ := by
  classical
  have _hunused : Odd (Nat.card K) ∧ Subgroup.centralizer (V : Set M) = V ⊔ K := ⟨hK, hCV⟩
  let c : {x : V // x ≠ 1} ≃ Fin 3 := Finite.equivFinOfCardEq card_nontrivial
  let ψ : MulAut V ≃* Equiv.Perm (Fin 3) :=
    (MulEquiv.ofBijective _ nontrivialPerm_bijective).trans c.permCongrHom
  have hψ : ∀ (σ : MulAut V) (x : {x : V // x ≠ 1}), ψ σ (c x) = c (nontrivialPerm V σ x) := by
    intro σ x
    change c (nontrivialPerm V σ (c.symm (c x))) = _
    rw [Equiv.symm_apply_apply]
  let φ : M →* MulAut V := MulAut.conjNormal
  have hφ : ∀ (g : M) (v : V), ((φ g v : V) : M) = g * v * g⁻¹ := fun g v =>
    MulAut.conjNormal_apply g v
  have hker : ∀ g : M, φ g = 1 → g ∈ Subgroup.centralizer (V : Set M) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hφ g ⟨v, hv⟩
    rw [hg] at h1
    change v = g * v * g⁻¹ at h1
    calc v * g = g * v * g⁻¹ * g := by rw [← h1]
      _ = g * v := by group
  have hk2 : k * k = 1 := by
    rw [← sq, ← hk]
    exact pow_orderOf_eq_one k
  have hτ2 : ψ (φ k) * ψ (φ k) = 1 := by rw [← map_mul, ← map_mul, hk2, map_one, map_one]
  have hτ1 : ψ (φ k) ≠ 1 := by
    intro h
    have h1 : φ k = 1 := ψ.injective (h.trans (map_one ψ).symm)
    obtain ⟨v, hv, hkv⟩ := hkV
    apply hkv
    have h2 := hφ k ⟨v, hv⟩
    rw [h1] at h2
    exact h2.symm
  obtain ⟨ρ, hρ3, hρ1⟩ := perm_three_exists_cycle
  obtain ⟨y, hy⟩ := hsurj (ψ.symm ρ)
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  have hkw : k * (y * k * y⁻¹ * k) * k⁻¹ = (y * k * y⁻¹ * k)⁻¹ := by
    have h1 : (y * k * y⁻¹ * k)⁻¹ = k⁻¹ * y * k⁻¹ * y⁻¹ := by group
    rw [h1, hkinv]
    calc k * (y * k * y⁻¹ * k) * k = k * y * k * y⁻¹ * (k * k) := by group
      _ = k * y * k * y⁻¹ := by rw [hk2, mul_one]
  have hψw : ψ (φ (y * k * y⁻¹ * k)) = ρ * ρ := by
    have hyρ : ψ (φ y) = ρ := by
      change ψ (MulAut.conjNormal y) = ρ
      rw [hy, MulEquiv.apply_symm_apply]
    simp only [map_mul, map_inv, hyρ]
    exact perm_three_commutator _ ρ hτ2 hτ1 hρ3 hρ1
  set w := y * k * y⁻¹ * k with hw
  have hw0 : orderOf w ≠ 0 := (orderOf_pos w).ne'
  have hm0 : orderOf w / 3 ^ (orderOf w).factorization 3 ≠ 0 :=
    (Nat.ordCompl_pos 3 hw0).ne'
  have hmcop : Nat.Coprime 3 (orderOf w / 3 ^ (orderOf w).factorization 3) :=
    Nat.coprime_ordCompl Nat.prime_three hw0
  have hord : orderOf (w ^ (orderOf w / 3 ^ (orderOf w).factorization 3)) =
      3 ^ (orderOf w).factorization 3 := by
    rw [orderOf_pow_of_dvd hm0 (Nat.ordCompl_dvd _ _)]
    exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm0)
      (Nat.ordProj_mul_ordCompl_eq_self (orderOf w) 3).symm
  set m := orderOf w / 3 ^ (orderOf w).factorization 3 with hm
  have hσ : ψ (φ (w ^ m)) = (ρ * ρ) ^ m := by rw [map_pow, map_pow, hψw]
  have h3 : (ρ * ρ) ^ 3 = 1 := by
    calc (ρ * ρ) ^ 3 = (ρ * ρ * ρ) * (ρ * ρ * ρ) := by rw [pow_three]; simp only [mul_assoc]
      _ = 1 := by rw [hρ3, one_mul]
  have hρρ1 : ρ * ρ ≠ 1 := by
    intro h
    apply hρ1
    calc ρ = ρ * ρ * ρ * (ρ * ρ)⁻¹ := by group
      _ = 1 := by rw [hρ3, h, inv_one, one_mul]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hordρρ : orderOf (ρ * ρ) = 3 := orderOf_eq_prime h3 hρρ1
  have hσ1 : (ρ * ρ) ^ m ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hordρρ] at h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hmcop h1
  have hσ3 : (ρ * ρ) ^ m * (ρ * ρ) ^ m * (ρ * ρ) ^ m = 1 := by
    rw [← pow_add, ← pow_add, show m + m + m = 3 * m by ring, pow_mul, h3, one_pow]
  refine ⟨(orderOf w).factorization 3, ?_, w ^ m, hord, ?_, ?_, ?_, ?_⟩
  ·
    by_contra hb
    have hb0 : (orderOf w).factorization 3 = 0 := by omega
    rw [hb0, pow_zero, orderOf_eq_one_iff] at hord
    apply hσ1
    rw [← hσ, hord, map_one, map_one]
  ·
    intro v hv hv1 hfix
    have hv1' : (⟨v, hv⟩ : V) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
    have h1 : φ (w ^ m) ⟨v, hv⟩ = ⟨v, hv⟩ := Subtype.ext (by rw [hφ]; exact hfix)
    have h2 := hψ (φ (w ^ m)) ⟨⟨v, hv⟩, hv1'⟩
    have h4 : nontrivialPerm V (φ (w ^ m)) ⟨⟨v, hv⟩, hv1'⟩ = ⟨⟨v, hv⟩, hv1'⟩ :=
      Subtype.ext (by rw [nontrivialPerm_apply, h1])
    rw [h4, hσ] at h2
    exact perm_three_fixed_free _ hσ3 hσ1 _ h2
  ·
    intro v hv
    have h1 : φ ((w ^ m) ^ 3) = 1 := by
      apply ψ.injective
      rw [map_pow, map_pow, hσ, map_one, pow_three, ← mul_assoc]
      exact hσ3
    have h2 := hφ ((w ^ m) ^ 3) ⟨v, hv⟩
    rw [h1] at h2
    exact h2.symm
  ·
    rw [← conj_pow, hkw, inv_pow]
  ·
    rw [eq_top_iff]
    intro g _
    have key : ∀ h : M, h ∈ Subgroup.closure ((Subgroup.centralizer (V : Set M) : Set M) ∪
        {k, w ^ m}) → ψ (φ g) = ψ (φ h) →
        g ∈ Subgroup.closure ((Subgroup.centralizer (V : Set M) : Set M) ∪ {k, w ^ m}) := by
      intro h hh heq
      have h1 : φ (g * h⁻¹) = 1 := by rw [map_mul, map_inv, ψ.injective heq, mul_inv_cancel]
      have h2 : g = (g * h⁻¹) * h := by group
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl (hker _ h1))) hh
    have hkmem : k ∈ Subgroup.closure ((Subgroup.centralizer (V : Set M) : Set M) ∪
        {k, w ^ m}) := Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have hamem : w ^ m ∈ Subgroup.closure ((Subgroup.centralizer (V : Set M) : Set M) ∪
        {k, w ^ m}) := Subgroup.subset_closure (Or.inr (Or.inr rfl))
    have hσ3' : ψ (φ (w ^ m)) * ψ (φ (w ^ m)) * ψ (φ (w ^ m)) = 1 := by rw [hσ]; exact hσ3
    have hσ1' : ψ (φ (w ^ m)) ≠ 1 := by rw [hσ]; exact hσ1
    rcases perm_three_generation _ _ hτ2 hτ1 hσ3' hσ1' (ψ (φ g)) with h | h | h | h | h | h
    · exact key 1 (Subgroup.one_mem _) (by rw [h, map_one, map_one])
    · exact key _ hamem h
    · exact key _ (Subgroup.mul_mem _ hamem hamem) (by rw [h, map_mul, map_mul])
    · exact key _ hkmem h
    · exact key _ (Subgroup.mul_mem _ hkmem hamem) (by rw [h, map_mul, map_mul])
    · exact key _ (Subgroup.mul_mem _ hkmem (Subgroup.mul_mem _ hamem hamem))
        (by rw [h, map_mul, map_mul, map_mul, map_mul])

end CFSG.Semidihedral.Local
