module

public import CFSG.CharacterTheory.Semidihedral.Local.FourGroupOddCycling
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Wreathed

open CFSG.Semidihedral.Local

variable {M : Type*} [Group M]

theorem isKleinFour_closure_pair {x y : M} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : Commute x y) (hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y)) :
    IsKleinFour (Subgroup.closure {x, y}) := by
  have hcl : Subgroup.closure {x, y} = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hyx : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set M) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hxy.zpow_left k).eq
  have hcard : Nat.card (Subgroup.closure {x, y}) = 4 := by
    rw [hcl, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hyx hdisj,
      Nat.card_zpowers, Nat.card_zpowers, hx, hy]
  have hsq : ∀ v : Subgroup.closure {x, y}, v ^ 2 = 1 := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    have hv' : v ∈ ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup M) : Set M) := by
      rw [← hcl]
      exact hv
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hyx] at hv'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hv'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    change (x ^ i * y ^ j) ^ 2 = 1
    rw [((hxy.zpow_left i).zpow_right j).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
      ← zpow_mul, mul_comm i, mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hx2, hy2,
      one_zpow, one_zpow, one_mul]
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent (Subgroup.closure {x, y}) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    have hsub := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : Subgroup.closure {x, y})
    omega
  · exact h

variable [Finite M]

theorem exists_inverted_odd_cycling_of_surjective (V : Subgroup M) [V.Normal] [IsKleinFour V]
    (hsurj : Function.Surjective (MulAut.conjNormal : M →* MulAut V))
    (k : M) (hk : orderOf k = 2) (hkV : ∃ v ∈ V, k * v * k⁻¹ ≠ v) :
    ∃ b : ℕ, 1 ≤ b ∧ ∃ a : M, orderOf a = 3 ^ b ∧
      (∀ v ∈ V, v ≠ 1 → a * v * a⁻¹ ≠ v) ∧ (∀ v ∈ V, a ^ 3 * v * (a ^ 3)⁻¹ = v) ∧
      k * a * k⁻¹ = a⁻¹ ∧
      Subgroup.closure ((Subgroup.centralizer (V : Set M) : Set M) ∪ {k, a}) = ⊤ := by
  classical
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

end CFSG.Wreathed
