module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityFrame

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryFrame

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

include h

theorem card_eq_four (hq : ℓ ^ f = 2) : Nat.card K = 4 := by
  rw [h.card, pow_mul', hq]; norm_num

theorem charP_two (hq : ℓ ^ f = 2) : CharP K 2 := by
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  subst hℓ
  exact h.charP

theorem pow_three_eq_one (hq : ℓ ^ f = 2) {a : K} (ha : a ≠ 0) : a ^ 3 = 1 := by
  have := h.finite
  have := Fintype.ofFinite K
  have h4 : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact card_eq_four h hq
  have : a ^ 4 = a := by simpa [h4] using FiniteField.pow_card a
  have : a * (a ^ 3 - 1) = 0 := by linear_combination this
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 ha
  · exact sub_eq_zero.1 h1

theorem bar_eq_sq (hq : ℓ ^ f = 2) (a : K) : h.bar a = a ^ 2 := by
  rw [UnitaryFieldData.bar_apply, hq]

theorem norm_eq_cube (hq : ℓ ^ f = 2) (a : K) : h.norm a = a ^ 3 := by
  rw [UnitaryFieldData.norm, bar_eq_sq h hq]; ring

theorem norm_eq_zero_or_one (hq : ℓ ^ f = 2) (a : K) :
    (a = 0 ∧ h.norm a = 0) ∨ (a ≠ 0 ∧ h.norm a = 1) := by
  by_cases ha : a = 0
  · left; exact ⟨ha, by rw [norm_eq_cube h hq, ha]; norm_num⟩
  · right; exact ⟨ha, by rw [norm_eq_cube h hq]; exact pow_three_eq_one h hq ha⟩


theorem idForm_sum_basis {b : Fin n → Fin n → K} (hb : IsOrthonormalFamily h b) (α β : Fin n → K) :
    idForm h n (∑ k, α k • b k) (∑ k, β k • b k) = ∑ k, h.bar (α k) * β k := by
  classical
  rw [map_sum (idForm h n), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, map_sum]
  have hk := hb k
  simp only [map_smul, hk, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem mono_of_commute {G : Type*} (hq : ℓ ^ f = 2)
    {b : Module.Basis (Fin n) K (Fin n → K)} (hb : IsOrthonormalFamily h b)
    (X : G → Matrix (Fin n) (Fin n) K) (χ : G → Fin n → K)
    (hX : ∀ g k, X g *ᵥ b k = χ g k • b k)
    (hcls : ∀ i j l : Fin n, i ≠ j → i ≠ l → j ≠ l → ¬ ∀ g, χ g i = χ g j ∧ χ g i = χ g l)
    (S : Matrix (Fin n) (Fin n) K)
    (hSiso : ∀ v w, idForm h n (S *ᵥ v) (S *ᵥ w) = idForm h n v w)
    (hSX : ∀ g, X g * S = S * X g) (l : Fin n) :
    ∃ m : Fin n, ∃ a : K, a ≠ 0 ∧ S *ᵥ b l = a • b m := by
  classical
  have := charP_two h hq
  set v : Fin n → K := S *ᵥ b l with hv
  set α : Fin n → K := fun k => b.repr v k with hα
  have hvα : v = ∑ k, α k • b k := (b.sum_repr v).symm
  have hsupp : ∀ k, α k ≠ 0 → ∀ g, χ g k = χ g l := by
    intro k hk g
    have e1 : X g *ᵥ v = χ g l • v := by
      rw [hv, Matrix.mulVec_mulVec, hSX g, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_smul]
    have e2 : X g *ᵥ v = ∑ k, (α k * χ g k) • b k := by
      conv_lhs => rw [hvα]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hX, smul_smul]
    have e3 : χ g l • v = ∑ k, (χ g l * α k) • b k := by
      conv_lhs => rw [hvα]
      simp only [Finset.smul_sum, smul_smul]
    have e4 := congrArg (fun w => b.repr w k) (e2.symm.trans (e1.trans e3))
    simp only [Module.Basis.repr_sum_self] at e4
    have e5 : α k * (χ g k - χ g l) = 0 := by linear_combination e4
    rcases mul_eq_zero.1 e5 with h1 | h1
    · exact absurd h1 hk
    · exact sub_eq_zero.1 h1
  have hnorm : ∑ k, h.bar (α k) * α k = 1 := by
    have h1 := hSiso (b l) (b l)
    rw [← hv, hb l l, ite_eq_left rfl] at h1
    rw [← h1]
    conv_rhs => rw [hvα]
    exact (idForm_sum_basis h hb α α).symm
  set s : Finset (Fin n) := Finset.univ.filter fun k => α k ≠ 0 with hs
  have hsum : ∑ k, h.bar (α k) * α k = (s.card : K) := by
    rw [← Finset.sum_filter_of_ne (p := fun k => α k ≠ 0) (fun k _ hk => by
      intro h0; exact hk (by rw [h0, mul_zero]))]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : α k ≠ 0 := (Finset.mem_filter.1 hk).2
    have := norm_eq_zero_or_one h hq (α k)
    rcases this with ⟨h0, -⟩ | ⟨-, h1⟩
    · exact absurd h0 hk'
    · rw [Nat.cast_one, mul_comm]; exact h1
  have hcard1 : (s.card : K) = 1 := by rw [← hsum, hnorm]
  have hcard2 : s.card ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.1 hlt
    refine hcls i j k hij hik hjk fun g => ?_
    have hi' := hsupp i (Finset.mem_filter.1 hi).2 g
    have hj' := hsupp j (Finset.mem_filter.1 hj).2 g
    have hk' := hsupp k (Finset.mem_filter.1 hk).2 g
    exact ⟨hi'.trans hj'.symm, hi'.trans hk'.symm⟩
  have hodd : s.card = 1 := by
    have h1 : s.card ≠ 0 := fun h0 => by
      rw [h0] at hcard1
      simp at hcard1
    have h2 : s.card ≠ 2 := fun h2 => by
      rw [h2] at hcard1
      have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
      rw [this] at hcard1
      exact zero_ne_one hcard1
    omega
  obtain ⟨m, hm⟩ := Finset.card_eq_one.1 hodd
  have hm' : α m ≠ 0 := by
    have : m ∈ s := by rw [hm]; exact Finset.mem_singleton_self m
    exact (Finset.mem_filter.1 this).2
  refine ⟨m, α m, hm', ?_⟩
  conv_lhs => rw [hvα]
  refine Finset.sum_eq_single_of_mem m (Finset.mem_univ m) fun k _ hkm => ?_
  have : α k = 0 := by
    by_contra hk
    have : k ∈ s := by simp [hs, hk]
    rw [hm] at this
    exact hkm (Finset.mem_singleton.1 this)
  rw [this, zero_smul]

theorem exists_cube_root (hq : ℓ ^ f = 2) : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  have hK : Fintype.card K = 3 + 1 := by
    rw [← Nat.card_eq_fintype_card, card_eq_four h hq]
  have hu : Nat.card Kˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hK]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hu])
  refine ⟨ω, by rw [← hω]; exact pow_orderOf_eq_one ω, fun h1 => ?_⟩
  rw [h1, orderOf_one] at hω
  omega

theorem torusMat_mulVec_basis {b : Fin n → Fin n → K} (hb : IsOrthonormalFamily h b)
    {i j : Fin n} (hij : i ≠ j) (c : K) (k : Fin n) :
    torusMat h (b i) (b j) c *ᵥ b k = (if k = i then c else if k = j then c⁻¹ else 1) • b k := by
  rw [torusMat_mulVec, hb i k, hb j k]
  by_cases hki : k = i
  · subst hki
    simp [hij.symm]
    module
  · by_cases hkj : k = j
    · subst hkj
      simp [hij, hki]
      module
    · simp [Ne.symm hki, Ne.symm hkj, hki, hkj]

theorem diag_of_coprime_commutators {G : Type*} (hq : ℓ ^ f = 2) (hn : 2 ≤ n)
    {b : Module.Basis (Fin n) K (Fin n → K)} (hb : IsOrthonormalFamily h b)
    (X : G → Matrix (Fin n) (Fin n) K) (χ : G → Fin n → K)
    (hX : ∀ g k, X g *ᵥ b k = χ g k • b k)
    (hcls : ∀ i j l : Fin n, i ≠ j → i ≠ l → j ≠ l → ¬ ∀ g, χ g i = χ g j ∧ χ g i = χ g l)
    (S : GL (Fin n) K)
    (hSiso : ∀ v w, idForm h n (((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      (((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = idForm h n v w)
    (hSX : ∀ g, X g * ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * X g)
    (ω : Kˣ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hcop : ∀ (i j : Fin n) (hij : i ≠ j),
      Nat.Coprime 3 (orderOf (S * torusGL h (hb.pair hij) ω * S⁻¹ *
        (torusGL h (hb.pair hij) ω)⁻¹)))
    (l : Fin n) :
    ∃ a : K, ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b l = a • b l := by
  classical
  have := h.finite
  have hmono := fun l => mono_of_commute h hq hb X χ hX hcls
    ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) hSiso hSX l
  choose π a ha hπ using hmono
  have hSinj : Function.Injective
      (fun v => ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) :=
    Matrix.mulVec_injective_iff_isUnit.mpr S.isUnit
  have hπinj : Function.Injective π := by
    intro l l' hll'
    by_contra hne
    have hpair := (hb.pair hne).linearIndependent
    rw [LinearIndependent.pair_iff] at hpair
    have h1 : ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (a l' • b l + (-a l) • b l') =
        ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ 0 := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hπ l, hπ l',
        Matrix.mulVec_zero,
        smul_smul, smul_smul, ← hll']
      rw [← add_smul]
      have : a l' * a l + -a l * a l' = 0 := by ring
      rw [this, zero_smul]
    have h2 := hSinj h1
    have := (hpair (a l') (-a l) (by simpa using h2)).1
    exact ha l' this
  have hπsurj : Function.Surjective π := Finite.injective_iff_surjective.1 hπinj
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  have hfix : ∀ i, π i = i := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne i
    have hij : i ≠ j := hji.symm
    set T : GL (Fin n) K := torusGL h (hb.pair hij) ω with hT
    set τ : Fin n → K := fun k => if k = i then (ω : K) else if k = j then (ω : K)⁻¹ else 1
      with hτ
    have hτ0 : ∀ k, τ k ≠ 0 := fun k => by
      simp only [hτ]
      split_ifs <;> simp
    have hτ3 : ∀ k, τ k ^ 3 = 1 := fun k => by
      have h1 : (ω : K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
      simp only [hτ]
      split_ifs
      · exact h1
      · rw [inv_pow, h1, inv_one]
      · exact one_pow _
    have hTb : ∀ k, ((T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b k = τ k • b k :=
      fun k => torusMat_mulVec_basis h hb hij (ω : K) k
    set W : GL (Fin n) K := S * T * S⁻¹ * T⁻¹ with hW
    have hWT : W * T * S = S * T := by rw [hW]; group
    have hWb : ∀ l, ((W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b (π l) =
        (τ l * (τ (π l))⁻¹) • b (π l) := by
      intro l
      have h1 := congrArg (fun g : GL (Fin n) K =>
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b l) hWT
      simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h1
      rw [hπ l, Matrix.mulVec_smul, hTb (π l), Matrix.mulVec_smul, Matrix.mulVec_smul,
        hTb l, Matrix.mulVec_smul, hπ l, smul_smul] at h1
      have h2 : (a l * τ (π l)) • ((W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b (π l) =
          (a l * τ (π l)) • ((τ l * (τ (π l))⁻¹) • b (π l)) := by
        rw [smul_smul]
        have : a l * τ (π l) * (τ l * (τ (π l))⁻¹) = τ l * a l := by
          field_simp [hτ0 (π l), ha l]
        rw [this, h1, smul_smul]
      exact smul_right_injective _ (mul_ne_zero (ha l) (hτ0 _)) h2
    have hW3 : W ^ 3 = 1 := by
      apply Units.ext
      apply Matrix.toLin'.injective
      apply b.ext
      intro k
      obtain ⟨l, rfl⟩ := hπsurj k
      have hr : (τ l * (τ (π l))⁻¹) ^ 3 = 1 := by
        rw [mul_pow, inv_pow, hτ3, hτ3, inv_one, mul_one]
      have key : ∀ (r : K) (v : Fin n → K),
          ((W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = r • v →
          ((W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            (((W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
              (((W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) = r ^ 3 • v := by
        intro r v hv
        simp only [hv, Matrix.mulVec_smul, smul_smul]
        congr 1
        ring
      have e2 := key _ _ (hWb l)
      rw [Units.val_pow_eq_pow_val, pow_three', Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [e2, hr, one_smul]
      simp
    have hW1 : W = 1 := by
      have h1 : orderOf W ∣ 3 := orderOf_dvd_of_pow_eq_one hW3
      have h2 : Nat.Coprime 3 (orderOf W) := hcop i j hij
      have := Nat.Coprime.eq_one_of_dvd h2.symm h1
      exact orderOf_eq_one_iff.1 this
    have h3 := hWb i
    rw [hW1] at h3
    have hb0 : b (π i) ≠ 0 := b.ne_zero _
    have h4 : (τ i * (τ (π i))⁻¹) = 1 := by
      have : (τ i * (τ (π i))⁻¹) • b (π i) = (1 : K) • b (π i) := by
        rw [← h3, one_smul]
        simp
      exact smul_left_injective K hb0 this
    have h5 : τ (π i) = τ i := by
      field_simp [hτ0 (π i)] at h4
      exact h4.symm
    have hτi : τ i = (ω : K) := by simp [hτ]
    by_contra hne
    by_cases hj : π i = j
    · rw [hj, hτi] at h5
      have h6 : τ j = (ω : K)⁻¹ := by simp [hτ, hji]
      rw [h6] at h5
      have h7 : (ω : K) * (ω : K) = 1 := by
        have : (ω : K) ≠ 0 := ω.ne_zero
        field_simp at h5
        linear_combination -h5
      have h8 : (ω : K) = 1 := by
        have h1 : (ω : K) ^ 3 = 1 := by
          rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
        linear_combination h1 - (ω : K) * h7
      exact hω1 (Units.ext h8)
    · have h6 : τ (π i) = 1 := by simp [hτ, hne, hj]
      rw [h6, hτi] at h5
      exact hω1 (Units.ext h5.symm)
  exact ⟨a l, by rw [hπ l, hfix l]⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
