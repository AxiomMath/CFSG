module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGU

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial

section Leaves

variable {ℓ f : ℕ} {E : Type} [Field E] {hE : UnitaryFieldData ℓ f E}
  {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
  {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E}

private theorem hf_apply_apply_of_basis {ι : Type*} (b : Module.Basis ι E W) (D : W →ₗ[E] W)
    (hD : ∀ i j, Hf (D (b i)) (D (b j)) = Hf (b i) (b j)) (x y : W) :
    Hf (D x) (D y) = Hf x y := by
  have key : ((Hf.comp D : W →ₛₗ[hE.bar] W →ₗ[E] E).compl₂ D : W →ₛₗ[hE.bar] W →ₗ[E] E) = Hf :=
    LinearMap.ext_basis b b fun i j => hD i j
  exact DFunLike.congr_fun (DFunLike.congr_fun key x) y

private theorem exists_mem_sesqUnitaryGroup_of_isometry (hHfl : Hf.SeparatingLeft)
    (D : W →ₗ[E] W) (hD : ∀ x y, Hf (D x) (D y) = Hf x y) :
    ∃ g : ↥(sesqUnitaryGroup Hf), ((g : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) = D := by
  have hker : LinearMap.ker D = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    refine hHfl x fun y => ?_
    rw [← hD x y, hx, map_zero, LinearMap.zero_apply]
  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_ker_eq_bot D).2 hker
  exact ⟨⟨u, fun x y => by rw [hu]; exact hD x y⟩, hu⟩

private theorem exists_mem_sesqUnitaryGroup_perm {ι : Type*} [DecidableEq ι]
    (hHfl : Hf.SeparatingLeft) (b : Module.Basis ι E W)
    (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0) (τ : Equiv.Perm ι) :
    ∃ g : ↥(sesqUnitaryGroup Hf),
      ∀ i, ((g : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) (b i) = b (τ i) := by
  have hD : ∀ i j, Hf (b.constr E (fun i => b (τ i)) (b i)) (b.constr E (fun i => b (τ i)) (b j)) =
      Hf (b i) (b j) := by
    intro i j
    simp only [Module.Basis.constr_basis, hb, τ.apply_eq_iff_eq]
  obtain ⟨g, hg⟩ := exists_mem_sesqUnitaryGroup_of_isometry hHfl _
    (hf_apply_apply_of_basis b _ hD)
  exact ⟨g, fun i => by rw [hg, Module.Basis.constr_basis]⟩

private theorem exists_mem_sesqUnitaryGroup_dilation {ι : Type*} [DecidableEq ι]
    (hHfl : Hf.SeparatingLeft) (b : Module.Basis ι E W)
    (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0) (i₀ : ι) {ω : E}
    (hω : hE.bar ω * ω = 1) :
    ∃ g : ↥(sesqUnitaryGroup Hf), ∀ x,
      ((g : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) x =
        x + (b.coord i₀ x * (ω - 1)) • b i₀ := by
  let D : W →ₗ[E] W := LinearMap.id + (b.coord i₀).smulRight ((ω - 1) • b i₀)
  have hD1 : ∀ x, D x = x + (b.coord i₀ x * (ω - 1)) • b i₀ := fun x => by
    simp [D, mul_smul]
  have hDb : ∀ j, D (b j) = if j = i₀ then ω • b j else b j := by
    intro j
    rw [hD1]
    by_cases hj : j = i₀
    · subst hj
      simp [sub_smul]
    · simp [hj]
  have hiso : ∀ j k, Hf (D (b j)) (D (b k)) = Hf (b j) (b k) := by
    intro j k
    have hω' : ω * hE.bar ω = 1 := by rw [mul_comm]; exact hω
    rw [hDb, hDb]
    by_cases hj : j = i₀ <;> by_cases hk : k = i₀
    · simp [hj, hk, hb, hω, hω']
    · have hk' : i₀ ≠ k := Ne.symm hk
      simp [hj, hk, hk', hb]
    · have hj' : i₀ ≠ j := Ne.symm hj
      simp [hj, hk, hj', hb]
    · simp [hj, hk]
  obtain ⟨g, hg⟩ := exists_mem_sesqUnitaryGroup_of_isometry hHfl D
    (hf_apply_apply_of_basis b D hiso)
  exact ⟨g, fun x => by rw [hg, hD1]⟩

theorem eq_bot_of_normal_isPGroup_two_sesqUnitaryGroup_three_two (hℓ : ℓ = 2)
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) (hq : ℓ ^ f = 2)
    (hm : Module.finrank E W = 3) (K : Subgroup ↥(sesqUnitaryGroup Hf)) [K.Normal]
    (hK : IsPGroup 2 ↥K) : K = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEfin : Finite E := hE.finite
  have hEcard : Nat.card E = 4 := by
    rw [hE.card, pow_mul', hq]
    norm_num
  haveI : Finite W := Module.finite_of_finite E
  haveI : Finite ↥(sesqUnitaryGroup Hf) := finite_sesqUnitaryGroup'
  obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
  obtain ⟨ω, hω, hω1⟩ : ∃ ω : E, hE.bar ω * ω = 1 ∧ ω ≠ 1 := by
    haveI := Fintype.ofFinite E
    have hc : ({0, 1} : Finset E).card < (Finset.univ : Finset E).card := by
      have h1 : ({0, 1} : Finset E).card ≤ 2 := Finset.card_le_two
      have h2 : (Finset.univ : Finset E).card = 4 := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact hEcard
      omega
    obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
    refine ⟨ω, ?_, hω.2⟩
    have h3 : ω ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one ω hω.1
      rwa [← Nat.card_eq_fintype_card, hEcard] at this
    rw [hE.bar_apply, hq]
    calc ω ^ 2 * ω = ω ^ 3 := by ring
      _ = 1 := h3
  have hsmul : ∀ (g : ↥(sesqUnitaryGroup Hf)) (v : W),
      g • v = ((g : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) v := fun g v => rfl
  obtain ⟨v, hv0, hv⟩ : ∃ v : W, v ≠ 0 ∧ ∀ k : ↥K, k • v = v := by
    have hcard : 2 ∣ Nat.card W := by
      rw [Module.natCard_eq_pow_finrank (K := E), hEcard, hm]
      norm_num
    obtain ⟨v, hv, hne⟩ := hK.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hcard
      (a := 0) fun k => smul_zero _
    exact ⟨v, fun h => hne h.symm, fun k => hv k⟩
  have hKsmul : ∀ (k : ↥K) (x : W),
      k • x = (((k : ↥(sesqUnitaryGroup Hf)) : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) x :=
    fun k x => rfl
  have hfix_sub : ∀ x y : W, (∀ k : ↥K, k • x = x) → (∀ k : ↥K, k • y = y) →
      ∀ k : ↥K, k • (x - y) = x - y := by
    intro x y hx hy k
    have hx' := hx k
    have hy' := hy k
    rw [hKsmul] at hx' hy' ⊢
    rw [map_sub, hx', hy']
  have hfix_smul : ∀ (c : E) (x : W), (∀ k : ↥K, k • x = x) →
      ∀ k : ↥K, k • (c • x) = c • x := by
    intro c x hx k
    have hx' := hx k
    rw [hKsmul] at hx' ⊢
    rw [map_smul, hx']
  have hinv : ∀ (g : ↥(sesqUnitaryGroup Hf)) (x : W), (∀ k : ↥K, k • x = x) →
      ∀ k : ↥K, k • (g • x) = g • x := by
    intro g x hx k
    have hkn : g⁻¹ * (k : ↥(sesqUnitaryGroup Hf)) * g ∈ K := by
      have := Subgroup.Normal.conj_mem ‹K.Normal› (k : ↥(sesqUnitaryGroup Hf)) k.2 g⁻¹
      simpa using this
    have h1 : (g⁻¹ * (k : ↥(sesqUnitaryGroup Hf)) * g) • x = x := hx ⟨_, hkn⟩
    calc k • (g • x) = ((k : ↥(sesqUnitaryGroup Hf)) * g) • x :=
      (mul_smul (k : ↥(sesqUnitaryGroup Hf)) g x).symm
      _ = (g * (g⁻¹ * (k : ↥(sesqUnitaryGroup Hf)) * g)) • x := by group
      _ = g • ((g⁻¹ * (k : ↥(sesqUnitaryGroup Hf)) * g) • x) := mul_smul _ _ _
      _ = g • x := by rw [h1]
  obtain ⟨i, hi⟩ : ∃ i, b.coord i v ≠ 0 := by
    by_contra! h
    refine hv0 (b.repr.injective ?_)
    ext j
    simpa using h j
  obtain ⟨g, hg⟩ := exists_mem_sesqUnitaryGroup_dilation hHfl b hb i hω
  have hbi : ∀ k : ↥K, k • b i = b i := by
    have h1 := hfix_sub _ _ (hinv g v hv) hv
    have e : g • v - v = (b.coord i v * (ω - 1)) • b i := by
      rw [hsmul, hg, add_sub_cancel_left]
    rw [e] at h1
    have hc : b.coord i v * (ω - 1) ≠ 0 := mul_ne_zero hi (sub_ne_zero.2 hω1)
    have h2 := hfix_smul (b.coord i v * (ω - 1))⁻¹ _ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  have hbj : ∀ j, ∀ k : ↥K, k • b j = b j := by
    intro j
    obtain ⟨g, hg⟩ := exists_mem_sesqUnitaryGroup_perm hHfl b hb (Equiv.swap i j)
    have h1 := hinv g (b i) hbi
    have e : g • b i = b j := by rw [hsmul, hg, Equiv.swap_apply_left]
    rwa [e] at h1
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  have hlin : ((k : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) = LinearMap.id :=
    b.ext fun j => hbj j ⟨k, hk⟩
  exact Subtype.ext (Units.ext hlin)

end Leaves

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
