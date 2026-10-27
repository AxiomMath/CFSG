module

public import CFSG.GroupTheory.WeirSylow.OrthogonalTori

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.GroupTheory.WeirSylow Module QuadraticMap

private theorem orthBlock_exists_hom {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H)
    {n : ℕ} [NeZero n] (hn : orderOf g = n) :
    ∃ ρ : Multiplicative (ZMod n) →* H, Function.Injective ρ ∧
      ∀ c, ((ρ c : H) : G) ∈ Subgroup.zpowers g := by
  have hcard : Nat.card (Multiplicative (ZMod n)) = Nat.card (Subgroup.zpowers g) := by
    rw [Nat.card_zpowers, hn, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let e := mulEquivOfCyclicCardEq hcard
  exact ⟨(Subgroup.inclusion (Subgroup.zpowers_le.2 hg)).comp e.toMonoidHom,
    (Subgroup.inclusion_injective (Subgroup.zpowers_le.2 hg)).comp e.injective,
    fun c => (e c).2⟩

private theorem orthBlock_conj_zpow_of_mem {G : Type*} [Group G] {φ g : G} {μ : ℤ}
    (hφ : φ * g * φ⁻¹ = g ^ μ) {x : G} (hx : x ∈ Subgroup.zpowers g) :
    φ * x * φ⁻¹ = x ^ μ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← conj_zpow, hφ, ← zpow_mul, ← zpow_mul, mul_comm μ k]

private theorem orthBlock_trace_eq_zero_of_neg {K : Type} [Field K] [Fintype K] {L : Type}
    [Field L] [Algebra K L] [Finite L] {f : ℕ} (hfL : finrank K L = 2 * f) (σ : L ≃ₐ[K] L)
    (hσdef : σ = FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ f) {z : L} (hz : σ z = -z) :
    Algebra.trace K L z = 0 := by
  haveI : Module.Finite K L := Module.Finite.of_finite
  let φL : L ≃ₐ[K] L := FiniteField.frobeniusAlgEquivOfAlgebraic K L
  have hterm : ∀ i : ℕ, z ^ (Nat.card K ^ i) = (φL ^ i) z := fun i => by
    rw [Nat.card_eq_fintype_card, frob_pow_apply]
  have key : ∀ i : ℕ, (φL ^ (f + i)) z = -((φL ^ i) z) := fun i => by
    rw [add_comm f i, pow_add, AlgEquiv.mul_apply, ← hσdef, hz, map_neg]
  have h := FiniteField.algebraMap_trace_eq_sum_pow K L z
  rw [hfL, two_mul, Finset.sum_range_add] at h
  simp only [hterm, key, Finset.sum_neg_distrib, add_neg_cancel] at h
  exact (algebraMap K L).injective (by rw [h, map_zero])

theorem exists_orthBlock_split (K : Type) [Field K] [Fintype K] {L : Type} [Field L] [Algebra K L]
    [Finite L] {m : ℕ} [NeZero m] (hm : m ∣ Nat.card L - 1) :
    ∃ (S₀ : FormSpace K K) (ρ : Multiplicative (ZMod m) →* S₀.isom) (J₀ φ₀ : S₀.isom),
      IsPlusQuadSpace S₀ ∧ finrank K S₀.V = 2 * finrank K L ∧ Function.Injective ρ ∧
      (∀ c, J₀ * ρ c * J₀⁻¹ = ρ c⁻¹) ∧
      ∀ c, φ₀ * ρ c * φ₀⁻¹ = ρ (c ^ (Fintype.card K : ℤ)) := by
  haveI : Module.Finite K L := Module.Finite.of_finite
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq (L := L) (d := m) hm
  obtain ⟨lam, hlamdef⟩ : ∃ lam : L →ₗ[K] K, lam = Algebra.trace K L := ⟨_, rfl⟩
  have hlam : lam ≠ 0 := by rw [hlamdef]; exact Algebra.trace_ne_zero K L
  let S₀ : FormSpace K K := ⟨L × L, fun v _ => hypQuadForm lam v⟩
  have hS₀ : IsPlusQuadSpace S₀ := ⟨hypQuadForm lam, fun _ _ => rfl,
    nondegenerate_polarBilin_hypQuadForm hlam, isPlusType_hypQuadForm lam⟩
  have hmem : prodUnitsHom K L ζ ∈ S₀.isom := fun v _ => hypQuadForm_prodUnitsHom lam ζ v
  obtain ⟨ρ, hρ, hrange⟩ := orthBlock_exists_hom hmem (n := m)
    (by rw [orderOf_injective _ (prodUnitsHom_injective K L), hζ])
  let J : (L × L) ≃ₗ[K] (L × L) := LinearEquiv.prodComm K L L
  have hJmem : J ∈ S₀.isom := fun v w => by
    show hypQuadForm lam (v.2, v.1) = hypQuadForm lam v
    rw [hypQuadForm_apply, hypQuadForm_apply]
    show lam (v.2 * v.1) = lam (v.1 * v.2)
    rw [mul_comm]
  have hJg : J * prodUnitsHom K L ζ * J⁻¹ = (prodUnitsHom K L ζ)⁻¹ := by
    have hinv : (prodUnitsHom K L ζ)⁻¹ = prodUnitsHom K L ζ⁻¹ := (map_inv _ ζ).symm
    rw [hinv, mul_inv_eq_iff_eq_mul]
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    show ((prodUnitsHom K L ζ v).2, (prodUnitsHom K L ζ v).1) = prodUnitsHom K L ζ⁻¹ (v.2, v.1)
    rw [prodUnitsHom_apply, prodUnitsHom_apply, inv_inv]
  let φL : L ≃ₐ[K] L := FiniteField.frobeniusAlgEquivOfAlgebraic K L
  have hφpow : ∀ x : L, φL x = x ^ Fintype.card K := fun x => by
    have := frob_pow_apply (K := K) (L := L) 1 x
    rwa [pow_one, pow_one] at this
  let φG : (L × L) ≃ₗ[K] (L × L) := φL.toLinearEquiv.prodCongr φL.toLinearEquiv
  have hφmem : φG ∈ S₀.isom := fun v w => by
    show hypQuadForm lam (φL v.1, φL v.2) = hypQuadForm lam v
    rw [hypQuadForm_apply, hypQuadForm_apply]
    show lam (φL v.1 * φL v.2) = lam (v.1 * v.2)
    rw [← map_mul φL, hlamdef]
    exact Algebra.trace_eq_of_algEquiv φL (v.1 * v.2)
  have hφg : φG * prodUnitsHom K L ζ * φG⁻¹ = (prodUnitsHom K L ζ) ^ (Fintype.card K : ℤ) := by
    rw [← map_zpow, mul_inv_eq_iff_eq_mul]
    refine LinearEquiv.ext fun v => ?_
    have hz : (((ζ ^ (Fintype.card K : ℤ)) : Lˣ) : L) = (ζ : L) ^ Fintype.card K := by
      rw [Units.val_zpow_eq_zpow_val, zpow_natCast]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    refine Prod.ext ?_ ?_
    · show φL ((prodUnitsHom K L ζ v).1) =
        (prodUnitsHom K L (ζ ^ (Fintype.card K : ℤ)) (φL v.1, φL v.2)).1
      rw [prodUnitsHom_apply, prodUnitsHom_apply]
      show φL ((ζ : L) * v.1) = ((ζ ^ (Fintype.card K : ℤ) : Lˣ) : L) * φL v.1
      rw [map_mul, hφpow (ζ : L), hz]
    · show φL ((prodUnitsHom K L ζ v).2) =
        (prodUnitsHom K L (ζ ^ (Fintype.card K : ℤ)) (φL v.1, φL v.2)).2
      rw [prodUnitsHom_apply, prodUnitsHom_apply]
      show φL (((ζ⁻¹ : Lˣ) : L) * v.2) = (((ζ ^ (Fintype.card K : ℤ))⁻¹ : Lˣ) : L) * φL v.2
      rw [map_mul, hφpow ((ζ⁻¹ : Lˣ) : L), Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hz,
        inv_pow]
  refine ⟨S₀, ρ, ⟨J, hJmem⟩, ⟨φG, hφmem⟩, hS₀, ?_, hρ, fun c => Subtype.ext ?_,
    fun c => Subtype.ext ?_⟩
  · show finrank K (L × L) = 2 * finrank K L
    rw [Module.finrank_prod, two_mul]
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_inv]
    have := orthBlock_conj_zpow_of_mem (μ := -1) (by rwa [zpow_neg_one]) (hrange c)
    rwa [zpow_neg_one] at this
  · rw [map_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    exact orthBlock_conj_zpow_of_mem hφg (hrange c)

theorem exists_orthBlock_aniso (K : Type) [Field K] [Fintype K] {L : Type} [Field L] [Algebra K L]
    [Finite L] {f : ℕ} (hf : 0 < f) (hfL : finrank K L = 2 * f) {m : ℕ} [NeZero m]
    (hm : m ∣ Fintype.card K ^ f + 1) :
    ∃ (S₀ : FormSpace K K) (ρ : Multiplicative (ZMod m) →* S₀.isom) (J₀ φ₀ : S₀.isom),
      IsQuadSpace S₀ ∧ finrank K S₀.V = finrank K L ∧ Function.Injective ρ ∧
      (∀ c, J₀ * ρ c * J₀⁻¹ = ρ c⁻¹) ∧
      ∀ c, φ₀ * ρ c * φ₀⁻¹ = ρ (c ^ (Fintype.card K : ℤ)) := by
  haveI : Module.Finite K L := Module.Finite.of_finite
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  let φL : L ≃ₐ[K] L := FiniteField.frobeniusAlgEquivOfAlgebraic K L
  obtain ⟨σ, hσdef⟩ : ∃ σ : L ≃ₐ[K] L, σ = φL ^ f := ⟨_, rfl⟩
  have hφpow : ∀ x : L, φL x = x ^ Fintype.card K := fun x => by
    have := frob_pow_apply (K := K) (L := L) 1 x
    rwa [pow_one, pow_one] at this
  have hσpow : ∀ x : L, σ x = x ^ Fintype.card K ^ f := fun x => by
    rw [hσdef]
    exact frob_pow_apply f x
  have hσσ : ∀ x : L, σ (σ x) = x := fun x => by
    rw [hσdef]
    exact frob_pow_frob_pow hfL x
  have hφσ : ∀ x : L, φL (σ x) = σ (φL x) := fun x => by
    rw [hσdef]
    exact congrArg (fun e : L ≃ₐ[K] L => e x) (Commute.self_pow φL f).eq
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : L, z₀ + σ z₀ ≠ 0 := by
    by_contra! h
    obtain ⟨x, hx⟩ := exists_pow_ne_self (K := K) (L := L) hf (by rw [hfL]; omega)
    have h1 : σ 1 = -1 := eq_neg_of_add_eq_zero_right (h 1)
    rw [map_one] at h1
    have hx' : σ x = -x := eq_neg_of_add_eq_zero_right (h x)
    apply hx
    rw [← hσpow, hx']
    have h2 : (2 : L) = 0 := by linear_combination h1
    linear_combination (-x) * h2
  have hσt : σ (z₀ + σ z₀) = z₀ + σ z₀ := by rw [map_add, hσσ, add_comm]
  obtain ⟨θ, hθ⟩ : ∃ θ : L, θ + σ θ = 1 := by
    refine ⟨z₀ / (z₀ + σ z₀), ?_⟩
    rw [map_div₀, hσt, ← add_div, div_self hz₀]
  let lam : L →ₗ[K] K := (Algebra.trace K L).comp (LinearMap.mulLeft K θ)
  have hlam : ∀ x, lam x = Algebra.trace K L (θ * x) := fun x => rfl
  have hN : ∀ z, lam (z + σ z) = Algebra.trace K L z := by
    intro z
    have h1 : θ * σ z = σ (σ θ * z) := by rw [map_mul, hσσ]
    rw [hlam, mul_add, map_add, h1, Algebra.trace_eq_of_algEquiv σ, ← map_add, ← add_mul, hθ,
      one_mul]
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : L, Algebra.trace K L z₁ ≠ 0 := by
    by_contra! h
    exact Algebra.trace_ne_zero K L (LinearMap.ext h)
  have hnd : (polarBilin (twistQuadForm lam σ)).Nondegenerate :=
    nondegenerate_polarBilin_twistQuadForm hσσ (z₀ := z₁) (by rw [hN]; exact hz₁)
  let S₀ : FormSpace K K := ⟨L, fun x _ => twistQuadForm lam σ x⟩
  have hS₀ : IsQuadSpace S₀ := ⟨twistQuadForm lam σ, fun _ _ => rfl, hnd⟩
  have hfac : (Fintype.card K ^ f + 1) * (Fintype.card K ^ f - 1) =
      Fintype.card K ^ (2 * f) - 1 := by
    have h1 : 1 ≤ Fintype.card K ^ f := Nat.one_le_pow _ _ Fintype.card_pos
    have h2 : 1 ≤ Fintype.card K ^ (2 * f) := Nat.one_le_pow _ _ Fintype.card_pos
    zify [h1, h2]
    rw [pow_mul']
    ring
  have hdvd : Fintype.card K ^ f + 1 ∣ Nat.card L - 1 := by
    rw [CFSG.GroupTheory.WeirSylow.natCard_eq_pow_finrank (K := K), hfL]
    exact ⟨_, hfac.symm⟩
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq (L := L) (d := m) (hm.trans hdvd)
  have hζσ : (ζ : L) * σ (ζ : L) = 1 := by
    rw [hσpow, ← pow_succ']
    have h1 : ζ ^ (Fintype.card K ^ f + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hm)
    have h2 := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
  have hσζ : σ (ζ : L) = ((ζ⁻¹ : Lˣ) : L) := by
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right hζσ
  have hmem : DistribMulAction.toModuleAut K L ζ ∈ S₀.isom := fun x y =>
    twistQuadForm_toModuleAut lam σ hζσ x
  obtain ⟨ρ, hρ, hrange⟩ := orthBlock_exists_hom hmem (n := m)
    (by rw [orderOf_toModuleAut, hζ])
  have hJmem : σ.toLinearEquiv ∈ S₀.isom := fun x y => by
    show twistQuadForm lam σ (σ x) = twistQuadForm lam σ x
    rw [twistQuadForm_apply, twistQuadForm_apply, hσσ, mul_comm]
  have hJg : σ.toLinearEquiv * DistribMulAction.toModuleAut K L ζ * σ.toLinearEquiv⁻¹ =
      (DistribMulAction.toModuleAut K L ζ)⁻¹ := by
    have hinv : (DistribMulAction.toModuleAut K L ζ)⁻¹ = DistribMulAction.toModuleAut K L ζ⁻¹ :=
      (map_inv (DistribMulAction.toModuleAut K L : Lˣ →* (L ≃ₗ[K] L)) ζ).symm
    rw [hinv, mul_inv_eq_iff_eq_mul]
    refine LinearEquiv.ext fun x => ?_
    show σ ((ζ : L) * x) = ((ζ⁻¹ : Lˣ) : L) * σ x
    rw [map_mul, hσζ]
  have hφI : ∀ w : L, σ w = w → lam (φL w) = lam w := by
    intro w hw
    obtain ⟨η, hη⟩ : ∃ η : L, η = φL.symm θ - θ := ⟨_, rfl⟩
    have hσφ : ∀ y : L, σ (φL.symm y) = φL.symm (σ y) := fun y => by
      apply φL.injective
      rw [hφσ, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    have hση : σ η = -η := by
      have h1 : η + σ η = 0 := by
        rw [hη, map_sub, hσφ, sub_add_sub_comm, ← map_add, hθ, map_one, sub_self]
      exact eq_neg_of_add_eq_zero_right h1
    have hz : σ (η * w) = -(η * w) := by rw [map_mul, hση, hw, neg_mul]
    have htr : Algebra.trace K L (η * w) = 0 :=
      orthBlock_trace_eq_zero_of_neg hfL σ hσdef hz
    rw [hlam, hlam]
    have h1 : θ * φL w = φL (φL.symm θ * w) := by rw [map_mul, AlgEquiv.apply_symm_apply]
    rw [h1, Algebra.trace_eq_of_algEquiv φL, show φL.symm θ = θ + η by rw [hη]; ring, add_mul,
      map_add, htr, add_zero]
  have hφmem : φL.toLinearEquiv ∈ S₀.isom := fun x y => by
    show twistQuadForm lam σ (φL x) = twistQuadForm lam σ x
    rw [twistQuadForm_apply, twistQuadForm_apply, ← hφσ, ← map_mul φL]
    exact hφI _ (by rw [map_mul, hσσ, mul_comm])
  have hφg : φL.toLinearEquiv * DistribMulAction.toModuleAut K L ζ * φL.toLinearEquiv⁻¹ =
      (DistribMulAction.toModuleAut K L ζ) ^ (Fintype.card K : ℤ) := by
    rw [← map_zpow, mul_inv_eq_iff_eq_mul]
    refine LinearEquiv.ext fun x => ?_
    show φL ((ζ : L) * x) = (((ζ ^ (Fintype.card K : ℤ) : Lˣ)) : L) * φL x
    rw [map_mul, hφpow (ζ : L), Units.val_zpow_eq_zpow_val, zpow_natCast]
  refine ⟨S₀, ρ, ⟨σ.toLinearEquiv, hJmem⟩, ⟨φL.toLinearEquiv, hφmem⟩, hS₀, rfl, hρ,
    fun c => Subtype.ext ?_, fun c => Subtype.ext ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_inv]
    have := orthBlock_conj_zpow_of_mem (μ := -1) (by rwa [zpow_neg_one]) (hrange c)
    rwa [zpow_neg_one] at this
  · rw [map_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    exact orthBlock_conj_zpow_of_mem hφg (hrange c)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
