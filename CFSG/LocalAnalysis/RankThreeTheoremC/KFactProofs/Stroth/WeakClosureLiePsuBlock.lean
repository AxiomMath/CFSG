module

public import CFSG.GroupTheory.WeirSylow.Unitary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.GroupTheory.WeirSylow Module
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {p₀ f : ℕ} {L : Type} [Field L] [Fintype L] (h : UnitaryFieldData p₀ f L)

private theorem suBlock_exists_hom {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H)
    {n : ℕ} [NeZero n] (hn : orderOf g = n) :
    ∃ ρ : Multiplicative (ZMod n) →* H, Function.Injective ρ ∧
      ∀ c, ((ρ c : H) : G) ∈ Subgroup.zpowers g := by
  have hcard : Nat.card (Multiplicative (ZMod n)) = Nat.card (Subgroup.zpowers g) := by
    rw [Nat.card_zpowers, hn, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let e := mulEquivOfCyclicCardEq hcard
  exact ⟨(Subgroup.inclusion (Subgroup.zpowers_le.2 hg)).comp e.toMonoidHom,
    (Subgroup.inclusion_injective (Subgroup.zpowers_le.2 hg)).comp e.injective,
    fun c => (e c).2⟩

private theorem suBlock_conj_zpow_of_mem {G : Type*} [Group G] {φ g : G} {μ : ℤ}
    (hφ : φ * g * φ⁻¹ = g ^ μ) {x : G} (hx : x ∈ Subgroup.zpowers g) :
    φ * x * φ⁻¹ = x ^ μ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← conj_zpow, hφ, ← zpow_mul, ← zpow_mul, mul_comm μ k]

private theorem suBlock_sq_sub_one (a : ℕ) : a ^ 2 - 1 = (a + 1) * (a - 1) := by
  rcases a with _ | b
  · norm_num
  · rw [Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)

private theorem suBlock_q_pos {q : ℕ} (hq : Fintype.card L = q ^ 2) : 0 < q := by
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · have := Fintype.card_pos (α := L)
    rw [hq, h0] at this
    norm_num at this
  · exact h0

private theorem suBlock_det_frobenius (F : Type) [Field F] [Fintype F] (K : Type) [Field K]
    [Algebra F K] [Finite K] :
    LinearMap.det (FiniteField.frobeniusAlgHom F K).toLinearMap =
      (-1 : F) ^ (Module.finrank F K - 1) := by
  haveI : Module.Finite F K := Module.Finite.of_finite
  set φ := (FiniteField.frobeniusAlgHom F K).toLinearMap with hφ
  have hn : 0 < Module.finrank F K := Module.finrank_pos
  have hmin : minpoly F φ = Polynomial.X ^ Module.finrank F K - 1 :=
    FiniteField.minpoly_frobeniusAlgHom F K
  have hdeg : (Polynomial.X ^ Module.finrank F K - 1 : Polynomial F).natDegree =
      Module.finrank F K := by
    simpa using Polynomial.natDegree_X_pow_sub_C (n := Module.finrank F K) (r := (1 : F))
  have hchar : φ.charpoly = Polynomial.X ^ Module.finrank F K - 1 := by
    have h := Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (LinearMap.isIntegral φ)) (LinearMap.charpoly_monic φ)
      (LinearMap.minpoly_dvd_charpoly φ) (by rw [LinearMap.charpoly_natDegree, hmin, hdeg])
    rw [h, hmin]
  have hcoeff : (Polynomial.X ^ Module.finrank F K - 1 : Polynomial F).coeff 0 = -1 := by
    simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, hn.ne]
  rw [LinearMap.det_eq_sign_charpoly_coeff, hchar, hcoeff]
  obtain ⟨k, hk⟩ : ∃ k, Module.finrank F K = k + 1 := ⟨Module.finrank F K - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  simp

private theorem suBlock_det_frobeniusEquiv (F : Type) [Field F] [Fintype F] (K : Type) [Field K]
    [Algebra F K] [Finite K] :
    LinearMap.det ((FiniteField.frobeniusAlgEquivOfAlgebraic F K).toLinearEquiv :
        K →ₗ[F] K) = (-1 : F) ^ (Module.finrank F K - 1) := by
  have hlin : ((FiniteField.frobeniusAlgEquivOfAlgebraic F K).toLinearEquiv : K →ₗ[F] K) =
      (FiniteField.frobeniusAlgHom F K).toLinearMap :=
    LinearMap.ext fun x => congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic F K) x
  rw [hlin, suBlock_det_frobenius F K]

private theorem suBlock_twist_apply {N : Type} [Field N] [Algebra L N]
    (φ' : Nˣ →* Nˣ) (u : Nˣ) (v : N × N) :
    twistUnitsHom L N φ' u v = ((u : N) * v.1, (((φ' u)⁻¹ : Nˣ) : N) * v.2) :=
  rfl

theorem exists_suBlock_odd {q : ℕ} (hq : Fintype.card L = q ^ 2) (hqf : q = p₀ ^ f) {e : ℕ}
    (he : Odd e) {m : ℕ} [NeZero m] (hm : m ∣ q ^ e + 1) :
    ∃ (S₀ : FormSpace L L) (ρ : Multiplicative (ZMod m) →* S₀.isom) (φ z : S₀.isom),
      IsHermitianSpace h S₀ ∧ finrank L S₀.V = e ∧ Function.Injective ρ ∧
      (∀ c, φ * ρ c * φ⁻¹ = ρ (c ^ ((q : ℤ) ^ 2))) ∧
      LinearMap.det ((φ : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) = 1 ∧
      (∀ c, z * ρ c * z⁻¹ = ρ c) ∧
      LinearMap.det ((z : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) = (-1) ^ e := by
  have hLc : CharP L p₀ := h.charP
  have hp : Fact p₀.Prime := ⟨h.prime⟩
  have hqpos : 0 < q := suBlock_q_pos hq
  have hepos : 0 < e := by obtain ⟨j, hj⟩ := he; omega
  haveI : NeZero e := ⟨hepos.ne'⟩
  let M := FiniteField.Extension L p₀ e
  have hMcard : Nat.card M = (q ^ e) ^ 2 := by
    rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card, hq, ← pow_mul, ← pow_mul,
      mul_comm]
  have hMdim : finrank L M = e := FiniteField.finrank_extension L p₀ e
  have : CharP M p₀ := charP_of_injective_algebraMap (algebraMap L M).injective p₀
  let τ : M →+* M := iterateFrobenius M p₀ (f * e)
  have hτpow : ∀ x : M, τ x = x ^ q ^ e := fun x => by
    rw [iterateFrobenius_def, pow_mul, ← hqf]
  have hτ : ∀ c : L, τ (algebraMap L M c) = algebraMap L M (h.bar c) := fun c => by
    rw [hτpow, ← map_pow, pow_pow_odd_eq hq he, unitaryBar_eq_pow h hqf]
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    rw [hτpow, hτpow, ← pow_mul, ← sq, ← hMcard, pow_natCard_eq]
  have hdvdM : m ∣ Nat.card M - 1 := by
    rw [hMcard, suBlock_sq_sub_one]
    exact dvd_mul_of_dvd_left hm _
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq hdvdM
  have hζτ : τ ζ * ζ = 1 := by
    rw [hτpow, ← pow_succ]
    have h2 : ζ ^ (q ^ e + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hm)
    simpa using congrArg Units.val h2
  let S₀ : FormSpace L L := ⟨M, fun x y => traceHerm h hτ x y⟩
  have hS₀ : IsHermitianSpace h S₀ := ⟨traceHerm h hτ, fun _ _ => rfl,
    traceHerm_isSymm h hτ hττ, traceHerm_separatingLeft h hτ⟩
  have hgmem : DistribMulAction.toModuleAut L M ζ ∈ S₀.isom := fun x y =>
    traceHerm_toModuleAut h hτ hζτ x y
  obtain ⟨ρ, hρ, hrange⟩ := suBlock_exists_hom hgmem (n := m)
    (by rw [orderOf_toModuleAut, hζ])
  let φL : M ≃ₐ[L] M := FiniteField.frobeniusAlgEquivOfAlgebraic L M
  have hφpow : ∀ x : M, φL x = x ^ q ^ 2 := fun x => by
    rw [← hq]
    exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic L M) x
  have hφτ : ∀ x : M, τ (φL x) = φL (τ x) := fun x => by
    rw [hτpow, hτpow, hφpow, hφpow, ← pow_mul, ← pow_mul, mul_comm]
  have hφiso : ∀ x y : M, traceHerm h hτ (φL x) (φL y) = traceHerm h hτ x y := fun x y => by
    rw [traceHerm_apply, traceHerm_apply, hφτ, ← map_mul φL, Algebra.trace_eq_of_algEquiv φL]
  let φG : M ≃ₗ[L] M := φL.toLinearEquiv
  let φ : S₀.isom := ⟨φG, fun x y => hφiso x y⟩
  have hgpow : ∀ (k : ℤ) (y : M),
      (DistribMulAction.toModuleAut L M ζ ^ k) y = (ζ : M) ^ k * y := fun k y => by
    rw [← map_zpow, ← Units.val_zpow_eq_zpow_val]
    rfl
  have hφg : φG * DistribMulAction.toModuleAut L M ζ =
      DistribMulAction.toModuleAut L M ζ ^ ((q : ℤ) ^ 2) * φG := by
    refine LinearEquiv.ext fun y => ?_
    have hz : (ζ : M) ^ ((q : ℤ) ^ 2) = (ζ : M) ^ (q ^ 2) := by
      rw [← zpow_natCast]
      push_cast
      rfl
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgpow]
    show φL ((ζ : M) * y) = (ζ : M) ^ ((q : ℤ) ^ 2) * φL y
    rw [map_mul, hφpow (ζ : M), hz]
  have hφgconj : φG * DistribMulAction.toModuleAut L M ζ * φG⁻¹ =
      DistribMulAction.toModuleAut L M ζ ^ ((q : ℤ) ^ 2) := mul_inv_eq_iff_eq_mul.2 hφg
  have hconj : ∀ c, φ * ρ c * φ⁻¹ = ρ (c ^ ((q : ℤ) ^ 2)) := fun c => by
    refine Subtype.ext ?_
    rw [map_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    exact suBlock_conj_zpow_of_mem hφgconj (hrange c)
  have hdetφ : LinearMap.det ((φ : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) = 1 := by
    have hd : LinearMap.det ((φL.toLinearEquiv : M ≃ₗ[L] M) : M →ₗ[L] M) =
        (-1 : L) ^ (Module.finrank L M - 1) :=
      suBlock_det_frobeniusEquiv L M
    show LinearMap.det ((φL.toLinearEquiv : M ≃ₗ[L] M) : M →ₗ[L] M) = 1
    rw [hd, hMdim]
    obtain ⟨j, hj⟩ := he
    rw [hj, Nat.add_sub_cancel, pow_mul, neg_one_sq, one_pow]
  have hτneg : τ (-1) = -1 := by rw [map_neg, map_one]
  have hu : τ ((-1 : Mˣ) : M) * ((-1 : Mˣ) : M) = 1 := by
    rw [Units.val_neg, Units.val_one, hτneg, neg_mul_neg, one_mul]
  let z : S₀.isom := ⟨DistribMulAction.toModuleAut L M (-1 : Mˣ), fun x y =>
    traceHerm_toModuleAut h hτ hu x y⟩
  have hzg : DistribMulAction.toModuleAut L M (-1 : Mˣ) * DistribMulAction.toModuleAut L M ζ =
      DistribMulAction.toModuleAut L M ζ * DistribMulAction.toModuleAut L M (-1 : Mˣ) := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hzconj : DistribMulAction.toModuleAut L M (-1 : Mˣ) * DistribMulAction.toModuleAut L M ζ *
      (DistribMulAction.toModuleAut L M (-1 : Mˣ))⁻¹ =
        DistribMulAction.toModuleAut L M ζ ^ (1 : ℤ) := by
    rw [zpow_one]
    exact mul_inv_eq_iff_eq_mul.2 hzg
  have hzcomm : ∀ c, z * ρ c * z⁻¹ = ρ c := fun c => by
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have := suBlock_conj_zpow_of_mem hzconj (hrange c)
    rwa [zpow_one] at this
  have hdetz : LinearMap.det ((z : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) = (-1) ^ e := by
    have hlin : ((DistribMulAction.toModuleAut L M (-1 : Mˣ) : M ≃ₗ[L] M) : M →ₗ[L] M) =
        (-1 : L) • LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show ((-1 : Mˣ) : M) * x = (-1 : L) • x
      rw [neg_one_smul, Units.val_neg, Units.val_one, neg_mul, one_mul]
    show LinearMap.det ((DistribMulAction.toModuleAut L M (-1 : Mˣ) : M ≃ₗ[L] M) : M →ₗ[L] M) =
      (-1) ^ e
    rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one, hMdim]
  exact ⟨S₀, ρ, φ, z, hS₀, hMdim, hρ, hconj, hdetφ, hzcomm, hdetz⟩

theorem exists_suBlock_even {q : ℕ} (hq : Fintype.card L = q ^ 2) (hqf : q = p₀ ^ f) {k : ℕ}
    (hk : 0 < k) {m : ℕ} [NeZero m] (hm : m ∣ q ^ (2 * k) - 1) :
    ∃ (S₀ : FormSpace L L) (ρ : Multiplicative (ZMod m) →* S₀.isom) (φ : S₀.isom),
      IsHermitianSpace h S₀ ∧ finrank L S₀.V = 2 * k ∧ Function.Injective ρ ∧
      (∀ c, φ * ρ c * φ⁻¹ = ρ (c ^ ((q : ℤ) ^ 2))) ∧
      LinearMap.det ((φ : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) = 1 := by
  have hLc : CharP L p₀ := h.charP
  have hp : Fact p₀.Prime := ⟨h.prime⟩
  have hqpos : 0 < q := suBlock_q_pos hq
  haveI : NeZero k := ⟨hk.ne'⟩
  let N := FiniteField.Extension L p₀ k
  have hNcard : Nat.card N = q ^ (2 * k) := by
    rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card, hq, ← pow_mul]
  have hNdim : finrank L N = k := FiniteField.finrank_extension L p₀ k
  have : CharP N p₀ := charP_of_injective_algebraMap (algebraMap L N).injective p₀
  have hdvd : m ∣ Nat.card N - 1 := by rw [hNcard]; exact hm
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq hdvd
  let τ : N →+* N := iterateFrobenius N p₀ f
  have hτpow : ∀ x : N, τ x = x ^ q := fun x => by
    rw [iterateFrobenius_def, hqf]
  have hτ : ∀ c : L, τ (algebraMap L N c) = algebraMap L N (h.bar c) := fun c => by
    rw [iterateFrobenius_def, ← map_pow, h.bar_apply]
  have hτs : Function.Surjective τ := Finite.injective_iff_surjective.1 τ.injective
  let μ : N →ₗ[L] L := Algebra.trace L N
  have hμ : μ ≠ 0 := Algebra.trace_ne_zero L N
  let φN : N ≃ₐ[L] N := FiniteField.frobeniusAlgEquivOfAlgebraic L N
  have hφpow : ∀ x : N, φN x = x ^ q ^ 2 := fun x => by
    rw [← hq]
    exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic L N) x
  have hφτ : ∀ x : N, τ (φN x) = φN (τ x) := fun x => by
    rw [hτpow, hτpow, hφpow, hφpow, ← pow_mul, ← pow_mul, mul_comm]
  have hμφ : ∀ x : N, μ (φN x) = μ x := fun x => Algebra.trace_eq_of_algEquiv φN x
  let S₀ : FormSpace L L := ⟨N × N, fun v w => hypHerm h hτ μ v w⟩
  have hS₀ : IsHermitianSpace h S₀ := ⟨hypHerm h hτ μ, fun _ _ => rfl,
    hypHerm_isSymm h hτ μ, hypHerm_separatingLeft h hτ μ hμ hτs⟩
  have hgmem : twistUnitsHom L N (Units.map τ.toMonoidHom) ζ ∈ S₀.isom := fun v w =>
    hypHerm_twistUnitsHom h hτ μ ζ v w
  obtain ⟨ρ, hρ, hrange⟩ := suBlock_exists_hom hgmem (n := m)
    (by rw [orderOf_injective _ (twistUnitsHom_injective _) ζ, hζ])
  let φG : (N × N) ≃ₗ[L] (N × N) := φN.toLinearEquiv.prodCongr φN.toLinearEquiv
  have hφG : ∀ w : N × N, φG w = (φN w.1, φN w.2) := fun w => rfl
  have hφiso : ∀ v w : N × N, hypHerm h hτ μ (φG v) (φG w) = hypHerm h hτ μ v w := fun v w => by
    simp only [hypHerm_apply, hφG, hφτ, ← map_mul φN, hμφ]
  let φ : S₀.isom := ⟨φG, fun v w => hφiso v w⟩
  have hcoeμ : ∀ x : Nˣ, ((Units.map τ.toMonoidHom x : Nˣ) : N) = τ x := fun x => rfl
  have hcoeφ : ∀ x : Nˣ, ((Units.map φN.toMonoidHom x : Nˣ) : N) = φN x := fun x => rfl
  have hφtwist : ∀ u : Nˣ, φG * twistUnitsHom L N (Units.map τ.toMonoidHom) u =
      twistUnitsHom L N (Units.map τ.toMonoidHom) (Units.map φN.toMonoidHom u) * φG := by
    intro u
    have key : φN (((Units.map τ.toMonoidHom u)⁻¹ : Nˣ) : N) =
        (((Units.map τ.toMonoidHom (Units.map φN.toMonoidHom u))⁻¹ : Nˣ) : N) := by
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hcoeμ, hcoeμ, hcoeφ, hφτ,
        map_inv₀]
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.mul_apply, hφG, suBlock_twist_apply, map_mul, hcoeφ, key]
  have hψζ : Units.map φN.toMonoidHom ζ = ζ ^ ((q : ℤ) ^ 2) := by
    refine Units.ext ?_
    rw [hcoeφ, Units.val_zpow_eq_zpow_val, hφpow, ← zpow_natCast]
    push_cast
    rfl
  have hφg : φG * twistUnitsHom L N (Units.map τ.toMonoidHom) ζ =
      twistUnitsHom L N (Units.map τ.toMonoidHom) ζ ^ ((q : ℤ) ^ 2) * φG := by
    rw [hφtwist ζ, hψζ, map_zpow]
  have hφgconj : φG * twistUnitsHom L N (Units.map τ.toMonoidHom) ζ * φG⁻¹ =
      twistUnitsHom L N (Units.map τ.toMonoidHom) ζ ^ ((q : ℤ) ^ 2) := mul_inv_eq_iff_eq_mul.2 hφg
  have hconj : ∀ c, φ * ρ c * φ⁻¹ = ρ (c ^ ((q : ℤ) ^ 2)) := fun c => by
    refine Subtype.ext ?_
    rw [map_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    exact suBlock_conj_zpow_of_mem hφgconj (hrange c)
  have hdetφ : LinearMap.det ((φ : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) = 1 := by
    have hd : LinearMap.det ((φN.toLinearEquiv : N ≃ₗ[L] N) : N →ₗ[L] N) =
        (-1 : L) ^ (Module.finrank L N - 1) :=
      suBlock_det_frobeniusEquiv L N
    show LinearMap.det (((φN.toLinearEquiv.prodCongr φN.toLinearEquiv : (N × N) ≃ₗ[L] (N × N)) :
      (N × N) →ₗ[L] (N × N))) = 1
    rw [LinearEquiv.coe_prodCongr, LinearMap.det_prodMap, hd, hNdim, ← mul_pow]
    norm_num
  have hfin : finrank L S₀.V = 2 * k := by
    show finrank L (N × N) = 2 * k
    rw [Module.finrank_prod, hNdim, two_mul]
  exact ⟨S₀, ρ, φ, hS₀, hfin, hρ, hconj, hdetφ⟩

theorem exists_suBlock_two {q : ℕ} (hq : Fintype.card L = q ^ 2) (hqf : q = p₀ ^ f) {m : ℕ}
    [NeZero m] (hm : m ∣ q - 1) :
    ∃ (S₀ : FormSpace L L) (ρ : Multiplicative (ZMod m) →* S₀.isom) (J : S₀.isom),
      IsHermitianSpace h S₀ ∧ finrank L S₀.V = 2 ∧ Function.Injective ρ ∧
      (∀ c, J * ρ c * J⁻¹ = ρ c⁻¹) ∧
      LinearMap.det ((J : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) = 1 := by
  have hLc : CharP L p₀ := h.charP
  have hp : Fact p₀.Prime := ⟨h.prime⟩
  have hq1 : 1 ≤ q := suBlock_q_pos hq
  have hdvd : m ∣ Nat.card L - 1 := by
    rw [Nat.card_eq_fintype_card, hq, suBlock_sq_sub_one]
    exact dvd_mul_of_dvd_right hm _
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq hdvd
  have hζq1 : (ζ : L) ^ (q - 1) = 1 := by
    have h2 : ζ ^ (q - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hm)
    simpa using congrArg Units.val h2
  have hζbar : h.bar (ζ : L) = ζ := by
    rw [unitaryBar_eq_pow h hqf]
    calc (ζ : L) ^ q = (ζ : L) ^ (q - 1 + 1) := by rw [Nat.sub_add_cancel hq1]
      _ = (ζ : L) ^ (q - 1) * ζ := pow_succ _ _
      _ = ζ := by rw [hζq1, one_mul]
  have hζ' : Units.map h.bar.toMonoidHom ζ = ζ := Units.ext hζbar
  obtain ⟨lam, hlam0, hlambar⟩ : ∃ lam : L, lam ≠ 0 ∧ h.bar lam = -lam := by
    obtain ⟨x, hx⟩ := h.exists_bar_ne
    exact ⟨x - h.bar x, sub_ne_zero.2 (Ne.symm hx), by rw [map_sub, h.bar_bar]; ring⟩
  have hbarlam0 : h.bar lam ≠ 0 := by rw [hlambar]; exact neg_ne_zero.2 hlam0
  have hτ2 : ∀ c : L, h.bar (algebraMap L L c) = algebraMap L L (h.bar c) := fun c => rfl
  have hμ0 : (LinearMap.id : L →ₗ[L] L) ≠ 0 := by
    intro h0
    have := LinearMap.congr_fun h0 1
    simp at this
  have hτs2 : Function.Surjective h.bar := Finite.injective_iff_surjective.1 h.bar.injective
  let S₀ : FormSpace L L := ⟨L × L, fun v w => hypHerm (τ := h.bar) h hτ2 LinearMap.id v w⟩
  have hS₀ : IsHermitianSpace h S₀ := ⟨hypHerm (τ := h.bar) h hτ2 LinearMap.id,
    fun _ _ => rfl, hypHerm_isSymm h hτ2 LinearMap.id,
    hypHerm_separatingLeft h hτ2 LinearMap.id hμ0 hτs2⟩
  obtain ⟨gT, hgT⟩ : ∃ g : (L × L) ≃ₗ[L] (L × L),
      g = (DistribMulAction.toModuleAut L L ζ).prodCongr
        (DistribMulAction.toModuleAut L L ζ⁻¹) := ⟨_, rfl⟩
  have hgeq : twistUnitsHom L L (Units.map h.bar.toMonoidHom) ζ = gT := by
    rw [hgT]
    show (DistribMulAction.toModuleAut L L ζ).prodCongr
      (DistribMulAction.toModuleAut L L (Units.map h.bar.toMonoidHom ζ)⁻¹) = _
    rw [hζ']
  have hgmem : gT ∈ S₀.isom := by
    rw [← hgeq]
    exact fun v w => hypHerm_twistUnitsHom h hτ2 LinearMap.id ζ v w
  obtain ⟨ρ, hρ, hrange⟩ := suBlock_exists_hom hgmem (n := m)
    (by rw [← hgeq, orderOf_injective _ (twistUnitsHom_injective _) ζ, hζ])
  have hgTapp : ∀ v : L × L, gT v = ((ζ : L) * v.1, ((ζ⁻¹ : Lˣ) : L) * v.2) := fun v => by
    rw [hgT]
    rfl
  obtain ⟨gI, hgI⟩ : ∃ g : (L × L) ≃ₗ[L] (L × L),
      g = (DistribMulAction.toModuleAut L L ζ⁻¹).prodCongr
        (DistribMulAction.toModuleAut L L ζ) := ⟨_, rfl⟩
  have hgIapp : ∀ v : L × L, gI v = (((ζ⁻¹ : Lˣ) : L) * v.1, (ζ : L) * v.2) := fun v => by
    rw [hgI]
    rfl
  have hgg : gI * gT = 1 := by
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, hgTapp, hgIapp]
    refine Prod.ext ?_ ?_ <;> simp
  have hginv : gI = gT⁻¹ := eq_inv_of_mul_eq_one_left hgg
  obtain ⟨J, hJ⟩ : ∃ J : (L × L) ≃ₗ[L] (L × L), J = (LinearEquiv.prodComm L L L).trans
      ((DistribMulAction.toModuleAut L L (Units.mk0 lam hlam0)).prodCongr
        (DistribMulAction.toModuleAut L L (Units.mk0 (h.bar lam)⁻¹ (inv_ne_zero hbarlam0)))) :=
    ⟨_, rfl⟩
  have hJapp : ∀ v : L × L, J v = (lam * v.2, (h.bar lam)⁻¹ * v.1) := fun v => by
    rw [hJ]
    rfl
  have hJiso : ∀ v w : L × L, hypHerm (τ := h.bar) h hτ2 LinearMap.id (J v) (J w) =
      hypHerm (τ := h.bar) h hτ2 LinearMap.id v w := by
    intro v w
    rw [hJapp, hJapp, hypHerm_apply, hypHerm_apply]
    simp only [LinearMap.id_apply, map_mul, map_inv₀, h.bar_bar]
    field_simp
    ring
  have hJmem : J ∈ S₀.isom := fun v w => hJiso v w
  have hJg : J * gT = gI * J := by
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgTapp, hJapp, hJapp, hgIapp]
    simp only [Prod.mk.injEq]
    constructor <;> ring
  have hJconj : J * gT * J⁻¹ = gT ^ (-1 : ℤ) := by
    rw [zpow_neg_one, mul_inv_eq_iff_eq_mul, hJg, hginv]
  have hdetJ : LinearMap.det ((J : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) = 1 := by
    show LinearMap.det ((J : (L × L) ≃ₗ[L] (L × L)) : (L × L) →ₗ[L] (L × L)) = 1
    rw [← LinearMap.det_toMatrix (Basis.finTwoProd L), Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, hJapp, hlambar]
    field_simp
  refine ⟨S₀, ρ, ⟨J, hJmem⟩, hS₀, ?_, hρ, ?_, hdetJ⟩
  · show finrank L (L × L) = 2
    rw [Module.finrank_prod, Module.finrank_self]
  · intro c
    refine Subtype.ext ?_
    rw [map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    have := suBlock_conj_zpow_of_mem hJconj (hrange c)
    exact this.trans (zpow_neg_one _)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
