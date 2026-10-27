module

public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.GroupTheory.WeirSylow.Symplectic

public section

namespace CFSG.GroupTheory.WeirSylow

open Module Finset
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Quasithin (StatedGU)

theorem ordMod_neg_natCast {p : ℕ} [Fact p.Prime] (q : ℕ) :
    ordMod p (-(q : ℤ)) = orderOf (-(q : ZMod p)) :=
  congrArg orderOf (by rw [Int.cast_neg, Int.cast_natCast]; rfl)

theorem factorization_card_statedGU {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) (L : Type)
    [Field L] [Fintype L] {q : ℕ} (hq : Fintype.card L = q ^ 2) (hpq : ¬ p ∣ q) {n : ℕ}
    (hn : 1 ≤ n) : (Nat.card (StatedGU n q L)).factorization p =
      padicValInt p ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1) *
          (n / orderOf (-(q : ZMod p))) +
        padicValNat p (n / orderOf (-(q : ZMod p))).factorial := by
  have hpZ := Nat.prime_iff_prime_int.mp hp.out
  have hq2 : 2 ≤ q := by
    by_contra h'
    have : q ^ 2 ≤ 1 := by
      interval_cases q <;> simp
    have := Fintype.one_lt_card (α := L)
    omega
  have hc : ¬ (p : ℤ) ∣ -(q : ℤ) := by
    rw [dvd_neg]
    exact_mod_cast hpq
  have hc2 : 2 ≤ |-(q : ℤ)| := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    exact_mod_cast hq2
  have hu : ¬ (p : ℤ) ∣ (q : ℤ) ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, (-1 : ℤ) ^ i := by
    intro h
    rcases hpZ.dvd_or_dvd h with h | h
    · exact hpq (by exact_mod_cast hpZ.dvd_of_dvd_pow h)
    · rw [Finset.prod_pow_eq_pow_sum] at h
      exact hpZ.not_isUnit (isUnit_of_dvd_unit h (isUnit_neg_one.pow _))
  rw [factorization_eq_of_cast_eq_mul_prod hp1 hc hc2 (natCard_statedGU_cast hq hn) hu,
    ordMod_neg_natCast]

section Tori

variable {p₀ f : ℕ} {L : Type} [Field L] (h : UnitaryFieldData p₀ f L)

section Trace

variable {M : Type} [Field M] [Algebra L M] {τ : M →+* M}

theorem bar_trace [Finite M] (hτ : ∀ c : L, τ (algebraMap L M c) = algebraMap L M (h.bar c))
    (z : M) :
    h.bar (Algebra.trace L M z) = Algebra.trace L M (τ z) := by
  apply (algebraMap L M).injective
  rw [← hτ, FiniteField.algebraMap_trace_eq_sum_pow, FiniteField.algebraMap_trace_eq_sum_pow,
    map_sum]
  exact Finset.sum_congr rfl fun i _ => map_pow τ z _

@[expose] noncomputable def traceHerm
    (hτ : ∀ c : L, τ (algebraMap L M c) = algebraMap L M (h.bar c)) :
    M →ₛₗ[h.bar] M →ₗ[L] L :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id L) (fun x y => Algebra.trace L M (τ x * y))
    (fun x x' y => by rw [map_add, add_mul, map_add])
    (fun c x y => by
      rw [Algebra.smul_def, map_mul τ, hτ, mul_assoc, ← Algebra.smul_def, map_smul,
        smul_eq_mul])
    (fun x y y' => by rw [mul_add, map_add])
    (fun c x y => by rw [mul_smul_comm, map_smul, RingHom.id_apply])

variable (hτ : ∀ c : L, τ (algebraMap L M c) = algebraMap L M (h.bar c))

theorem traceHerm_apply (x y : M) : traceHerm h hτ x y = Algebra.trace L M (τ x * y) :=
  rfl

theorem traceHerm_isSymm [Finite M] (hττ : ∀ x, τ (τ x) = x) : (traceHerm h hτ).IsSymm :=
  ⟨fun x y => by
    rw [traceHerm_apply, traceHerm_apply, bar_trace h hτ, map_mul, hττ, mul_comm]⟩

theorem traceHerm_separatingLeft [Finite M] : (traceHerm h hτ).SeparatingLeft := fun x hx => by
  by_contra hx0
  have hτx : τ x ≠ 0 := (map_ne_zero τ).2 hx0
  apply Algebra.trace_ne_zero L M
  ext w
  have := hx ((τ x)⁻¹ * w)
  rwa [traceHerm_apply, mul_inv_cancel_left₀ hτx] at this

theorem traceHerm_toModuleAut {u : Mˣ} (hu : τ u * u = 1) (x y : M) :
    traceHerm h hτ (DistribMulAction.toModuleAut L M u x)
      (DistribMulAction.toModuleAut L M u y) = traceHerm h hτ x y := by
  change Algebra.trace L M (τ (u • x) * (u • y)) = Algebra.trace L M (τ x * y)
  rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, map_mul τ, mul_mul_mul_comm, hu,
    one_mul]

end Trace

section Hyperbolic

variable {N : Type} [Field N] [Algebra L N] {τ : N →+* N}

theorem mu_tau_smul (hτ : ∀ c : L, τ (algebraMap L N c) = algebraMap L N (h.bar c))
    (μ : N →ₗ[L] L) (c : L) (x y : N) : μ (τ (c • x) * y) = h.bar c * μ (τ x * y) := by
  rw [Algebra.smul_def, map_mul τ, hτ, mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]

@[expose] noncomputable def hypHerm
    (hτ : ∀ c : L, τ (algebraMap L N c) = algebraMap L N (h.bar c)) (μ : N →ₗ[L] L) :
    (N × N) →ₛₗ[h.bar] (N × N) →ₗ[L] L :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id L)
    (fun v w => μ (τ v.1 * w.2) + h.bar (μ (τ w.1 * v.2)))
    (fun v v' w => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, add_mul, mul_add]
      ring)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [mu_tau_smul h hτ, mul_smul_comm, map_smul, smul_eq_mul, map_mul h.bar]
      ring)
    (fun v w w' => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, add_mul, mul_add]
      ring)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
      rw [mu_tau_smul h hτ, mul_smul_comm, map_smul, smul_eq_mul, map_mul h.bar, h.bar_bar]
      ring)

variable (hτ : ∀ c : L, τ (algebraMap L N c) = algebraMap L N (h.bar c)) (μ : N →ₗ[L] L)

theorem hypHerm_apply (v w : N × N) :
    hypHerm h hτ μ v w = μ (τ v.1 * w.2) + h.bar (μ (τ w.1 * v.2)) :=
  rfl

theorem hypHerm_isSymm : (hypHerm h hτ μ).IsSymm :=
  ⟨fun v w => by rw [hypHerm_apply, hypHerm_apply, map_add, h.bar_bar, add_comm]⟩

theorem hypHerm_separatingLeft (hμ : μ ≠ 0) (hτs : Function.Surjective τ) :
    (hypHerm h hτ μ).SeparatingLeft := fun v hv => by
  have h1 : ∀ z, μ (τ v.1 * z) = 0 := fun z => by
    simpa [hypHerm_apply] using hv (0, z)
  have h2 : ∀ z, μ (τ z * v.2) = 0 := fun z => by
    have := hv (z, 0)
    rw [hypHerm_apply, mul_zero, map_zero, zero_add] at this
    exact (map_eq_zero_iff h.bar h.bar.injective).1 this
  refine Prod.ext ?_ ?_
  · by_contra hx
    have hτx : τ v.1 ≠ 0 := (map_ne_zero τ).2 hx
    exact hμ (LinearMap.ext fun w => by simpa [mul_inv_cancel_left₀ hτx] using h1 ((τ v.1)⁻¹ * w))
  · by_contra hy
    refine hμ (LinearMap.ext fun w => ?_)
    obtain ⟨z, hz⟩ := hτs (w * v.2⁻¹)
    have := h2 z
    rwa [hz, inv_mul_cancel_right₀ hy] at this

variable (L N) in
@[expose] noncomputable def twistUnitsHom (φ : Nˣ →* Nˣ) : Nˣ →* ((N × N) ≃ₗ[L] (N × N)) where
  toFun u := (DistribMulAction.toModuleAut L N u).prodCongr
    (DistribMulAction.toModuleAut L N (φ u)⁻¹)
  map_one' := LinearEquiv.ext fun x => by
    change ((1 : Nˣ) • x.1, (φ 1)⁻¹ • x.2) = x
    rw [map_one, inv_one, one_smul, one_smul]
  map_mul' u v := LinearEquiv.ext fun x => by
    change ((u * v) • x.1, (φ (u * v))⁻¹ • x.2) = (u • v • x.1, (φ u)⁻¹ • (φ v)⁻¹ • x.2)
    rw [map_mul, mul_inv, mul_smul, mul_smul]

theorem twistUnitsHom_injective (φ : Nˣ →* Nˣ) : Function.Injective (twistUnitsHom L N φ) :=
  fun u v huv => by
    have := congrArg Prod.fst (LinearEquiv.congr_fun huv (1, 0))
    change u • (1 : N) = v • (1 : N) at this
    rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at this
    exact Units.ext this

theorem hypHerm_twistUnitsHom (u : Nˣ) (v w : N × N) :
    hypHerm h hτ μ (twistUnitsHom L N (Units.map τ.toMonoidHom) u v)
      (twistUnitsHom L N (Units.map τ.toMonoidHom) u w) = hypHerm h hτ μ v w := by
  change μ (τ (u • v.1) * ((Units.map τ.toMonoidHom u)⁻¹ • w.2)) +
      h.bar (μ (τ (u • w.1) * ((Units.map τ.toMonoidHom u)⁻¹ • v.2))) = _
  have key : ∀ x y : N, τ (u • x) * ((Units.map τ.toMonoidHom u)⁻¹ • y) = τ x * y := by
    intro x y
    rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, map_mul, mul_mul_mul_comm]
    have : τ (u : N) * (((Units.map τ.toMonoidHom u)⁻¹ : Nˣ) : N) = 1 := by
      rw [Units.val_inv_eq_inv_val, Units.coe_map]
      exact mul_inv_cancel₀ ((map_ne_zero τ).2 u.ne_zero)
    rw [this, one_mul]
  rw [key, key, hypHerm_apply]

end Hyperbolic

end Tori

theorem pow_pow_odd_eq {L : Type} [Field L] [Fintype L] {q : ℕ} (hq : Fintype.card L = q ^ 2)
    {e : ℕ} (he : Odd e) (c : L) : c ^ q ^ e = c ^ q := by
  obtain ⟨j, rfl⟩ := he
  rw [pow_succ, mul_comm, pow_mul, pow_mul, ← hq, FiniteField.pow_card_pow]

theorem exists_injective_sigmaModel_GU {p : ℕ} [hp : Fact p.Prime] (L : Type) [Field L]
    [Fintype L] {q : ℕ} (hq : Fintype.card L = q ^ 2) (hpq : ¬ p ∣ q) (n : ℕ) :
    ∃ φ : sigmaModel p (orderOf (-(q : ZMod p)))
        (padicValInt p ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1)) n →* StatedGU n q L,
      Function.Injective φ := by
  obtain ⟨f, hqf, h⟩ := exists_unitaryFieldData L hq
  have : Fact (ringChar L).Prime := ⟨h.prime⟩
  set e := orderOf (-(q : ZMod p)) with hedef
  set a := padicValInt p ((-(q : ℤ)) ^ e - 1) with hadef
  have he : 0 < e := by
    rw [hedef, ← ordMod_neg_natCast]
    exact ordMod_pos (by rw [dvd_neg]; exact_mod_cast hpq)
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · have := Fintype.one_lt_card (α := L)
      rw [hq] at this
      norm_num at this
    · exact hq0
  have hdvdZ : (p : ℤ) ^ a ∣ (-(q : ℤ)) ^ e - 1 := padicValInt_dvd _
  by_cases hev : Even e
  ·
    obtain ⟨k, hk⟩ := hev
    have hk0 : NeZero k := ⟨by omega⟩
    let N := FiniteField.Extension L (ringChar L) k
    have hNcard : Nat.card N = q ^ e := by
      rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card, hq, ← pow_mul, hk, two_mul]
    have hNdim : finrank L N = k := FiniteField.finrank_extension L _ k
    have hdvd : p ^ a ∣ Nat.card N - 1 := by
      rw [Even.neg_pow ⟨k, hk⟩] at hdvdZ
      rw [hNcard]
      have : ((q ^ e - 1 : ℕ) : ℤ) = (q : ℤ) ^ e - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow, Nat.cast_one]
      exact_mod_cast this ▸ hdvdZ
    obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq hdvd
    have : CharP N (ringChar L) := charP_of_injective_algebraMap (algebraMap L N).injective _
    let τ := iterateFrobenius N (ringChar L) f
    have hτ : ∀ c : L, τ (algebraMap L N c) = algebraMap L N (h.bar c) := fun c => by
      rw [iterateFrobenius_def, ← map_pow, h.bar_apply]
    have hτs : Function.Surjective τ := Finite.injective_iff_surjective.1 τ.injective
    obtain ⟨μ, hμ⟩ := exists_ne_zero_dual (K := L) N
    let S₀ : FormSpace L L := ⟨N × N, fun v w => hypHerm h hτ μ v w⟩
    have hS₀ : IsHermitianSpace h S₀ := ⟨hypHerm h hτ μ, fun _ _ => rfl,
      hypHerm_isSymm h hτ μ, hypHerm_separatingLeft h hτ μ hμ hτs⟩
    have hmem : twistUnitsHom L N (Units.map τ.toMonoidHom) ζ ∈ S₀.isom := fun v w =>
      hypHerm_twistUnitsHom h hτ μ ζ v w
    obtain ⟨ρ, hρ⟩ := exists_injective_hom_of_orderOf_eq hmem
      (by rw [orderOf_injective _ (twistUnitsHom_injective _) ζ, hζ])
    obtain ⟨S, hS, hSdim, φ, hφ⟩ := exists_sigmaModel_rep p (IsHermitianSpace h)
      (fun ι _ S hS => isHermitianSpace_pi S hS) S₀ hS₀
      (inferInstanceAs (Nontrivial (N × N))) ρ hρ e n
    let T := stdHermSpace h (n - e * (n / e))
    obtain ⟨ψ, hψ⟩ := exists_rep_prod S T φ hφ
    have hdim : finrank L (S.prod T).V = n := by
      rw [FormSpace.finrank_prod, hSdim, finrank_stdHermSpace]
      change finrank L (N × N) * (n / e) + _ = _
      rw [Module.finrank_prod, hNdim, ← hk]
      have := Nat.mul_div_le n e
      omega
    obtain ⟨χ, hχ⟩ := exists_injective_isom_statedGU hqf (S.prod T)
      (isHermitianSpace_prod S T hS (isHermitianSpace_stdHermSpace _)) hdim
    exact ⟨χ.comp ψ, hχ.comp hψ⟩
  ·
    have heo : Odd e := Nat.not_even_iff_odd.1 hev
    let M := FiniteField.Extension L (ringChar L) e
    have hMcard : Nat.card M = (q ^ e) ^ 2 := by
      rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card, hq, ← pow_mul, ← pow_mul,
        mul_comm]
    have hMdim : finrank L M = e := FiniteField.finrank_extension L _ e
    have hdvd1 : p ^ a ∣ q ^ e + 1 := by
      rw [Odd.neg_pow heo, show -(q : ℤ) ^ e - 1 = -((q : ℤ) ^ e + 1) by ring, dvd_neg]
        at hdvdZ
      exact_mod_cast hdvdZ
    have hdvd : p ^ a ∣ Nat.card M - 1 := by
      refine hdvd1.trans ⟨q ^ e - 1, ?_⟩
      have h1 : 1 ≤ q ^ e := Nat.one_le_pow _ _ hq1
      have h2 : 1 ≤ (q ^ e) ^ 2 := Nat.one_le_pow _ _ h1
      rw [hMcard]
      zify [h1, h2]
      ring
    obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq hdvd
    have : CharP M (ringChar L) := charP_of_injective_algebraMap (algebraMap L M).injective _
    let τ := iterateFrobenius M (ringChar L) (f * e)
    have hτpow : ∀ x : M, τ x = x ^ q ^ e := fun x => by
      rw [iterateFrobenius_def, pow_mul, ← hqf]
    have hτ : ∀ c : L, τ (algebraMap L M c) = algebraMap L M (h.bar c) := fun c => by
      rw [hτpow, ← map_pow, pow_pow_odd_eq hq heo, unitaryBar_eq_pow h hqf]
    have hττ : ∀ x, τ (τ x) = x := fun x => by
      rw [hτpow, hτpow, ← pow_mul, ← sq, ← hMcard, pow_natCard_eq]
    have hζτ : τ ζ * ζ = 1 := by
      rw [hτpow, ← pow_succ]
      have : ζ ^ (q ^ e + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hdvd1)
      have h' := congrArg Units.val this
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h'
    let S₀ : FormSpace L L := ⟨M, fun x y => traceHerm h hτ x y⟩
    have hS₀ : IsHermitianSpace h S₀ := ⟨traceHerm h hτ, fun _ _ => rfl,
      traceHerm_isSymm h hτ hττ, traceHerm_separatingLeft h hτ⟩
    have hmem : DistribMulAction.toModuleAut L M ζ ∈ S₀.isom := fun x y =>
      traceHerm_toModuleAut h hτ hζτ x y
    obtain ⟨ρ, hρ⟩ := exists_injective_hom_of_orderOf_eq hmem (by rw [orderOf_toModuleAut, hζ])
    obtain ⟨S, hS, hSdim, φ, hφ⟩ := exists_sigmaModel_rep p (IsHermitianSpace h)
      (fun ι _ S hS => isHermitianSpace_pi S hS) S₀ hS₀ (inferInstanceAs (Nontrivial M))
      ρ hρ e n
    let T := stdHermSpace h (n - e * (n / e))
    obtain ⟨ψ, hψ⟩ := exists_rep_prod S T φ hφ
    have hdim : finrank L (S.prod T).V = n := by
      rw [FormSpace.finrank_prod, hSdim, finrank_stdHermSpace]
      change finrank L M * (n / e) + _ = _
      rw [hMdim]
      have := Nat.mul_div_le n e
      omega
    obtain ⟨χ, hχ⟩ := exists_injective_isom_statedGU hqf (S.prod T)
      (isHermitianSpace_prod S T hS (isHermitianSpace_stdHermSpace _)) hdim
    exact ⟨χ.comp ψ, hχ.comp hψ⟩

theorem sylow_GU {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) (L : Type) [Field L] [Fintype L]
    {q : ℕ} (hq : Fintype.card L = q ^ 2) (hpq : ¬ p ∣ q) {n : ℕ} (hn : 1 ≤ n)
    (P : Sylow p (StatedGU n q L)) :
    Nonempty (P ≃* sigmaModel p (orderOf (-(q : ZMod p)))
      (padicValInt p ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1)) n) := by
  obtain ⟨φ, hφ⟩ := exists_injective_sigmaModel_GU L hq hpq n
  exact nonempty_sylow_mulEquiv_sigmaModel φ hφ (factorization_card_statedGU hp1 L hq hpq hn) P

end CFSG.GroupTheory.WeirSylow
