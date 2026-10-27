module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearFaithfulness

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module Subgroup CFSG.ComponentClassification

variable {K : Type*} [Field K] {n : ℕ}

theorem conjAut_scalar (u : Kˣ) : conjAut n K (GeneralLinearGroup.scalar (Fin n) u) = 1 := by
  change descendAut n K (CatalogueBHigherLinearAction.slConjugation n K _) = 1
  rw [CatalogueBHigherLinearAction.slConjugation_scalar, map_one]

theorem eq_one_of_conjAut_mul_fieldAut_eq_one [Finite K] (hn : 3 ≤ n) (B : GL (Fin n) K)
    (τ : K ≃+* K) (h : conjAut n K B * fieldAut n K τ = 1) :
    τ = 1 ∧ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = B := by
  have hsl : ∀ g : SpecialLinearGroup (Fin n) K,
      proj n K (CatalogueBLinearSemilinear.slSemilinearAction n K B τ g) = proj n K g := by
    intro g
    have := congrArg (fun φ : MulAut (projectiveSL n K) => φ (proj n K g)) h
    simp only [MulAut.one_apply] at this
    rw [← this]
    rfl
  have hpsl : CatalogueBLinearSemilinear.semilinearAction n K B τ = 1 := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup (Fin n) K)) x
    rw [CatalogueBLinearSemilinear.semilinearAction_mk, MulAut.one_apply]
    have h1 := hsl g
    rw [proj_eq_proj_iff, scalars_eq_center] at h1
    exact QuotientGroup.eq.mpr h1
  exact (CatalogueBLinearSemilinear.semilinearAction_eq_one_iff n K (by omega) (Or.inl hn)
    B τ).mp hpsl

theorem pow_apply_of_sq {φ : K ≃+* K} (hφ : ∀ x, φ x = x ^ 2) :
    ∀ (k : ℕ) (x : K), (φ ^ k) x = x ^ 2 ^ k := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ, mul_comm]

theorem even_and_eq_pow_of_involution {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {σ : K ≃+* K} (hσ : σ ≠ 1) (hσσ : σ * σ = 1) :
    Even f ∧ ∀ x, σ x = x ^ 2 ^ (f / 2) := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality
    Nat.prime_two hf hK
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨k, hk, rfl⟩ : ∃ k < f, φ ^ k = σ := by
    have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
    rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k % f, Nat.mod_lt _ (by omega), ?_⟩
    rw [← hk, ← hord, pow_mod_orderOf]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hσ (pow_zero φ)
  have h2k : f ∣ 2 * k := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, two_mul, pow_add, hσσ]
  obtain ⟨c, hc⟩ := h2k
  have hc1 : c = 1 := by
    rcases c with _ | _ | c
    · omega
    · rfl
    · nlinarith
  rw [hc1, mul_one] at hc
  refine ⟨⟨k, by omega⟩, fun x => ?_⟩
  rw [pow_apply_of_sq hφ, show f / 2 = k by omega]

theorem exists_fixed_basis [CharP K 2] {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) {x₀ : K}
    (hx₀ : σ x₀ ≠ x₀) (T : (Fin n → K) → (Fin n → K)) (hadd : ∀ v w, T (v + w) = T v + T w)
    (hsmul : ∀ (c : K) v, T (c • v) = σ c • T v) (hTT : ∀ v, T (T v) = v) :
    ∃ H : GL (Fin n) K, ∀ c : Fin n,
      T (fun r => (H : Matrix (Fin n) (Fin n) K) r c) =
        fun r => (H : Matrix (Fin n) (Fin n) K) r c := by
  classical
  have hden : x₀ + σ x₀ ≠ 0 := by
    intro h
    apply hx₀
    rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]
  set e := x₀ / (x₀ + σ x₀) with he
  have hee : e + σ e = 1 := by
    rw [he, map_div₀, map_add, hσσ, add_comm (σ x₀) x₀, ← add_div, div_self hden]
  set Fix : Set (Fin n → K) := {v | T v = v} with hFix
  have hspan : Submodule.span K Fix = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    have hw₁ : v + T v ∈ Fix := by
      change T (v + T v) = v + T v
      rw [hadd, hTT, add_comm]
    have hw₂ : σ e • v + e • T v ∈ Fix := by
      change T (σ e • v + e • T v) = σ e • v + e • T v
      rw [hadd, hsmul, hsmul, hσσ, hTT, add_comm]
    have h2 : e • T v + e • T v = 0 := by rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    have hv : v = e • (v + T v) + (σ e • v + e • T v) := by
      calc v = (e + σ e) • v + (e • T v + e • T v) := by rw [hee, one_smul, h2, add_zero]
        _ = _ := by
          rw [smul_add, add_smul]
          abel
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hw₁))
      (Submodule.subset_span hw₂)
  obtain ⟨b, hbFix, hbspan, hbli⟩ := exists_linearIndependent K Fix
  rw [hspan] at hbspan
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin n → K)) := by
    rw [Subtype.range_coe, hbspan]
  let bas₀ := Basis.mk hbli hsp
  let _ := FiniteDimensional.fintypeBasisIndex bas₀
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis bas₀, Module.finrank_fin_fun]
  let bas := bas₀.reindex (Fintype.equivFinOfCardEq hcard)
  have hbas : ∀ c, T (bas c) = bas c := fun c => by
    rw [Basis.reindex_apply, Basis.mk_apply]
    exact hbFix (Subtype.mem _)
  obtain ⟨Hm, hHm⟩ : ∃ Hm : Matrix (Fin n) (Fin n) K, Hm = Matrix.of fun r c => bas c r :=
    ⟨_, rfl⟩
  have hHunit : IsUnit Hm := by
    rw [← mulVec_surjective_iff_isUnit]
    intro u
    refine ⟨bas.repr u, ?_⟩
    conv_rhs => rw [← bas.sum_repr u]
    ext r
    simp only [hHm, mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  refine ⟨hHunit.unit, fun c => ?_⟩
  have hcol : (fun r => (hHunit.unit : Matrix (Fin n) (Fin n) K) r c) = bas c := by
    rw [IsUnit.unit_spec, hHm]
    rfl
  rw [hcol]
  exact hbas c

theorem even_linear_field_involution_descent [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1) :
    Even f ∧ (∀ x, σ x = x ^ 2 ^ (f / 2)) ∧
      ∃ H : GL (Fin n) K, conjAut n K A * fieldAut n K σ =
        conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
  classical
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hsq :
      conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) A) * fieldAut n K (σ * σ) = 1 := by
    rw [← conjAut_mul_fieldAut_mul, ← pow_two]
    exact hα
  obtain ⟨hσσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ hsq
  obtain ⟨hfeven, hσpow⟩ := even_and_eq_pow_of_involution hf hK hσ hσσ
  have hσσx : ∀ x, σ (σ x) = x := fun x => by rw [← RingAut.mul_apply, hσσ]; rfl
  have hmapmap : GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.map (σ : K →+* K) A) =
      A := by
    ext i j
    simp [hσσx]
  have h1 : GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.map (σ : K →+* K) A * A := by
    rw [hc, map_mul, hmapmap]
  have h2 : GeneralLinearGroup.map (σ : K →+* K) A * A = GeneralLinearGroup.scalar (Fin n) c := by
    have h3 :
        GeneralLinearGroup.map (σ : K →+* K) A = A⁻¹ * GeneralLinearGroup.scalar (Fin n) c := by
      rw [hc]
      group
    rw [h3, mul_assoc, GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcfix : σ (c : K) = c := by
    have h3 := h1.trans h2
    have h4 := congrArg (fun g : GL (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) h3
    simpa [GeneralLinearGroup.coe_scalar] using h4
  obtain ⟨h, hh⟩ := hfeven
  have hud : UnitaryFieldData 2 h K := ⟨Nat.prime_two, by omega, by rw [hK, hh, two_mul]⟩
  have : CharP K 2 := hud.charP
  have hbar : ∀ x, hud.bar x = σ x := fun x => by
    rw [UnitaryFieldData.bar_apply, hσpow, show f / 2 = h by omega]
  have hcinv : ((c⁻¹ : Kˣ) : K) ∈ hud.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, hbar, Units.val_inv_eq_inv_val, map_inv₀, hcfix]
  obtain ⟨b, hb⟩ := (unitary_field_norm hud).1 ⟨_, hcinv⟩
  have hb' : b * σ b = ((c⁻¹ : Kˣ) : K) := by
    have := congrArg Subtype.val hb
    rwa [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm, hbar] at this
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hb'
    exact (Units.ne_zero _) hb'.symm
  set B := GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) * A with hB
  have hcB : conjAut n K B = conjAut n K A := by rw [hB, map_mul, conjAut_scalar, one_mul]
  have hBB : B * GeneralLinearGroup.map (σ : K →+* K) B = 1 := by
    rw [hB, map_mul, GeneralLinearGroup.map_scalar]
    calc GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) * A *
          (GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) (Units.mk0 b hb0)) *
            GeneralLinearGroup.map (σ : K →+* K) A)
        _ = GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) *
            GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) (Units.mk0 b hb0)) *
            (A * GeneralLinearGroup.map (σ : K →+* K) A) := by
          rw [mul_assoc, ← mul_assoc A, ← GeneralLinearGroup.scalar_commute]
          group
        _ = 1 := by
          rw [← hc, ← map_mul, ← map_mul, ← map_one (GeneralLinearGroup.scalar (Fin n))]
          congr 1
          ext
          simp [hb']
  set T : (Fin n → K) → (Fin n → K) := fun v =>
    (B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i) with hT
  have hBBm : (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K).map σ = 1 := by
    have := congrArg Units.val hBB
    simpa using this
  have hTT : ∀ v, T (T v) = v := by
    intro v
    have hσBv : (fun i => σ (((B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i)) i)) =
        (B : Matrix (Fin n) (Fin n) K).map σ *ᵥ v := by
      funext i
      have h1 := RingHom.map_mulVec (σ : K →+* K) (B : Matrix (Fin n) (Fin n) K)
        (fun i => σ (v i)) i
      simp only [RingEquiv.coe_toRingHom] at h1
      rw [h1]
      congr 2
      funext j
      exact hσσx (v j)
    simp only [hT]
    rw [hσBv, mulVec_mulVec, hBBm, one_mulVec]
  have hadd : ∀ v w, T (v + w) = T v + T w := fun v w => by
    simp only [hT, Pi.add_apply, map_add]
    rw [← mulVec_add]
    rfl
  have hsmul : ∀ (a : K) v, T (a • v) = σ a • T v := fun a v => by
    simp only [hT, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← mulVec_smul]
    rfl
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, σ x₀ ≠ x₀ := by
    by_contra hall
    exact hσ (RingEquiv.ext fun x => by
      by_contra hx
      exact hall ⟨x, hx⟩)
  obtain ⟨H, hH⟩ := exists_fixed_basis hσσx hx₀ T hadd hsmul hTT
  have hBH : B * GeneralLinearGroup.map (σ : K →+* K) H = H := by
    ext r c
    have := congrFun (hH c) r
    simp only [hT, mulVec, dotProduct] at this
    rw [← this]
    simp [Matrix.mul_apply]
  have hBeq : B = H * (GeneralLinearGroup.map (σ : K →+* K) H)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hBH
  refine ⟨⟨h, hh⟩, hσpow, H, ?_⟩
  have hfH : conjAut n K (GeneralLinearGroup.map (σ : K →+* K) H)⁻¹ * fieldAut n K σ =
      fieldAut n K σ * conjAut n K H⁻¹ := by
    rw [← map_inv, ← htrans.2.2.1 σ H⁻¹]
    group
  rw [← hcB, hBeq, map_mul, mul_assoc, hfH, ← mul_assoc, map_inv]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
