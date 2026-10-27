module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Arf
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.ArfModel
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open Matrix CFSG.Open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Transfer

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

noncomputable def glEquivCoord (φ : V ≃ₗ[ZMod 2] (ι → ZMod 2)) : GL ι (ZMod 2) ≃* (V ≃ₗ[ZMod 2] V) :=
  (Matrix.GeneralLinearGroup.toLin' (Module.Basis.ofEquivFun φ)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)

theorem glEquivCoord_apply (φ : V ≃ₗ[ZMod 2] (ι → ZMod 2)) (M : GL ι (ZMod 2)) (v : V) :
    glEquivCoord φ M v = φ.symm ((M : Matrix ι ι (ZMod 2)) *ᵥ φ v) := by
  have h := Matrix.GeneralLinearGroup.toLin'_apply (Module.Basis.ofEquivFun φ) M v
  have e : Fintype.linearCombination (ZMod 2) (⇑(Module.Basis.ofEquivFun φ))
      ((M : Matrix ι ι (ZMod 2)) *ᵥ (Module.Basis.ofEquivFun φ).repr v) =
      φ.symm ((M : Matrix ι ι (ZMod 2)) *ᵥ φ v) := by
    rw [Fintype.linearCombination_apply]
    have := (Module.Basis.ofEquivFun φ).equivFun_symm_apply ((M : Matrix ι ι (ZMod 2)) *ᵥ φ v)
    rw [Module.Basis.equivFun_ofEquivFun] at this
    have hr : ⇑((Module.Basis.ofEquivFun φ).repr v) = φ v :=
      funext fun i => Module.Basis.ofEquivFun_repr_apply φ v i
    rw [hr]
    exact this.symm
  exact h.trans e

theorem exists_mem_statedOmega_of_model (Qs : (ι → ZMod 2) → ZMod 2)
    (φ : V ≃ₗ[ZMod 2] (ι → ZMod 2)) (Q : V → ZMod 2) (hφ : ∀ v, Qs (φ v) = Q v) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (T g : V ≃ₗ[ZMod 2] V) (hT : ∀ v, Q (T v) = Q v)
    (hg : ∀ v, Q (g v) = Q v) (hord : orderOf T = p) (hfix : ∀ v, T v = v → v = 0)
    (hconj : g * T * g⁻¹ = T⁻¹) :
    ∃ A ∈ StatedOmega Qs, orderOf A = p ∧
      ∀ v : ι → ZMod 2, (A : Matrix ι ι (ZMod 2)) *ᵥ v = v → v = 0 := by
  have hact : ∀ (M : GL ι (ZMod 2)) (v : V),
      φ (glEquivCoord φ M v) = (M : Matrix ι ι (ZMod 2)) *ᵥ φ v := fun M v => by
    rw [glEquivCoord_apply, LinearEquiv.apply_symm_apply]
  have hiso : ∀ (U : V ≃ₗ[ZMod 2] V), (∀ v, Q (U v) = Q v) →
      ∀ w, Qs ((((glEquivCoord φ).symm U : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w) = Qs w := by
    intro U hU w
    obtain ⟨v, rfl⟩ := φ.surjective w
    rw [← hact, MulEquiv.apply_symm_apply, hφ, hφ, hU]
  set A := (glEquivCoord φ).symm T with hA
  set G := (glEquivCoord φ).symm g with hG
  have hAS : A ∈ Subgroup.closure
      {A : GL ι (ZMod 2) | ∀ v, Qs ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Qs v} :=
    Subgroup.subset_closure (hiso T hT)
  have hGS : G ∈ Subgroup.closure
      {A : GL ι (ZMod 2) | ∀ v, Qs ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Qs v} :=
    Subgroup.subset_closure (hiso g hg)
  have hcomm : ⁅G, A⁆ = A⁻¹ * A⁻¹ := by
    have : G * A * G⁻¹ = A⁻¹ := by
      apply (glEquivCoord φ).injective
      simp only [map_mul, map_inv, hA, hG, MulEquiv.apply_symm_apply]
      exact hconj
    rw [commutatorElement_def, this]
  have hordA : orderOf A = p := by rw [hA, MulEquiv.orderOf_eq]; exact hord
  have hmem : A⁻¹ * A⁻¹ ∈ StatedOmega Qs := hcomm ▸ Subgroup.commutator_mem_commutator hGS hAS
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have hApow : A ^ (2 * k) * A = 1 := by
    rw [← pow_succ, ← hk, ← hordA]; exact pow_orderOf_eq_one A
  have hAmem : A ∈ StatedOmega Qs := by
    have := Subgroup.pow_mem _ hmem k
    have e : (A⁻¹ * A⁻¹) ^ k = A := by
      have h2 : A ^ (2 * k) = A⁻¹ := eq_inv_of_mul_eq_one_left hApow
      rw [← _root_.mul_inv_rev, inv_pow, ← sq, ← pow_mul, h2, inv_inv]
    rwa [e] at this
  refine ⟨A, hAmem, hordA, fun w hw => ?_⟩
  obtain ⟨v, rfl⟩ := φ.surjective w
  have h1 : T v = v := by
    have := glEquivCoord_apply φ A v
    rw [hA, MulEquiv.apply_symm_apply] at this
    rw [this, hw]
    exact φ.symm_apply_apply v
  rw [hfix v h1, map_zero]

end Transfer

theorem eq_two_of_dvd_pred_succ {n p : ℕ} (hp : p.Prime) (h1 : p ∣ 2 ^ n - 1)
    (h2 : p ∣ 2 ^ n + 1) : p = 2 := by
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h3 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h1
  have e : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
  rw [e] at h3
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3

theorem exists_hasFixedPointFreeOrder_of_dvd {ε : Bool} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 1 ≤ n) (h : p ∣ (if ε then 2 ^ n - 1 else 2 ^ n + 1)) :
    HasFixedPointFreeOrder ε n p := by
  have hmodel : HasFpfModel n p := by
    cases ε
    · exact hasFpfModel_minus hp hn (by simpa using h)
    · exact hasFpfModel_plus hp hn (by simpa using h)
  obtain ⟨V, _, _, _, Q, hQ, hdim, T, g, hT, hg, hord, hfix, hconj⟩ := hmodel
  obtain ⟨ε', m, hstd, hm⟩ := exists_isStdSpace Q hQ
  have hmn : m = n := by
    have := finrank_of_isStdSpace_arf hstd hm
    omega
  subst hmn
  have hTp : T ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one T
  have hdvd := dvd_of_fpf hstd hm hp T hT hTp hfix
  have hε : ε' = ε := by
    cases ε <;> cases ε' <;> first
      | rfl
      | (exfalso; simp only [Bool.false_eq_true, ↓reduceIte] at h hdvd
         first
           | exact hp2 (eq_two_of_dvd_pred_succ hp hdvd h)
           | exact hp2 (eq_two_of_dvd_pred_succ hp h hdvd))
  subst hε
  cases ε'
  · obtain ⟨φ, hφ⟩ := hstd
    exact exists_mem_statedOmega_of_model (StatedQuadMinus m (ZMod 2) 1 1) φ Q
      (fun v => by rw [← hφ v, quadMinus_apply]; rfl) hp hp2 T g hT hg hord hfix hconj
  · obtain ⟨φ, hφ⟩ := hstd
    exact exists_mem_statedOmega_of_model (StatedQuadPlus m (ZMod 2)) φ Q
      (fun v => by rw [← hφ v, quadPlus_apply]; rfl) hp hp2 T g hT hg hord hfix hconj

theorem cs_quadMinus' {n : ℕ} (hn : 1 ≤ n) :
    cs (quadMinus n (ZMod 2) 1 1) = if (false : Bool) then 2 ^ n else -2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using cs_quadMinus k

section Converse

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_statedOmega_isometry (Qs : (ι → ZMod 2) → ZMod 2) {A : GL ι (ZMod 2)}
    (hA : A ∈ StatedOmega Qs) (v : ι → ZMod 2) : Qs ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Qs v := by
  set S : Set (GL ι (ZMod 2)) :=
    {A : GL ι (ZMod 2) | ∀ v, Qs ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Qs v} with hS
  have hcl : A ∈ Subgroup.closure S := by
    have : StatedOmega Qs ≤ Subgroup.closure S := by
      unfold StatedOmega
      rw [Subgroup.commutator_le]
      intro g₁ h₁ g₂ h₂
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
        (Subgroup.inv_mem _ h₂)
    exact this hA
  clear hA
  induction hcl using Subgroup.closure_induction generalizing v with
  | mem x hx => exact hx v
  | one => simp
  | mul a b _ _ iha ihb =>
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, iha, ihb]
  | inv a _ iha =>
    have h1 : (a : Matrix ι ι (ZMod 2)) *ᵥ (((a⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v) =
        v := by
      rw [Matrix.mulVec_mulVec]; simp
    conv_rhs => rw [← h1]
    rw [iha]

set_option backward.isDefEq.respectTransparency false in
theorem fpf_dvd_of_coord (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) {ε : Bool} {m : ℕ}
    (hcard : Fintype.card ι = 2 * m) (hcs : cs Q = if ε then 2 ^ m else -2 ^ m) {p : ℕ}
    (hp : p.Prime) (A : GL ι (ZMod 2))
    (hiso : ∀ v, Q ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Q v) (hord : orderOf A = p)
    (hfix : ∀ w : ι → ZMod 2, (A : Matrix ι ι (ZMod 2)) *ᵥ w = w → w = 0) :
    p ∣ (if ε then 2 ^ m - 1 else 2 ^ m + 1) := by
  have hfr : Module.finrank (ZMod 2) (ι → ZMod 2) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  let φ : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) := LinearEquiv.refl _ _
  have hact : ∀ v, glEquivCoord φ A v = (A : Matrix ι ι (ZMod 2)) *ᵥ v := fun v => by
    rw [glEquivCoord_apply]; rfl
  have hAp : A ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one A
  refine dvd_of_fpf_of_cs hfr hcs hp (glEquivCoord φ A) (fun v => ?_) (by rw [← map_pow, hAp, map_one])
    (fun v hv => ?_)
  · rw [hact]; exact hiso v
  · exact hfix v (by rw [← hact]; exact hv)

end Converse

theorem hasFixedPointFreeOrder_iff {ε : Bool} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) :
    HasFixedPointFreeOrder ε n p ↔ p ∣ (if ε then 2 ^ n - 1 else 2 ^ n + 1) := by
  refine ⟨fun h => ?_, exists_hasFixedPointFreeOrder_of_dvd hp hp2 hn⟩
  cases ε
  · obtain ⟨A, hA, hord, hfix⟩ := h
    have hiso := mem_statedOmega_isometry _ hA
    refine fpf_dvd_of_coord (quadMinus n (ZMod 2) 1 1) ?_ (cs_quadMinus' hn) hp A
      (fun v => by rw [quadMinus_apply, quadMinus_apply]; exact hiso v) hord hfix
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · obtain ⟨A, hA, hord, hfix⟩ := h
    have hiso := mem_statedOmega_isometry _ hA
    refine fpf_dvd_of_coord (quadPlus n (ZMod 2)) ?_ (by simpa using cs_quadPlus n) hp A
      (fun v => by rw [quadPlus_apply, quadPlus_apply]; exact hiso v) hord hfix
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
