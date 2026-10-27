module

public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelectionRep
public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelectionInertia

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed

open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.TwoRankLowerBound.Helpers

section Trace

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem liesAbove_of_restrict_eq {θ : CentralExtension F b m hm heven → ℂ}
    (hθ : θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    {ξ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ}
    (hξ : (fun g => ξ (SemidirectProduct.inl g)) = θ) : liesAbove hSigma ξ θ := by
  unfold liesAbove
  rw [hξ, CFSG.DirectProduct.blocksInnerProduct_self_of_mem hθ]
  exact zero_lt_one

theorem trace_normalization {σ₀ : Sigma} (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀)
    {θ : CentralExtension F b m hm heven → ℂ}
    (hθ : θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    (hStab : twistStabilizer hSigma θ = ⊤)
    {ξ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ}
    (hξ : ξ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma))
    (hξθ : (fun g => ξ (SemidirectProduct.inl g)) = θ) {a : ℂ} (hξa : ξ ⟨1, σ₀⟩ = a)
    (ha : a ≠ 0) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (R : Representation ℂ (CentralExtension F b m hm heven) V) (hR : R.IsIrreducible)
    (hRθ : R.character = θ) (T : (Module.End ℂ V)ˣ)
    (hT : ∀ k, (T : Module.End ℂ V) * R k * ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) =
      R (fieldAction F b m hm heven Sigma hSigma σ₀ k))
    (hTd : T ^ Nat.card Sigma = 1) :
    LinearMap.trace ℂ V (T : Module.End ℂ V) ≠ 0 ∧
      (a / LinearMap.trace ℂ V (T : Module.End ℂ V)) ^ Nat.card Sigma = 1 ∧
      ∀ (ω : ℂ) (ρ' : Representation ℂ (SemilinearExtension F b m hm heven Sigma hSigma) V),
        (∀ (k : CentralExtension F b m hm heven) (j : ℕ),
          ρ' ⟨k, σ₀ ^ j⟩ = R k * (ω • (T : Module.End ℂ V)) ^ j) →
        (ρ'.character = ξ ↔ ω = a / LinearMap.trace ℂ V (T : Module.End ℂ V)) := by
  set d := Nat.card Sigma with hd
  set trT := LinearMap.trace ℂ V (T : Module.End ℂ V) with htrT
  obtain ⟨ρT, hρT⟩ := exists_semilinear_representation hSigma hgen R T hT hTd
  have hρTres := semilinear_representation_comp_inl hSigma R (T : Module.End ℂ V) ρT hρT
  have hρTirr : ρT.IsIrreducible := by
    apply isIrreducible_of_comp_hom ρT SemidirectProduct.inl
    rw [hρTres]
    exact hR
  have hχT : ρT.character ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) :=
    ⟨V, inferInstance, inferInstance, inferInstance, ρT, hρTirr, rfl⟩
  have hχTθ : (fun g => ρT.character (SemidirectProduct.inl g)) = θ := by
    rw [← hRθ]
    funext g
    change LinearMap.trace ℂ V (ρT (SemidirectProduct.inl g)) =
      LinearMap.trace ℂ V (R g)
    rw [← MonoidHom.comp_apply, hρTres]
  obtain ⟨χ, hχ, hres, ρ₀, hξρ₀⟩ := exists_twistInduced_of_liesAbove hSigma hθ hξ
    (liesAbove_of_restrict_eq hSigma hθ hξθ)
  obtain ⟨-, -, hiff, -, -⟩ := twist_clifford hSigma hθ hχ hres
  obtain ⟨ρ₁, hχTρ₁⟩ := (hiff _ hχT).mp (liesAbove_of_restrict_eq hSigma hθ hχTθ)
  have hmem : ∀ y : SemilinearExtension F b m hm heven Sigma hSigma,
      y ∈ semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
        (twistStabilizer hSigma θ) := by
    intro y
    rw [mem_semilinearInertia_iff, hStab]
    exact Subgroup.mem_top _
  set ν : twistStabilizer hSigma θ →* ℂˣ := ρ₀ * ρ₁⁻¹ with hν
  have hξν : ∀ y, ξ y = ρT.character y * (ν ⟨y.right, hmem y⟩ : ℂ) := by
    intro y
    rw [hξρ₀, hχTρ₁, twistInduced_of_top hSigma hStab hχ ρ₀ y (hmem y),
      twistInduced_of_top hSigma hStab hχ ρ₁ y (hmem y), hν, MonoidHom.mul_apply,
      MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    have h0 : ((ρ₁ ⟨y.right, hmem y⟩ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  have hχTval : ∀ (k : CentralExtension F b m hm heven) (j : ℕ),
      ρT.character ⟨k, σ₀ ^ j⟩ = LinearMap.trace ℂ V (R k * (T : Module.End ℂ V) ^ j) := by
    intro k j
    change LinearMap.trace ℂ V (ρT ⟨k, σ₀ ^ j⟩) = _
    rw [hρT]
  have hσ₀ : σ₀ ∈ twistStabilizer hSigma θ := by
    rw [hStab]
    exact Subgroup.mem_top _
  set s₀ : twistStabilizer hSigma θ := ⟨σ₀, hσ₀⟩ with hs₀
  have hνpow : ∀ (k : CentralExtension F b m hm heven) (j : ℕ),
      (ν ⟨(⟨k, σ₀ ^ j⟩ : SemilinearExtension F b m hm heven Sigma hSigma).right,
        hmem ⟨k, σ₀ ^ j⟩⟩ : ℂ) = (ν s₀ : ℂ) ^ j := by
    intro k j
    have he : (⟨(⟨k, σ₀ ^ j⟩ : SemilinearExtension F b m hm heven Sigma hSigma).right,
        hmem ⟨k, σ₀ ^ j⟩⟩ : twistStabilizer hSigma θ) = s₀ ^ j :=
      Subtype.ext (by rw [SubgroupClass.coe_pow])
    rw [he, map_pow, Units.val_pow_eq_pow_val]
  have hξval : ∀ (k : CentralExtension F b m hm heven) (j : ℕ),
      ξ ⟨k, σ₀ ^ j⟩ = LinearMap.trace ℂ V (R k * (T : Module.End ℂ V) ^ j) *
        (ν s₀ : ℂ) ^ j := by
    intro k j
    rw [hξν, hχTval, hνpow]
  have hat : a = trT * (ν s₀ : ℂ) := by
    have h := hξval 1 1
    simp only [pow_one, map_one, one_mul] at h
    rw [← hξa, h]
  have htr0 : trT ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hat
    exact ha hat
  have hc : a / trT = (ν s₀ : ℂ) := by
    rw [hat]
    field_simp
  have hσd : s₀ ^ d = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hs₀, OneMemClass.coe_one, hd,
      ← orderOf_eq_card_of_forall_mem_zpowers hgen]
    exact pow_orderOf_eq_one σ₀
  refine ⟨htr0, ?_, fun ω ρ' hρ' => ?_⟩
  · rw [hc, ← Units.val_pow_eq_pow_val, ← map_pow, hσd, map_one, Units.val_one]
  · have hval' : ∀ (k : CentralExtension F b m hm heven) (j : ℕ),
        ρ'.character ⟨k, σ₀ ^ j⟩ =
          ω ^ j * LinearMap.trace ℂ V (R k * (T : Module.End ℂ V) ^ j) := by
      intro k j
      change LinearMap.trace ℂ V (ρ' ⟨k, σ₀ ^ j⟩) = _
      rw [hρ', trace_mul_smul_pow]
    constructor
    · intro h
      have h1 := congrFun h ⟨1, σ₀ ^ 1⟩
      rw [hval', hξval] at h1
      simp only [pow_one, map_one, one_mul] at h1
      rw [hc]
      exact mul_right_cancel₀ htr0 (by rw [h1, mul_comm])
    · intro hω
      funext y
      obtain ⟨j, hj⟩ := exists_pow_eq_of_generator hgen y.right
      have hy : y = ⟨y.left, σ₀ ^ j⟩ := by
        rw [hj]
      rw [hy, hval', hξval, hω, hc, mul_comm]

theorem eq_of_restrict_eq_of_generator_value {σ₀ : Sigma}
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) {θ : CentralExtension F b m hm heven → ℂ}
    (hθ : θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    (hStab : twistStabilizer hSigma θ = ⊤)
    {ξ₁ ξ₂ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ}
    (hξ₁ : ξ₁ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma))
    (hξ₂ : ξ₂ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma))
    (h₁ : (fun g => ξ₁ (SemidirectProduct.inl g)) = θ)
    (h₂ : (fun g => ξ₂ (SemidirectProduct.inl g)) = θ) (hv : ξ₁ ⟨1, σ₀⟩ = ξ₂ ⟨1, σ₀⟩)
    (hv0 : ξ₁ ⟨1, σ₀⟩ ≠ 0) : ξ₁ = ξ₂ := by
  obtain ⟨χ, hχ, hres, ρ₁, hξρ₁⟩ := exists_twistInduced_of_liesAbove hSigma hθ hξ₁
    (liesAbove_of_restrict_eq hSigma hθ h₁)
  obtain ⟨-, -, hiff, -, -⟩ := twist_clifford hSigma hθ hχ hres
  obtain ⟨ρ₂, hξρ₂⟩ := (hiff _ hξ₂).mp (liesAbove_of_restrict_eq hSigma hθ h₂)
  have hmem : ∀ y : SemilinearExtension F b m hm heven Sigma hSigma,
      y ∈ semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
        (twistStabilizer hSigma θ) := by
    intro y
    rw [mem_semilinearInertia_iff, hStab]
    exact Subgroup.mem_top _
  have hσ₀ : σ₀ ∈ twistStabilizer hSigma θ := by
    rw [hStab]
    exact Subgroup.mem_top _
  set s₀ : twistStabilizer hSigma θ := ⟨σ₀, hσ₀⟩ with hs₀
  have hv₁ := twistInduced_of_top hSigma hStab hχ ρ₁ ⟨1, σ₀⟩ (hmem _)
  have hv₂ := twistInduced_of_top hSigma hStab hχ ρ₂ ⟨1, σ₀⟩ (hmem _)
  rw [← hξρ₁] at hv₁
  rw [← hξρ₂] at hv₂
  have hρ : ρ₁ s₀ = ρ₂ s₀ := by
    have hne : χ ⟨⟨1, σ₀⟩, hmem _⟩ ≠ 0 := by
      intro h0
      rw [hv₁, h0, zero_mul] at hv0
      exact hv0 rfl
    apply Units.ext
    exact mul_left_cancel₀ hne ((hv₁.symm.trans hv).trans hv₂)
  have hρeq : ρ₁ = ρ₂ := by
    refine MonoidHom.ext fun s => ?_
    obtain ⟨j, hj⟩ := exists_pow_eq_of_generator hgen (s : Sigma)
    have hs : s = s₀ ^ j := Subtype.ext (by rw [SubgroupClass.coe_pow, hs₀, ← hj])
    rw [hs, map_pow, map_pow, hρ]
  rw [hξρ₁, hξρ₂, hρeq]

end Trace

end CFSG.Wreathed
