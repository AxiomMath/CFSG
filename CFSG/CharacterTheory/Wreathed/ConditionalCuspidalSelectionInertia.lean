module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalSum
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearTwistClifford

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.TwoRankLowerBound.Helpers

theorem inducedFunction_of_forall_mem {G : Type*} [Group G] [Fintype G] (I : Subgroup G)
    (hI : ∀ g, g ∈ I) (f : I → ℂ) (hf : ∀ x y : I, f (y * x * y⁻¹) = f x) (g : G) :
    inducedFunction I f g = f ⟨g, hI g⟩ := by
  unfold inducedFunction
  have hterm : ∀ c : G, (if hmem : c⁻¹ * g * c ∈ I then f ⟨c⁻¹ * g * c, hmem⟩ else 0) =
      f ⟨g, hI g⟩ := by
    intro c
    rw [dite_eq_left (hI _)]
    have h := hf ⟨g, hI g⟩ ⟨c⁻¹, hI _⟩
    have he : (⟨c⁻¹, hI _⟩ : I) * ⟨g, hI g⟩ * (⟨c⁻¹, hI _⟩ : I)⁻¹ =
        ⟨c⁻¹ * g * c, hI _⟩ := Subtype.ext (by simp)
    rw [he] at h
    exact h
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Nat.card I = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr ⟨Subtype.val, fun x => ⟨x, hI x⟩, fun _ => rfl, fun _ => rfl⟩
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hcard, ← mul_assoc, inv_mul_cancel₀ hG, one_mul]

section Top

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

omit [Fintype F] in
theorem twist_integrand_classFunction {S : Subgroup Sigma}
    {χ : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S → ℂ}
    (hχ : χ ∈ BlocksIrr (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S))
    (ρ : S →* ℂˣ) (x y : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
    χ (y * x * y⁻¹) * (ρ ⟨((y * x * y⁻¹ : semilinearInertia (hm := hm) (heven := heven)
        (hSigma := hSigma) S) : SemilinearExtension F b m hm heven Sigma hSigma).right,
        (y * x * y⁻¹).2⟩ : ℂ) =
      χ x * (ρ ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).right, x.2⟩ : ℂ) := by
  let r : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S →* S :=
    (SemidirectProduct.rightHom.comp (semilinearInertia S).subtype).codRestrict S fun z => z.2
  have hr : ∀ z : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S,
      (⟨(z : SemilinearExtension F b m hm heven Sigma hSigma).right, z.2⟩ : S) = r z :=
    fun _ => rfl
  rw [hr, hr, classFunction_of_blocksIrr hχ x y, map_mul, map_mul, map_inv, map_mul, map_mul,
    map_inv, mul_comm (ρ (r y)) (ρ (r x)), mul_assoc, mul_inv_cancel, mul_one]

theorem twistInduced_of_top {θ : CentralExtension F b m hm heven → ℂ}
    (hStab : twistStabilizer hSigma θ = ⊤)
    {χ : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
      (twistStabilizer hSigma θ) → ℂ}
    (hχ : χ ∈ BlocksIrr (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
      (twistStabilizer hSigma θ)))
    (ρ : twistStabilizer hSigma θ →* ℂˣ) (y : SemilinearExtension F b m hm heven Sigma hSigma)
    (hy : y ∈ semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
      (twistStabilizer hSigma θ)) :
    twistInduced hSigma θ χ ρ y = χ ⟨y, hy⟩ * (ρ ⟨y.right, hy⟩ : ℂ) := by
  have hall : ∀ z : SemilinearExtension F b m hm heven Sigma hSigma,
      z ∈ semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
        (twistStabilizer hSigma θ) := by
    intro z
    rw [mem_semilinearInertia_iff, hStab]
    exact Subgroup.mem_top _
  rw [twistInduced, inducedFunction_of_forall_mem _ hall _
    (twist_integrand_classFunction hSigma hχ ρ) y]

theorem twistInduced_inl_of_top {θ : CentralExtension F b m hm heven → ℂ}
    (hStab : twistStabilizer hSigma θ = ⊤)
    {χ : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
      (twistStabilizer hSigma θ) → ℂ}
    (hχ : χ ∈ BlocksIrr (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
      (twistStabilizer hSigma θ)))
    (hres : ∀ (g : CentralExtension F b m hm heven)
      (hg : (SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma) ∈
        semilinearInertia (twistStabilizer hSigma θ)), χ ⟨SemidirectProduct.inl g, hg⟩ = θ g)
    (ρ : twistStabilizer hSigma θ →* ℂˣ) :
    (fun g => twistInduced hSigma θ χ ρ (SemidirectProduct.inl g)) = θ := by
  funext g
  have hg : (SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma) ∈
      semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
        (twistStabilizer hSigma θ) := by
    rw [mem_semilinearInertia_iff]
    exact Subgroup.one_mem _
  rw [twistInduced_of_top hSigma hStab hχ ρ _ hg, hres g hg]
  have h1 : (⟨(SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma).right,
      hg⟩ : twistStabilizer hSigma θ) = 1 := Subtype.ext rfl
  rw [h1, map_one, Units.val_one, mul_one]

theorem mem_twistStabilizer_of_twistInduced_ne_zero {θ : CentralExtension F b m hm heven → ℂ}
    (hθ : θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    {χ : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
      (twistStabilizer hSigma θ) → ℂ}
    (hχ : χ ∈ BlocksIrr (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
      (twistStabilizer hSigma θ)))
    (hres : ∀ (g : CentralExtension F b m hm heven)
      (hg : (SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma) ∈
        semilinearInertia (twistStabilizer hSigma θ)), χ ⟨SemidirectProduct.inl g, hg⟩ = θ g)
    (ρ : twistStabilizer hSigma θ →* ℂˣ) (g : CentralExtension F b m hm heven) (τ : Sigma)
    (hne : twistInduced hSigma θ χ ρ ⟨g, τ⟩ ≠ 0) : τ ∈ twistStabilizer hSigma θ := by
  by_contra hτ
  exact hne ((twist_clifford hSigma hθ hχ hres).2.2.2.2 ρ g τ hτ)

omit [Fintype F] in
theorem eq_top_of_generator_mem {S : Subgroup Sigma} {σ₀ : Sigma}
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (h : σ₀ ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen σ)
  exact S.zpow_mem h k

theorem exists_twistInduced_of_liesAbove {θ : CentralExtension F b m hm heven → ℂ}
    (hθ : θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    {ξ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ}
    (hξ : ξ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma))
    (habove : liesAbove hSigma ξ θ) :
    ∃ χ ∈ BlocksIrr (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
        (twistStabilizer hSigma θ)),
      (∀ (g : CentralExtension F b m hm heven)
        (hg : (SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma) ∈
          semilinearInertia (twistStabilizer hSigma θ)), χ ⟨SemidirectProduct.inl g, hg⟩ = θ g) ∧
      ∃ ρ, ξ = twistInduced hSigma θ χ ρ := by
  obtain ⟨χ, hχ, hres⟩ := exists_inertia_extension (hm := hm) (heven := heven) hSigma hθ
  obtain ⟨-, -, hiff, -, -⟩ := twist_clifford hSigma hθ hχ hres
  exact ⟨χ, hχ, hres, (hiff ξ hξ).mp habove⟩

end Top

end CFSG.Wreathed
