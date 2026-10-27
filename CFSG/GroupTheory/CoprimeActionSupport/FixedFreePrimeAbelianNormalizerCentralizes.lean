module

public import CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition
public import CFSG.LinearAlgebra.CoprimeActions.FixedFreeNormalizerPreservesWeights

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeAbelianNormalizerCentralizes

open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

theorem centralizes {F : Type*} [Field F] [IsAlgClosed F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hρ : Function.Injective ρ)
    (r : ℕ) [Fact r.Prime] (D : Subgroup G) (hDcard : Nat.card D = r)
    (hD : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule F V))
    (E : Subgroup G) [hE : IsMulCommutative E] (hDE : D ≤ Subgroup.normalizer (E : Set G))
    (hEF : (Nat.card E : F) ≠ 0) (hrF : (r : F) ≠ 0) :
    D ≤ Subgroup.centralizer (E : Set G) := by
  classical
  letI : CommGroup E := { (inferInstance : Group E) with mul_comm := fun a b => mul_comm' a b }
  haveI : IsCyclic D := isCyclic_of_prime_card hDcard
  obtain ⟨⟨d, hdD⟩, hgen⟩ := IsCyclic.exists_generator (α := D)
  have hzp : Subgroup.zpowers d = D := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]; exact hdD
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (show (⟨x, hx⟩ : D) ∈ Subgroup.zpowers (⟨d, hdD⟩ : D) from hgen _)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
  have hker : LinearMap.ker (ρ d - LinearMap.id) = ⊥ := by
    rw [eq_bot_iff, ← hD]
    intro v hv
    have hv' : ρ d v = v := by simpa [sub_eq_zero] using hv
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    intro x hx
    rw [← hzp] at hx
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).mpr hx
    have : ∀ m : ℕ, ρ (d ^ m) v = v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, map_mul, Module.End.mul_apply, hv', ih]
    rw [← hn, this, sub_self]
  let ψ : G →* (V ≃ₗ[F] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp (MonoidHom.toHomUnits ρ)
  have hψ : ∀ g v, ψ g v = ρ g v := fun g v => rfl
  have hdr : d ^ r = 1 := by
    have := pow_card_eq_one' (G := D) (x := (⟨d, hdD⟩ : D))
    rw [hDcard] at this
    simpa using congrArg Subtype.val this
  set σ : V ≃ₗ[F] V := ψ d with hσ
  have hσr : σ ^ r = 1 := by rw [hσ, ← map_pow, hdr, map_one]
  have hσker : LinearMap.ker (σ.toLinearMap - LinearMap.id) = ⊥ := by
    rw [← hker]; rfl
  have hn : ∀ g : G, g ∈ E → d * g * d⁻¹ ∈ E := fun g hg => ((hDE hdD) g).1 hg
  have hn' : ∀ g : G, g ∈ E → d⁻¹ * g * d ∈ E := by
    intro g hg
    have := ((Subgroup.normalizer (E : Set G)).inv_mem (hDE hdD)) g
    simpa using this.1 hg
  let α : MulAut E :=
    { toFun := fun g => ⟨d * g * d⁻¹, hn g g.2⟩
      invFun := fun g => ⟨d⁻¹ * g * d, hn' g g.2⟩
      left_inv := fun g => by ext; simp [mul_assoc]
      right_inv := fun g => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hαk : ∀ (k : ℕ) (g : E), (((α ^ k) g : E) : G) = d ^ k * g * (d ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ, MulAut.mul_apply]
      rw [ih]
      show d ^ k * (d * (g : G) * d⁻¹) * (d ^ k)⁻¹ = _
      simp [pow_succ, mul_assoc]
  have hαr : α ^ r = 1 := by
    ext g
    rw [hαk, hdr]; simp
  let τ : Representation F E V := ρ.comp E.subtype
  have hcov : ∀ (g : E) v, σ (τ g v) = τ (α g) (σ v) := by
    intro g v
    have : ((α g : E) : G) = d * g * d⁻¹ := rfl
    simp only [τ, MonoidHom.comp_apply, Subgroup.coe_subtype, this, hσ, hψ, map_mul]
    rw [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (ρ d⁻¹), ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hspan := CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition.span_eq_top τ hEF
  have hcomm := CFSG.LinearAlgebra.CoprimeActions.FixedFreeNormalizerPreservesWeights.commutes_if_weights_span
    r τ σ hσr hσker α hαr hcov hspan
  have hdc : d ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 := LinearMap.congr_fun (hcomm ⟨e, he⟩)
    apply hρ
    ext v
    have := h1 v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    simp only [map_mul, Module.End.mul_apply]
    exact this.symm
  rw [← hzp, Subgroup.zpowers_le]
  exact hdc

end CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeAbelianNormalizerCentralizes
