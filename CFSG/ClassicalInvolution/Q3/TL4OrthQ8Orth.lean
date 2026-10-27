module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.OrthQ8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.ClassicalInvolution.Generic
  QuadraticMap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Type} [Group S]

omit [Group S] in
theorem orthDerived_le : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem ker_le_center {θ : ↥(orthDerived Q) →* S}
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) :
    θ.ker ≤ Subgroup.center ↥(orthDerived Q) := by
  intro z hz
  rw [hker, Subgroup.mem_subgroupOf] at hz
  rw [Subgroup.mem_center_iff]
  intro w
  exact Subtype.ext (commute_of_mem_scalars hz w).symm

omit [Group S] in
theorem exists_Q_ne_zero (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V] :
    ∃ v : V, Q v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_polar_ne_zero hQ hv
  apply hw
  show Q (v + w) - Q v - Q w = 0
  rw [hcon, hcon, hcon, sub_zero, sub_zero]

omit [Group S] in
theorem scalar_sq (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {c : K}
    (hc : ∀ v, g v = c • v) : c * c = 1 := by
  obtain ⟨v, hv⟩ := exists_Q_ne_zero hQ
  have h1 := map_of_mem hg v
  rw [hc, QuadraticMap.map_smul] at h1
  have h3 : (c * c - 1) * Q v = 0 := by linear_combination h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hv)

theorem ker_mul_self (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) :
    ∀ z ∈ θ.ker, z * z = 1 := by
  intro z hz
  rw [hker, Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := mem_scalars.mp hz
  have hcc := scalar_sq hQ (orthDerived_le z.2) hc
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hc v, hc, smul_smul, hcc, one_smul]
  rfl

theorem exists_smul_of_map_eq (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {m m' : ↥(orthDerived Q)} (h : θ m = θ m') :
    ∃ c : K, c * c = 1 ∧ ∀ v, (m' : V ≃ₗ[K] V) v = c • (m : V ≃ₗ[K] V) v := by
  have hz : m' * m⁻¹ ∈ θ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := mem_scalars.mp hz
  refine ⟨c, scalar_sq hQ (orthDerived_le (m' * m⁻¹).2) hc, fun v => ?_⟩
  have := hc ((m : V ≃ₗ[K] V) v)
  rwa [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
    LinearEquiv.inv_apply_apply'] at this

theorem exists_smul_of_mem_ker (hQ : (polarBilin Q).Nondegenerate)
    [Nontrivial V] {θ : ↥(orthDerived Q) →* S}
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) {z : ↥(orthDerived Q)}
    (hz : z ∈ θ.ker) : ∃ c : K, c * c = 1 ∧ ∀ v, (z : V ≃ₗ[K] V) v = c • v := by
  rw [hker, Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := mem_scalars.mp hz
  exact ⟨c, scalar_sq hQ (orthDerived_le z.2) hc, hc⟩

theorem sq_ne_neg_one [Finite K] (hK : Nat.card K = 3) (c : K) : c * c ≠ -1 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  intro h
  by_cases hc : c = 0
  · rw [hc, zero_mul] at h
    exact one_ne_zero (neg_eq_zero.mp h.symm)
  · have h1 := FiniteField.pow_card_sub_one_eq_one c hc
    rw [hcard, show 3 - 1 = 2 from rfl, pow_two, h] at h1
    exact two_ne_zero' hK (by linear_combination -h1)

theorem mul_self_eq_one [Finite K] (hK : Nat.card K = 3) {c : K} (hc : c ≠ 0) : c * c = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  have h1 := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [hcard, show 3 - 1 = 2 from rfl, pow_two] at h1

theorem eichler_pow_three (h3 : (3 : K) = 0) {u w : V} (huw : polar Q u w = 0) :
    eichler Q u w ^ 3 = 1 := by
  have h2w : polar Q u (w + w) = 0 := by rw [polar_add_right, huw, add_zero]
  rw [pow_three, eichler_mul huw huw, eichler_mul huw h2w,
    show w + (w + w) = (3 : K) • w by module, h3, zero_smul, eichler_zero_right]

theorem eichler_fix {u w v : V} (hu : Q u = 0) (huw : polar Q u w = 0) (h1 : polar Q v u = 0)
    (h2 : polar Q v w = 0) : eichler Q u w v = v := by
  rw [eichler_apply hu huw, h1, h2]
  simp

theorem exists_smul_of_gens [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    {S' : Submodule K V}
    (hS : PolarNondegOn Q S') (h3 : 3 ≤ Module.finrank K S') {M : V ≃ₗ[K] V}
    (hM : M ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hMS : ∀ v, v ∈ S' ↔ M v ∈ S')
    (hgen : ∀ u w, u ∈ S' → w ∈ S' → Q u = 0 → polar Q u w = 0 →
      M * eichler Q u w = eichler Q u w * M) : ∃ c : K, ∀ v ∈ S', M v = c • v := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  refine Orth15.exists_smul_of_commute_elemOn hodd hS h3 hM hMS fun h hh => ?_
  have hle : elemOn Q S' ≤ Subgroup.centralizer ({M} : Set (V ≃ₗ[K] V)) := by
    rw [elemOn, Subgroup.closure_le]
    rintro _ ⟨u, w, hu, hw, hQu, huw, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hgen u w hu hw hQu huw).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh)).symm

section Quat

variable {X Y : V ≃ₗ[K] V}

theorem mem_minusSp_iff_of_comm {ρ : V ≃ₗ[K] V} (hX : X * ρ = ρ * X) (v : V) :
    v ∈ minusSp ρ ↔ X v ∈ minusSp ρ := by
  constructor
  · exact fun hv => map_mem_minusSp hX hv
  · intro hv
    have hX' : X⁻¹ * ρ = ρ * X⁻¹ := inv_mul_eq_mul_inv_of hX
    have := map_mem_minusSp hX' hv
    rwa [LinearEquiv.inv_apply_apply'] at this

theorem mem_plusSp_iff_of_comm {ρ : V ≃ₗ[K] V} (hX : X * ρ = ρ * X) (v : V) :
    v ∈ plusSp ρ ↔ X v ∈ plusSp ρ := by
  constructor
  · exact fun hv => map_mem_plusSp hX hv
  · intro hv
    have hX' : X⁻¹ * ρ = ρ * X⁻¹ := inv_mul_eq_mul_inv_of hX
    have := map_mem_plusSp hX' hv
    rwa [LinearEquiv.inv_apply_apply'] at this

theorem quat_rels (hYY : Y * Y = X * X) (hYX : Y * X * (Y * X) = X * X) {v : V}
    (hv : v ∈ minusSp (X * X)) :
    X (X v) = -v ∧ Y (Y v) = -v ∧ Y (X v) = -X (Y v) := by
  have hρ : (X * X) v = -v := mem_minusSp.mp hv
  have hXX : X (X v) = -v := hρ
  have hYY' : Y (Y v) = -v := by
    have := LinearEquiv.congr_fun hYY v
    rw [LinearEquiv.mul_apply] at this
    rw [this]
    exact hρ
  refine ⟨hXX, hYY', ?_⟩
  have hYXY : Y * X * Y = X := by
    calc Y * X * Y = Y * X * (Y * X) * X⁻¹ := by group
      _ = X := by rw [hYX]; group
  have hYX' : Y * X = X * Y⁻¹ := by
    calc Y * X = Y * X * Y * Y⁻¹ := by group
      _ = X * Y⁻¹ := by rw [hYXY]
  have hYinv : Y⁻¹ v = -Y v := by
    apply Y.injective
    rw [LinearEquiv.apply_inv_apply', map_neg, hYY', neg_neg]
  have := LinearEquiv.congr_fun hYX' v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hYinv, map_neg] at this
  exact this

theorem false_of_moved (h2 : (2 : K) ≠ 0) (hYY : Y * Y = X * X)
    (hYX : Y * X * (Y * X) = X * X) {v : V} (hv : v ∈ minusSp (X * X)) (hv0 : v ≠ 0) {c : K}
    (hc : c * c = 1) (h : X v = c • Y v ∨ X v = c • Y⁻¹ v) : False := by
  obtain ⟨hXX, hYY', hYX'⟩ := quat_rels hYY hYX hv
  have hYinv : Y⁻¹ v = -Y v := by
    apply Y.injective
    rw [LinearEquiv.apply_inv_apply', map_neg, hYY', neg_neg]
  obtain ⟨d, hd, hXv⟩ : ∃ d : K, d * d = 1 ∧ X v = d • Y v := by
    rcases h with h | h
    · exact ⟨c, hc, h⟩
    · exact ⟨-c, by rw [neg_mul_neg, hc], by rw [h, hYinv, smul_neg, neg_smul]⟩
  have h1 : Y (X v) = -(d • v) := by rw [hXv, map_smul, hYY', smul_neg]
  have hYv : Y v = d • X v := by rw [hXv, smul_smul, hd, one_smul]
  have h3 : X (Y v) = -(d • v) := by rw [hYv, map_smul, hXX, smul_neg]
  rw [hYX', h3, neg_neg] at h1
  have h4 : (2 * d) • v = 0 := by
    rw [mul_smul, two_smul]
    nth_rw 1 [h1]
    exact neg_add_cancel _
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hd
    exact zero_ne_one hd
  exact hv0 ((smul_eq_zero.mp h4).resolve_left (mul_ne_zero h2 hd0))

end Quat

theorem finrank_le_four {W : Submodule K V} {X : V ≃ₗ[K] V} {u w : V}
    (h : ∀ v ∈ W, polar Q v u = 0 → polar Q v w = 0 → polar Q (X v) u = 0 →
      polar Q (X v) w = 0 → v = 0) : Module.finrank K W ≤ 4 := by
  let φ : W →ₗ[K] (Fin 4 → K) := LinearMap.pi fun i =>
    ![(polarBilin Q).flip u, (polarBilin Q).flip w, (polarBilin Q).flip u ∘ₗ (X : V →ₗ[K] V),
      (polarBilin Q).flip w ∘ₗ (X : V →ₗ[K] V)] i ∘ₗ W.subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    have h3 := congrFun hv 3
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      LinearMap.flip_apply, polarBilin_apply_apply, Pi.zero_apply] at h0 h1 h2 h3
    exact Subtype.ext (h v v.2 h0 h1 h2 h3)
  have := LinearMap.finrank_le_finrank_of_injective hφ
  simpa using this

end CFSG.ClassicalInvolution.Q3.TL4.OrthQ8
