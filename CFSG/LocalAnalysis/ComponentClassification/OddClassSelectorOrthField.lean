module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalFourGroupCommutant

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalDescent
  CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)

variable {K : Type} [Field K] [Finite K] {d : ℕ}

omit [Finite K] in
theorem originalQuadratic_polarBilin_eq (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K (Fin d → K)) :
    originalQuadratic Q.polarBilin = Q := by
  ext x
  rw [originalQuadratic_apply, QuadraticMap.polarBilin_apply_apply, polar_self, two_smul]
  field_simp
  ring

theorem orth_field_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1)
    (hσ1 : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c)
    {Y : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      commutant (coordinateSemilinearMap g.val)))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) : False := by
  classical
  have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ he hK
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk2
  have hd0 : 0 < d := by omega
  have hsemi : ∀ (a : K) x, coordinateSemilinearMap g.val (a • x) =
      g.val.right a • coordinateSemilinearMap g.val x := coordinateSemilinearMap_smul g.val
  have hQτ := multiplier_spec Q g
  have hform : ∀ x y, Q.polarBilin (coordinateSemilinearMap g.val x)
      (coordinateSemilinearMap g.val y) =
        (multiplier Q g : K) * g.val.right (Q.polarBilin x y) := by
    intro x y
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar,
      ← map_add (coordinateSemilinearMap g.val) x y, hQτ, hQτ, hQτ, map_sub, map_sub]
    ring
  have hsquare : ∀ x, coordinateSemilinearMap g.val (coordinateSemilinearMap g.val x) =
      (c : K) • x := fun x => by
    rw [← coordinateSemilinearMap_mul, coordinateSemilinearMap_apply,
      coordinateSemilinearGroup_mul_matrix, hc, coordinateSemilinearGroup_mul_field, ← pow_two,
      hσ2]
    exact LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar c x
  obtain ⟨-, -, -, ⟨b, c', hb, hc'⟩, hall⟩ := odd_orthogonal_quadratic_semilinear_descent
    g.val.right hσ2 hσ1 h2 (by rw [Module.finrank_fin_fun]; exact hd0) Q.polarBilin
    (LocalAnalysis.ComponentInitial.OddOrthogonal.isSymm_polarBilin Q) hQ
    (coordinateSemilinearMap g.val) (multiplier Q g) c hsemi hform hsquare
  obtain ⟨-, -, -, -, hfin, hrank, -, hB0nd, -, -, hQ0pol, -, -, eD, -⟩ := hall b c' hb hc'
  set k₀ := fixedSubfield K g.val.right
  obtain ⟨hcard0, -⟩ := CatalogueBOrthogonalInvolutionRepresentation.field_involution_facts hℓ he
    hK hσ2 hσ1
  have hk₀ : Nat.card k₀ = Nat.card {c : K // g.val.right c = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight (mem_fixedSubfield K g.val.right))
  obtain ⟨j, hj, hjcard⟩ : ∃ j, 1 ≤ j ∧ Nat.card k₀ = ℓ ^ j := by
    have hdvd : Nat.card k₀ ∣ ℓ ^ e := by
      rw [← hK, hcard0, hk₀]
      exact Dvd.intro_left _ (_root_.sq _).symm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).mp hdvd
    have h2j : ℓ ^ (2 * j) = ℓ ^ e := by
      rw [pow_mul', ← hj, hk₀, ← hcard0, hK]
    have he2 : 2 * j = e := Nat.pow_right_injective hℓ.two_le h2j
    exact ⟨j, by omega, hj⟩
  have hodd₀ : Odd (Nat.card k₀) := by rw [hjcard]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have : Module.Finite k₀ (originalFixedSubspace g.val.right (coordinateSemilinearMap g.val) b
      hsemi) := hfin
  have hQ0nd : (originalDescendedQuadratic g.val.right (coordinateSemilinearMap g.val) b hsemi
      Q.polarBilin (multiplier Q g) c' hform hc').polarBilin.Nondegenerate := by
    rw [hQ0pol]
    exact hB0nd
  have h5 : 5 ≤ finrank k₀ (originalFixedSubspace g.val.right (coordinateSemilinearMap g.val) b
      hsemi) := by
    rw [hrank, Module.finrank_fin_fun]
    omega
  have hOQ : TauCeti.QuadraticMap.orthogonalGroup (originalQuadratic Q.polarBilin) =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [originalQuadratic_polarBilin_eq h2 Q]
  have hY' : CFSG.Assembly.IsComponentOf Y
      (TauCeti.QuadraticMap.orthogonalGroup (originalQuadratic Q.polarBilin) ⊓
        commutant (coordinateSemilinearMap g.val)) := by
    rw [hOQ]
    exact hY
  have hYO : Y ≤ TauCeti.QuadraticMap.orthogonalGroup (originalQuadratic Q.polarBilin) :=
    hY'.1.trans inf_le_left
  have hY₂ := isComponentOf_comap_of_le_range
    (TauCeti.QuadraticMap.orthogonalGroup (originalQuadratic Q.polarBilin)).subtype
    (TauCeti.QuadraticMap.orthogonalGroup (originalQuadratic Q.polarBilin)).subtype_injective hY'
    (by rw [Subgroup.range_subtype]; exact inf_le_left)
  have hS : (TauCeti.QuadraticMap.orthogonalGroup (originalQuadratic Q.polarBilin) ⊓
      commutant (coordinateSemilinearMap g.val)).comap
        (TauCeti.QuadraticMap.orthogonalGroup (originalQuadratic Q.polarBilin)).subtype =
      semilinearOrthogonalCentralizer (originalQuadratic Q.polarBilin)
        (coordinateSemilinearMap g.val) := by
    ext u
    rw [Subgroup.mem_comap, mem_semilinearOrthogonalCentralizer_iff, Subgroup.mem_inf,
      mem_commutant]
    exact ⟨fun h x => (h.2 x), fun h => ⟨u.2, h⟩⟩
  rw [hS] at hY₂
  have hY₁ := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hY₂.1).mp hY₂
  have eY := (Subgroup.subgroupOfEquivOfLe hY₂.1).trans (Subgroup.subgroupOfEquivOfLe hYO)
  have hL' := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent eD hY₁
  have hq := OddSelector.commutator_orthogonalGroup_quasisimple hodd₀ _ hQ0nd h5
  have hrange := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hL' hq
  obtain ⟨τ, hτ⟩ := OddSelector.exists_sp_four_hom hodd₀ _ hQ0nd h5
  have : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSp 2 k₀) :=
    OddSelector.isPerfect_statedSp le_rfl hodd₀
  have hτr : ∀ x, τ x ∈ ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup
      (originalQuadratic Q.polarBilin)).subtype).subgroupOf (semilinearOrthogonalCentralizer
        (originalQuadratic Q.polarBilin) (coordinateSemilinearMap g.val))).map eD.toMonoidHom :=
    fun x => by
      rw [hrange]
      exact OddSelector.map_mem_commutator_of_isPerfect τ x
  exact false_of_smallSource hs
    (OddSelector.not_small_source_of_sp_cover le_rfl hℓ hℓ2 hj hjcard _
      (ker_comp_codRestrict_le_center τ hτ hτr
        ((_root_.Subgroup.equivMapOfInjective _ eD.toMonoidHom eD.injective).symm.trans eY) σ
        hσk))

end CFSG.ComponentClassification.OddClassSelector
