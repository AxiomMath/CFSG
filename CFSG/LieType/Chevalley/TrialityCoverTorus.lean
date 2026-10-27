module

public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators
public import CFSG.LieType.Chevalley.EvenTrialityOrbitParametrization
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverHeight
public import CFSG.LieType.Chevalley.TwistedE6EvenCoverTorus

public noncomputable section

namespace CFSG.LieType.Chevalley.TrialityCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover

theorem odd_card_units_of_charTwo (L : Type*) [Field L] [Finite L] [CharP L 2] :
    Odd (Nat.card Lˣ) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hu2 : (u : L) * u = 1 := by
    rw [← Units.val_mul, ← pow_two, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : u ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hsq : ((u : L) + 1) * ((u : L) + 1) = 0 := by
    have h2' : (2 : L) = 0 := CharTwo.two_eq_zero
    linear_combination hu2 + ((u : L) + 1) * h2'
  have h0 : (u : L) + 1 = 0 := mul_self_eq_zero.1 hsq
  refine hu1 (Units.ext ?_)
  rw [Units.val_one]
  linear_combination h0 - (CharTwo.two_eq_zero : (2 : L) = 0)

variable {K : Type} [Field K] (σ : K ≃+* K)

abbrev unitsSigma : Kˣ →* Kˣ :=
  Units.map σ.toRingHom.toMonoidHom

@[expose] def torusParam :
    Kˣ × (trialityFixedField K σ.toRingHom)ˣ →* (Fin TwistTag.D4.tag.rank → Kˣ) where
  toFun p := d4Tuple p.1 (unitsSigma σ p.1) (trialityFixedUnit K σ p.2)
    (unitsSigma σ (unitsSigma σ p.1))
  map_one' := by
    funext i
    fin_cases i
    · rfl
    · exact map_one _
    · exact map_one _
    · show unitsSigma σ (unitsSigma σ 1) = 1
      rw [map_one, map_one]
  map_mul' p q := by
    funext i
    fin_cases i
    · rfl
    · exact map_mul _ _ _
    · exact map_mul _ _ _
    · show unitsSigma σ (unitsSigma σ (p.1 * q.1)) =
        unitsSigma σ (unitsSigma σ p.1) * unitsSigma σ (unitsSigma σ q.1)
      rw [map_mul, map_mul]

@[expose] def trialityTorus :
    Kˣ × (trialityFixedField K σ.toRingHom)ˣ →* ModGL TwistTag.D4.tag K :=
  (torusVec TwistTag.D4.tag K).comp (torusParam σ)

theorem torusParam_eq_mulSingle (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    torusParam σ p = Pi.mulSingle ⟨0, by decide⟩ p.1 * Pi.mulSingle ⟨1, by decide⟩
      (unitsSigma σ p.1) * Pi.mulSingle ⟨3, by decide⟩ (unitsSigma σ (unitsSigma σ p.1)) *
        Pi.mulSingle ⟨2, by decide⟩ (trialityFixedUnit K σ p.2) := by
  funext i
  fin_cases i <;> simp [torusParam, d4Tuple, Pi.mulSingle_apply] <;> rfl

theorem trialityTorus_eq
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorus σ p = trialityTorusHom σ p := by
  rw [trialityTorus, MonoidHom.comp_apply, torusParam_eq_mulSingle, map_mul, map_mul, map_mul,
    torusVec_mulSingle, torusVec_mulSingle, torusVec_mulSingle, torusVec_mulSingle,
    trialityTorusHom_apply, trialityOuterTorus_eq, trialityMiddleTorus]

theorem trialityTorus_mem_twistedFixedGroup
    (hσ : σ ^ 3 = 1)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorus σ p ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  rw [trialityTorus_eq]
  exact (Subgroup.mem_inf.1 (trialityTorusHom_mem_graphFixedTorus hσ p)).2

theorem pow_three_apply_eq (hσ : σ ^ 3 = 1) (c : K) : σ (σ (σ c)) = c := by
  rw [← ringEquiv_pow_three_apply, hσ]
  rfl

theorem trialityTorus_mem_graphFixedRootGroup
    [Finite K] [CharP K 2] (hσ : σ ^ 3 = 1)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorus σ p ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  rw [← (even_triality_fixed_group_eq_root_group K (ringChar.eq K 2) σ
    (pow_three_apply_eq σ hσ)).1]
  exact trialityTorus_mem_twistedFixedGroup σ hσ p

theorem rootChar_torusParam (β : Fin TwistTag.D4.tag.rank → ℤ)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    rootChar K β (torusParam σ p) = p.1 ^ cartanCoord β ⟨0, by decide⟩ *
      unitsSigma σ p.1 ^ cartanCoord β ⟨1, by decide⟩ *
      trialityFixedUnit K σ p.2 ^ cartanCoord β ⟨2, by decide⟩ *
      unitsSigma σ (unitsSigma σ p.1) ^ cartanCoord β ⟨3, by decide⟩ := by
  have key : ∀ (v : Fin 4 → Kˣ) (c : Fin 4 → ℤ),
      ∏ k, v k ^ c k = v 0 ^ c 0 * v 1 ^ c 1 * v 2 ^ c 2 * v 3 ^ c 3 :=
    fun v c => Fin.prod_univ_four _
  exact key (torusParam σ p) (cartanCoord β)

theorem torusParam_perm (hσ : σ ^ 3 = 1) (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ)
    (i : Fin TwistTag.D4.tag.rank) :
    torusParam σ p (TwistTag.D4.perm i) = unitsSigma σ (torusParam σ p i) := by
  have h0 : TwistTag.D4.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have h1 : TwistTag.D4.perm ⟨1, by decide⟩ = ⟨3, by decide⟩ := by decide
  have h2 : TwistTag.D4.perm ⟨2, by decide⟩ = ⟨2, by decide⟩ := by decide
  have h3 : TwistTag.D4.perm ⟨3, by decide⟩ = ⟨0, by decide⟩ := by decide
  fin_cases i
  · rw [show (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) = ⟨0, by decide⟩ from rfl, h0]
    rfl
  · rw [show (⟨1, by decide⟩ : Fin TwistTag.D4.tag.rank) = ⟨1, by decide⟩ from rfl, h1]
    rfl
  · rw [show (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) = ⟨2, by decide⟩ from rfl, h2]
    exact (units_map_trialityFixedUnit p.2).symm
  · rw [show (⟨3, by decide⟩ : Fin TwistTag.D4.tag.rank) = ⟨3, by decide⟩ from rfl, h3]
    exact (units_map_three hσ p.1).symm

theorem cartanCoord_permLattice (β : Fin TwistTag.D4.tag.rank → ℤ)
    (k : Fin TwistTag.D4.tag.rank) :
    cartanCoord (permLattice TwistTag.D4.perm β) k = cartanCoord β (TwistTag.D4.perm.symm k) := by
  simp only [cartanCoord, permLattice, Function.comp_apply]
  refine (Fintype.sum_equiv TwistTag.D4.perm _ _ fun j => ?_).symm
  rw [Equiv.symm_apply_apply, ← TwistTag.D4.cartan_perm, Equiv.apply_symm_apply]

theorem rootChar_permLattice_torusParam (hσ : σ ^ 3 = 1) (β : Fin TwistTag.D4.tag.rank → ℤ)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    rootChar K (permLattice TwistTag.D4.perm β) (torusParam σ p) =
      unitsSigma σ (rootChar K β (torusParam σ p)) := by
  rw [rootChar_apply, rootChar_apply, map_prod]
  simp only [map_zpow, ← torusParam_perm σ hσ p, cartanCoord_permLattice]
  exact Fintype.prod_equiv TwistTag.D4.perm.symm _ _ fun k => by rw [Equiv.apply_symm_apply]

theorem rootChar_permLattice_sq_torusParam (hσ : σ ^ 3 = 1) (β : Fin TwistTag.D4.tag.rank → ℤ)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    rootChar K (permLattice (TwistTag.D4.perm ^ 2) β) (torusParam σ p) =
      unitsSigma σ (unitsSigma σ (rootChar K β (torusParam σ p))) := by
  rw [pow_two, permLattice_mul, rootChar_permLattice_torusParam σ hσ,
    rootChar_permLattice_torusParam σ hσ]

theorem trialityTorus_conj_pinnedX
    {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.D4.tag β) (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityTorus σ p * pinnedX TwistTag.D4.tag K β c * (trialityTorus σ p)⁻¹ =
      pinnedX TwistTag.D4.tag K β ((rootChar K β (torusParam σ p) : K) * c) :=
  torusVec_conj_pinnedX hβ (torusParam σ p) c

theorem trialityTorus_conj_orbitProd
    (hσ : σ ^ 3 = 1) {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : ∀ h : ℕ, IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ h) α) ∧
      0 < height (permLattice (TwistTag.D4.perm ^ h) α))
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) (s : K) :
    trialityTorus σ p * (trialityOrbitProd K σ.toRingHom α s : ModGL TwistTag.D4.tag K) *
        (trialityTorus σ p)⁻¹ =
      trialityOrbitProd K σ.toRingHom α ((rootChar K α (torusParam σ p) : K) * s) := by
  have e1 : permLattice TwistTag.D4.perm α = permLattice (TwistTag.D4.perm ^ 1) α := by
    rw [pow_one]
  have hα0 : IsRoot TwistTag.D4.tag α := (hα 0).1
  have hα1 : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm α) := e1 ▸ (hα 1).1
  have hα2 : IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ 2) α) := (hα 2).1
  rw [coe_trialityOrbitProd, coe_trialityOrbitProd]
  set g := trialityTorus σ p
  have e : g * (pinnedX TwistTag.D4.tag K α s *
      pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) (σ.toRingHom s) *
      pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α)
        (σ.toRingHom (σ.toRingHom s))) * g⁻¹ =
      (g * pinnedX TwistTag.D4.tag K α s * g⁻¹) *
        (g * pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) (σ.toRingHom s) * g⁻¹) *
        (g * pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α)
          (σ.toRingHom (σ.toRingHom s)) * g⁻¹) := by
    group
  rw [e, trialityTorus_conj_pinnedX σ hα0, trialityTorus_conj_pinnedX σ hα1,
    trialityTorus_conj_pinnedX σ hα2, rootChar_permLattice_torusParam σ hσ,
    rootChar_permLattice_sq_torusParam σ hσ]
  simp only [Units.coe_map, MonoidHom.coe_ofClass, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingHom.toMonoidHom_eq_coe, map_mul]

end CFSG.LieType.Chevalley.TrialityCover
