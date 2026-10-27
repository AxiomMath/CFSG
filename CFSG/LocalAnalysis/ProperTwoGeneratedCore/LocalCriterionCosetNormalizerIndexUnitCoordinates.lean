module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCosetAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe v

variable {G : Type v} [Group G]

@[expose] def unitTranslateEquiv (U : Subgroup G) (u : G) :
    U ≃ ((fun x : G => u * x) '' (U : Set G)) where
  toFun x := ⟨u * (x : G), ⟨(x : G), x.property, rfl⟩⟩
  invFun y := ⟨u⁻¹ * (y : G), by
    change u⁻¹ * (y : G) ∈ (U : Set G)
    obtain ⟨x, hx, heq⟩ := y.property
    rw [← heq, inv_mul_cancel_left]
    exact hx⟩
  left_inv x := Subtype.ext (inv_mul_cancel_left u (x : G))
  right_inv y := Subtype.ext (mul_inv_cancel_left u (y : G))

theorem unitTranslateEquiv_apply (U : Subgroup G) (u : G) (x : U) :
    ((unitTranslateEquiv U u x : ((fun y : G => u * y) '' (U : Set G))) : G) =
      u * (x : G) := rfl

theorem unitTranslateEquiv_symm_apply (U : Subgroup G) (u : G)
    (y : ((fun x : G => u * x) '' (U : Set G))) :
    ((unitTranslateEquiv U u).symm y : G) = u⁻¹ * (y : G) := rfl

@[expose] def unitCoordinatePerm (U : Subgroup G) (u : G) :
    Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)) →* Equiv.Perm U :=
  (unitTranslateEquiv U u).symm.permCongrHom.toMonoidHom.comp
    (cosetNormalizerPerm ((fun x : G => u * x) '' (U : Set G)))

theorem unitCoordinatePerm_apply (U : Subgroup G) (u : G)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) (x : U) :
    ((unitCoordinatePerm U u n x : U) : G) =
      u⁻¹ * ((n : G) * (u * (x : G)) * (n : G)⁻¹) := rfl

theorem unit_translate_entire_centralizer (U : Subgroup G) (u : G) :
    Subgroup.centralizer ((fun x : G => u * x) '' (U : Set G)) =
      Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G) := by
  ext n
  constructor
  · intro hn
    have hun : u * n = n * u := Subgroup.mem_centralizer_iff.mp hn u
      ⟨1, U.one_mem, mul_one u⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr hun.symm, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact mul_left_cancel (calc
      u * (x * n) = (u * x) * n := (mul_assoc _ _ _).symm
      _ = n * (u * x) := Subgroup.mem_centralizer_iff.mp hn (u * x) ⟨x, hx, rfl⟩
      _ = (n * u) * x := (mul_assoc _ _ _).symm
      _ = (u * n) * x := congrArg (fun y : G => y * x) hun.symm
      _ = u * (n * x) := mul_assoc _ _ _)
  · rintro ⟨hnu, hnU⟩
    have hnu' := Subgroup.mem_centralizer_singleton_iff.mp hnu
    apply Subgroup.mem_centralizer_iff.mpr
    rintro y ⟨x, hx, rfl⟩
    calc
      (u * x) * n = u * (x * n) := mul_assoc _ _ _
      _ = u * (n * x) := congrArg (fun y : G => u * y)
        (Subgroup.mem_centralizer_iff.mp hnU x hx)
      _ = (u * n) * x := (mul_assoc _ _ _).symm
      _ = (n * u) * x := congrArg (fun y : G => y * x) hnu'.symm
      _ = n * (u * x) := mul_assoc _ _ _

theorem unitCoordinatePerm_ker (U : Subgroup G) (u : G) :
    (unitCoordinatePerm U u).ker =
      (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) := by
  rw [unitCoordinatePerm, MonoidHom.ker_comp_of_injective _ _
    (unitTranslateEquiv U u).symm.permCongrHom.injective,
    cosetNormalizerPerm_ker_eq_entire_centralizer, unit_translate_entire_centralizer]

theorem unitCoordinatePerm_ker_map (U : Subgroup G) (u : G) :
    (unitCoordinatePerm U u).ker.map
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))).subtype =
      Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G) := by
  rw [unitCoordinatePerm_ker]
  apply Subgroup.map_subgroupOf_eq_of_le
  rw [← unit_translate_entire_centralizer]
  exact Subgroup.centralizer_le_normalizer _

@[expose] def unitLinearConjugation (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)) →* MulAut U :=
  U.normalizerMonoidHom.comp (Subgroup.inclusion
    (involution_translate_normalizer_le_unit_normalizer U u hu hcentral))

theorem unitLinearConjugation_apply (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) (x : U) :
    ((unitLinearConjugation U u hu hcentral n x : U) : G) =
      (n : G) * (x : G) * (n : G)⁻¹ := rfl

theorem unitLinearConjugation_ker (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (unitLinearConjugation U u hu hcentral).ker =
      (Subgroup.centralizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) := by
  ext n
  change U.normalizerMonoidHom
      (Subgroup.inclusion (involution_translate_normalizer_le_unit_normalizer
        U u hu hcentral) n) = 1 ↔ (n : G) ∈ Subgroup.centralizer (U : Set G)
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
  rfl

theorem unitLinearConjugation_ker_map (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (unitLinearConjugation U u hu hcentral).ker.map
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))).subtype =
      Subgroup.centralizer (U : Set G) ⊓
        Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)) := by
  rw [unitLinearConjugation_ker, Subgroup.subgroupOf_map_subtype]

theorem unitCoordinatePerm_displacement_mul_conjugation (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) (x : U) :
    unitCoordinatePerm U u n x =
      unitCoordinatePerm U u n 1 * unitLinearConjugation U u hu hcentral n x := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, unitCoordinatePerm_apply, unitLinearConjugation_apply,
    Subgroup.coe_one, mul_one]
  simp only [mul_assoc, inv_mul_cancel_left]

theorem unitCoordinatePerm_one_eq_one_iff (U : Subgroup G) (u : G)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) :
    unitCoordinatePerm U u n 1 = 1 ↔ (n : G) ∈ Subgroup.centralizer ({u} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro heq
    have h := congrArg (fun x : U => (x : G)) heq
    rw [unitCoordinatePerm_apply, Subgroup.coe_one, mul_one] at h
    have hmul := congrArg (fun x : G => u * x * (n : G)) h
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
      inv_mul_cancel, mul_one, one_mul] using hmul
  · intro hn
    apply Subtype.ext
    rw [unitCoordinatePerm_apply]
    simp only [Subgroup.coe_one, mul_one]
    rw [hn]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    exact inv_mul_cancel u

theorem unitCoordinatePerm_displacement_mul (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (n m : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) :
    unitCoordinatePerm U u (n * m) 1 = unitCoordinatePerm U u n 1 *
      unitLinearConjugation U u hu hcentral n (unitCoordinatePerm U u m 1) := by
  calc
    unitCoordinatePerm U u (n * m) 1 =
        unitCoordinatePerm U u n (unitCoordinatePerm U u m 1) :=
      congrArg (fun e : Equiv.Perm U => e 1) ((unitCoordinatePerm U u).map_mul n m)
    _ = _ := unitCoordinatePerm_displacement_mul_conjugation U u hu hcentral n _

theorem unitCoordinatePerm_ker_eq_linear_ker_inter_u_centralizer (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (unitCoordinatePerm U u).ker =
      (unitLinearConjugation U u hu hcentral).ker ⊓
        (Subgroup.centralizer ({u} : Set G)).subgroupOf
          (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) := by
  rw [unitCoordinatePerm_ker, unitLinearConjugation_ker]
  ext n
  change ((n : G) ∈ Subgroup.centralizer ({u} : Set G) ∧
      (n : G) ∈ Subgroup.centralizer (U : Set G)) ↔
    ((n : G) ∈ Subgroup.centralizer (U : Set G) ∧
      (n : G) ∈ Subgroup.centralizer ({u} : Set G))
  exact and_comm

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
