module

public import CFSG.ClassicalInvolution.Q3.Q3TJD4Fam
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution.Q3.Q3T CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (spinAction spinMatrix map_spinAction quadPlus
  quadPlus_apply nondegenerate_quadPlus spinToStatedProj_quadPlus
  range_spinAction_quadPlus_eq_commutator toLinEquiv_spinMatrix)

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "Q₀" => quadPlus 4 (ZMod 3)

@[expose] noncomputable def fkField : GaloisField 3 1 ≃+* ZMod 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  (GaloisField.equivZmodP 3).toRingEquiv

instance fkRingHomInvPair : RingHomInvPair fkField.toRingHom fkField.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv fkField

instance fkRingHomInvPairSymm : RingHomInvPair fkField.symm.toRingHom fkField.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm fkField

@[expose] noncomputable def fkCoord :
    (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₛₗ[fkField.toRingHom]
      (Fin 4 ⊕ Fin 4 → ZMod 3) where
  toFun v i := fkField (v i)
  invFun w i := fkField.symm (w i)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp
  left_inv v := by ext i; simp
  right_inv w := by ext i; simp

theorem fkCoord_apply (v : Fin 4 ⊕ Fin 4 → GaloisField 3 1) (i : Fin 4 ⊕ Fin 4) :
    fkCoord v i = fkField (v i) :=
  rfl

theorem quadPlus_fkCoord (v : Fin 4 ⊕ Fin 4 → GaloisField 3 1) :
    quadPlus 4 (ZMod 3) (fkCoord v) = fkField (quadPlus 4 (GaloisField 3 1) v) := by
  simp only [quadPlus_apply, map_sum, map_mul, fkCoord_apply]

theorem fk_mem_orth {a : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1)}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄) :
    LinearEquiv.autCongr fkCoord a ∈ TauCeti.QuadraticMap.orthogonalGroup Q₀ := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => ?_
  obtain ⟨v, rfl⟩ := fkCoord.surjective w
  rw [LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply, quadPlus_fkCoord,
    quadPlus_fkCoord, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp ha v]

theorem fk_mem_orth_symm {g : (Fin 4 ⊕ Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 ⊕ Fin 4 → ZMod 3)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₀) :
    (LinearEquiv.autCongr fkCoord).symm g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  apply fkField.injective
  rw [LinearEquiv.autCongr_symm_apply_apply, ← quadPlus_fkCoord, ← quadPlus_fkCoord,
    LinearEquiv.apply_symm_apply, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg]

theorem fk_map_orth :
    (TauCeti.QuadraticMap.orthogonalGroup Q₄).map (LinearEquiv.autCongr fkCoord).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q₀ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact fk_mem_orth ha
  · intro g hg
    exact ⟨_, fk_mem_orth_symm hg, by simp⟩

@[expose] noncomputable def fkOrth {a : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1)}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄) : OGroup Q₀ :=
  ⟨LinearEquiv.autCongr fkCoord a, fk_mem_orth ha⟩

@[expose] noncomputable def fkSpin : spinGroup Q₄ →* OGroup Q₀ :=
  ((LinearEquiv.autCongr fkCoord).toMonoidHom.comp (spinAction Q₄)).codRestrict
    (TauCeti.QuadraticMap.orthogonalGroup Q₀) fun x =>
      fk_mem_orth (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q₄ x))

theorem coe_fkSpin (x : spinGroup Q₄) :
    ((fkSpin x : OGroup Q₀) : (Fin 4 ⊕ Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 ⊕ Fin 4 → ZMod 3)) =
      LinearEquiv.autCongr fkCoord (spinAction Q₄ x) :=
  rfl

theorem fk_mem_omegaGroup_iff (g : OGroup Q₀) :
    g ∈ omegaGroup (nondegenerate_quadPlus 4 (ZMod 3)) ↔
      (g : (Fin 4 ⊕ Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 ⊕ Fin 4 → ZMod 3)) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q₀, TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ := by
  rw [omegaGroup_eq_commutator (nondegenerate_quadPlus 4 (ZMod 3)) (by
    rw [Module.finrank_fintype_fun_eq_card]; decide),
    ← Subgroup.map_subtype_commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)]
  constructor
  · intro h
    simpa using Subgroup.mem_map_of_mem (TauCeti.QuadraticMap.orthogonalGroup Q₀).subtype h
  · rintro ⟨y, hy, hxy⟩
    have hy' : y = g := Subtype.ext hxy
    rwa [hy'] at hy

theorem fkSpin_mem_omegaGroup (x : spinGroup Q₄) :
    fkSpin x ∈ omegaGroup (nondegenerate_quadPlus 4 (ZMod 3)) := by
  rw [fk_mem_omegaGroup_iff, coe_fkSpin]
  have h1 : spinAction Q₄ x ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₄,
      TauCeti.QuadraticMap.orthogonalGroup Q₄⁆ := by
    rw [← range_spinAction_quadPlus_eq_commutator (n := 4) (K := GaloisField 3 1) (by norm_num)]
    exact ⟨x, rfl⟩
  have h2 := Subgroup.mem_map_of_mem (LinearEquiv.autCongr fkCoord).toMonoidHom h1
  rwa [Subgroup.map_commutator, fk_map_orth] at h2

theorem fkSpin_exists_of_mem_omegaGroup {y : OGroup Q₀}
    (hy : y ∈ omegaGroup (nondegenerate_quadPlus 4 (ZMod 3))) : ∃ x, fkSpin x = y := by
  rw [fk_mem_omegaGroup_iff] at hy
  have hy' : (y : (Fin 4 ⊕ Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 ⊕ Fin 4 → ZMod 3)) ∈
      (⁅TauCeti.QuadraticMap.orthogonalGroup Q₄, TauCeti.QuadraticMap.orthogonalGroup Q₄⁆).map
        (LinearEquiv.autCongr fkCoord).toMonoidHom := by
    rw [Subgroup.map_commutator, fk_map_orth]
    exact hy
  obtain ⟨z, hz, hzy⟩ := hy'
  rw [← range_spinAction_quadPlus_eq_commutator (n := 4) (K := GaloisField 3 1) (by norm_num)]
    at hz
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, Subtype.ext hzy⟩

theorem fk_exists_quad_eq_one :
    ∃ v : Fin 4 ⊕ Fin 4 → GaloisField 3 1, quadPlus 4 (GaloisField 3 1) v = 1 :=
  ⟨Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1, by
    simp [quadPlus_apply, Pi.single_apply, Fin.sum_univ_succ]⟩

theorem fk_sq_eq_of_orth {a : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1)}
    (ha : ∀ v, quadPlus 4 (GaloisField 3 1) (a v) = quadPlus 4 (GaloisField 3 1) v)
    {s : GaloisField 3 1} (ha2 : ∀ v, a (a v) = s • v) : s = 1 ∨ s = -1 := by
  obtain ⟨v₀, hv₀⟩ := fk_exists_quad_eq_one
  have h := ha (a v₀)
  rw [ha v₀, ha2, QuadraticMap.map_smul, hv₀] at h
  have hs : s * s = 1 := by simpa using h
  exact mul_self_eq_one_iff.mp hs

theorem fk_mem_center_iff (x : spinGroup Q₄) :
    x ∈ Subgroup.center (spinGroup Q₄) ↔
      spinAction Q₄ x = 1 ∨ spinAction Q₄ x = LinearEquiv.neg (GaloisField 3 1) := by
  obtain ⟨-, hcomap, hZ⟩ :=
    spinToStatedProj_quadPlus (K := GaloisField 3 1) (n := 4) (by norm_num)
  rw [← hZ, hcomap, Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix,
    mem_scalars]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨v₀, hv⟩ := fk_exists_quad_eq_one
    have h := map_spinAction Q₄ x v₀
    rw [hd, QuadraticMap.map_smul, hv] at h
    have hd2 : d * d = 1 := by simpa using h
    rcases mul_self_eq_one_iff.mp hd2 with rfl | rfl
    · exact Or.inl (LinearEquiv.ext fun v => by simp [hd])
    · exact Or.inr (LinearEquiv.ext fun v => by simp [hd])
  · rintro (h | h)
    · exact ⟨1, fun v => by simp [h]⟩
    · exact ⟨-1, fun v => by simp [h]⟩

theorem fk_autCongr_neg :
    LinearEquiv.autCongr fkCoord (LinearEquiv.neg (GaloisField 3 1)) =
      ((piOrth Q₀ : OGroup Q₀) : (Fin 4 ⊕ Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 ⊕ Fin 4 → ZMod 3)) :=
  LinearEquiv.ext fun w => by
    rw [LinearEquiv.autCongr_apply_apply, coe_piOrth_apply]
    change fkCoord (-fkCoord.symm w) = -w
    rw [map_neg, LinearEquiv.apply_symm_apply]

theorem fkSpin_mem_piGroup_iff (x : spinGroup Q₄) :
    fkSpin x ∈ piGroup Q₀ ↔ x ∈ Subgroup.center (spinGroup Q₄) := by
  rw [fk_mem_center_iff, mem_piGroup_iff]
  constructor
  · rintro (h | h)
    · left
      have h' := congrArg (fun g : OGroup Q₀ => (g : (Fin 4 ⊕ Fin 4 → ZMod 3) ≃ₗ[ZMod 3]
        (Fin 4 ⊕ Fin 4 → ZMod 3))) h
      simp only [coe_fkSpin, OneMemClass.coe_one] at h'
      exact (LinearEquiv.autCongr fkCoord).injective (h'.trans (map_one _).symm)
    · right
      have h' := congrArg (fun g : OGroup Q₀ => (g : (Fin 4 ⊕ Fin 4 → ZMod 3) ≃ₗ[ZMod 3]
        (Fin 4 ⊕ Fin 4 → ZMod 3))) h
      simp only [coe_fkSpin] at h'
      exact (LinearEquiv.autCongr fkCoord).injective (h'.trans fk_autCongr_neg.symm)
  · rintro (h | h)
    · left
      exact Subtype.ext (by rw [coe_fkSpin, h, map_one]; rfl)
    · right
      exact Subtype.ext (by rw [coe_fkSpin, h, fk_autCongr_neg])

end CFSG.OddStandard.SmallF3.Omega
