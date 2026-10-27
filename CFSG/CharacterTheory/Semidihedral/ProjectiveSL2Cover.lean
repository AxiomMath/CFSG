module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.CharacterTheory.Semidihedral.QuaternionDoubleCoverUniqueness

public section

namespace CFSG.Semidihedral.ProjectiveSL2Cover

open Matrix
open CFSG.Assembly.LowTwoRank

universe u v

section NativeScalarQuotient

variable (F : Type u) [Field F]

@[expose] def minusIdentity : SpecialLinearGroup (Fin 2) F :=
  ⟨Matrix.scalar (Fin 2) (-1), by simp⟩

theorem minusIdentity_matrix :
    (minusIdentity F : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (-1) := rfl

theorem minusIdentity_eq_neg_one :
    minusIdentity F = (-1 : SpecialLinearGroup (Fin 2) F) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [minusIdentity]

theorem minusIdentity_square : (minusIdentity F) ^ 2 = 1 := by
  apply Subtype.ext
  change (Matrix.scalar (Fin 2) (-1 : F)) ^ 2 = (1 : Matrix (Fin 2) (Fin 2) F)
  rw [← map_pow]
  simp

theorem minusIdentity_mem_center :
    minusIdentity F ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1, by simp, rfl⟩

theorem minusIdentity_ne_one (hF : ringChar F ≠ 2) : minusIdentity F ≠ 1 := by
  intro h
  have hentry := congrArg (fun g : SpecialLinearGroup (Fin 2) F => g 0 0) h
  exact Ring.neg_one_ne_one_of_char_ne_two hF (by simpa [minusIdentity] using hentry)

theorem minusIdentity_order (hF : ringChar F ≠ 2) : orderOf (minusIdentity F) = 2 := by
  exact orderOf_eq_prime (minusIdentity_square F) (minusIdentity_ne_one F hF)

theorem mem_center_iff_eq_one_or_minusIdentity (g : SpecialLinearGroup (Fin 2) F) :
    g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔
      g = 1 ∨ g = minusIdentity F := by
  constructor
  · intro hg
    obtain ⟨a, ha, hmatrix⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
    have ha2 : a ^ 2 = 1 := by simpa using ha
    rcases sq_eq_one_iff.mp ha2 with rfl | rfl
    · left
      apply Subtype.ext
      simpa using hmatrix.symm
    · right
      exact Subtype.ext hmatrix.symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact minusIdentity_mem_center F

theorem center_eq_zpowers_minusIdentity :
    Subgroup.center (SpecialLinearGroup (Fin 2) F) = Subgroup.zpowers (minusIdentity F) := by
  apply le_antisymm
  · intro g hg
    rcases (mem_center_iff_eq_one_or_minusIdentity F g).mp hg with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (minusIdentity_mem_center F)

theorem center_card (hF : ringChar F ≠ 2) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) F)) = 2 := by
  rw [center_eq_zpowers_minusIdentity, Nat.card_zpowers, minusIdentity_order F hF]

@[expose] def nativeQuotient :
    SpecialLinearGroup (Fin 2) F →* ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))

theorem nativeQuotient_surjective : Function.Surjective (nativeQuotient F) :=
  QuotientGroup.mk'_surjective _

theorem nativeQuotient_ker :
    (nativeQuotient F).ker = Subgroup.zpowers (minusIdentity F) := by
  rw [nativeQuotient, QuotientGroup.ker_mk', center_eq_zpowers_minusIdentity]

theorem nativeQuotient_minusIdentity : nativeQuotient F (minusIdentity F) = 1 := by
  exact (QuotientGroup.eq_one_iff _).mpr (minusIdentity_mem_center F)

theorem quarterTurn_square :
    (CFSG.Semidihedral.OddLinearNormals.quarterTurn F) ^ 2 = minusIdentity F := by
  exact Subtype.ext (CFSG.Semidihedral.OddLinearNormals.quarterTurn_square_matrix F)

end NativeScalarQuotient

section ActualNativeScalarQuotient

variable (F : Type u) [Field F]

@[expose] def nativeScalarKernel (n : ℕ) : Subgroup (SpecialLinearGroup (Fin n) F) :=
  ((GeneralLinearGroup.scalar (Fin n)).range).comap Matrix.SpecialLinearGroup.toGL

theorem nativeScalarKernel_eq_center (n : ℕ) :
    nativeScalarKernel F n = Subgroup.center (SpecialLinearGroup (Fin n) F) := by
  ext g
  change Matrix.SpecialLinearGroup.toGL g ∈ (GeneralLinearGroup.scalar (Fin n)).range ↔ _
  rw [← GeneralLinearGroup.center_eq_range_scalar]
  exact Matrix.SpecialLinearGroup.toGL_mem_center_iff g

instance nativeScalarKernel_normal (n : ℕ) : (nativeScalarKernel F n).Normal := by
  rw [nativeScalarKernel_eq_center]
  infer_instance

theorem mem_nativeScalarKernel_iff (n : ℕ) (g : SpecialLinearGroup (Fin n) F) :
    g ∈ nativeScalarKernel F n ↔
      ∃ c : Fˣ, c ^ n = 1 ∧ GeneralLinearGroup.scalar (Fin n) c =
        Matrix.SpecialLinearGroup.toGL g := by
  change Matrix.SpecialLinearGroup.toGL g ∈ (GeneralLinearGroup.scalar (Fin n)).range ↔ _
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc⟩
    have hdet := Matrix.SpecialLinearGroup.coeToGL_det g
    rw [← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
    exact hdet
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

theorem nativeScalarKernel_two_eq_zpowers :
    nativeScalarKernel F 2 = Subgroup.zpowers (minusIdentity F) := by
  rw [nativeScalarKernel_eq_center, center_eq_zpowers_minusIdentity]

theorem nativeScalarKernel_two_card (hF : ringChar F ≠ 2) :
    Nat.card (nativeScalarKernel F 2) = 2 := by
  rw [nativeScalarKernel_two_eq_zpowers, Nat.card_zpowers, minusIdentity_order F hF]

abbrev NativeScalarProjective (n : ℕ) :=
  SpecialLinearGroup (Fin n) F ⧸ nativeScalarKernel F n

@[expose] def scalarQuotient (n : ℕ) :
    SpecialLinearGroup (Fin n) F →* NativeScalarProjective F n :=
  QuotientGroup.mk' (nativeScalarKernel F n)

theorem scalarQuotient_surjective (n : ℕ) : Function.Surjective (scalarQuotient F n) :=
  QuotientGroup.mk'_surjective _

theorem scalarQuotient_two_ker :
    (scalarQuotient F 2).ker = Subgroup.zpowers (minusIdentity F) := by
  exact (QuotientGroup.ker_mk' _).trans (nativeScalarKernel_two_eq_zpowers F)

@[expose] def scalarProjectiveEquivNative (n : ℕ) :
    NativeScalarProjective F n ≃* ProjectiveSpecialLinearGroup (Fin n) F :=
  QuotientGroup.quotientMulEquivOfEq (nativeScalarKernel_eq_center F n)

theorem scalarProjectiveEquivNative_mk (n : ℕ) (g : SpecialLinearGroup (Fin n) F) :
    scalarProjectiveEquivNative F n (scalarQuotient F n g) =
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) g := rfl

theorem nativeQuotient_eq_scalarQuotient_comp :
    nativeQuotient F = (scalarProjectiveEquivNative F 2).toMonoidHom.comp
      (scalarQuotient F 2) := by
  ext g
  rfl

end ActualNativeScalarQuotient

section StatedScalarQuotient

variable (K : Type) [Field K]

@[expose] def statedScalarKernel (n : ℕ) : Subgroup (StatedSL n K) :=
  (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)

instance statedScalarKernel_normal (n : ℕ) : (statedScalarKernel K n).Normal := by
  dsimp only [statedScalarKernel]
  infer_instance

theorem mem_statedSL_iff_det_eq_one (n : ℕ) (A : GL (Fin n) K) :
    A ∈ StatedSL n K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem mem_statedScalarKernel_iff (n : ℕ) (g : StatedSL n K) :
    g ∈ statedScalarKernel K n ↔
      ∃ c : Kˣ, c ^ n = 1 ∧ GeneralLinearGroup.scalar (Fin n) c = (g : GL (Fin n) K) := by
  change (g : GL (Fin n) K) ∈ (GeneralLinearGroup.scalar (Fin n)).range ↔ _
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc⟩
    have hdet : GeneralLinearGroup.det (g : GL (Fin n) K) = 1 :=
      Units.ext ((mem_statedSL_iff_det_eq_one K n _).mp g.property)
    rw [← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
    exact hdet
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

@[expose] def statedQuotient (n : ℕ) : StatedSL n K →* StatedProj (StatedSL n K) :=
  QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))

theorem coordinate_quotient_compatibility (n : ℕ) (g : SpecialLinearGroup (Fin n) K) :
    projectiveSpecialLinearGroupEquivStatedProj n K
        (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K)) g) =
      statedQuotient K n (specialLinearGroupEquivStatedSL n K g) := by
  exact QuotientGroup.congr_mk' _ _ _ _ g

theorem coordinate_quotient_comp (n : ℕ) :
    (projectiveSpecialLinearGroupEquivStatedProj n K).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K))) =
    (statedQuotient K n).comp (specialLinearGroupEquivStatedSL n K).toMonoidHom := by
  ext g
  exact coordinate_quotient_compatibility K n g

@[expose] noncomputable def statedMinusIdentity : StatedSL 2 K :=
  specialLinearGroupEquivStatedSL 2 K (minusIdentity K)

theorem statedMinusIdentity_matrix :
    ((statedMinusIdentity K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.scalar (Fin 2) (-1) := rfl

theorem statedScalarKernel_two_eq_zpowers :
    statedScalarKernel K 2 = Subgroup.zpowers (statedMinusIdentity K) := by
  rw [statedScalarKernel, ← map_center_eq_statedScalars,
    center_eq_zpowers_minusIdentity, MonoidHom.map_zpowers]
  rfl

theorem statedQuotient_surjective (n : ℕ) : Function.Surjective (statedQuotient K n) :=
  QuotientGroup.mk'_surjective _

theorem statedQuotient_two_ker :
    (statedQuotient K 2).ker = Subgroup.zpowers (statedMinusIdentity K) := by
  exact (QuotientGroup.ker_mk' _).trans (statedScalarKernel_two_eq_zpowers K)

theorem statedMinusIdentity_order (hK : ringChar K ≠ 2) :
    orderOf (statedMinusIdentity K) = 2 := by
  rw [statedMinusIdentity, (specialLinearGroupEquivStatedSL 2 K).orderOf_eq,
    minusIdentity_order K hK]

theorem statedMinusIdentity_mem_center :
    statedMinusIdentity K ∈ Subgroup.center (StatedSL 2 K) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  obtain ⟨a, rfl⟩ := (specialLinearGroupEquivStatedSL 2 K).surjective g
  simpa only [map_mul, statedMinusIdentity] using
    congrArg (specialLinearGroupEquivStatedSL 2 K)
      (Subgroup.mem_center_iff.mp (minusIdentity_mem_center K) a)

theorem statedScalarKernel_two_card (hK : ringChar K ≠ 2) :
    Nat.card (statedScalarKernel K 2) = 2 := by
  rw [statedScalarKernel_two_eq_zpowers, Nat.card_zpowers, statedMinusIdentity_order K hK]

theorem statedScalarKernel_eq_center (n : ℕ) :
    statedScalarKernel K n = Subgroup.center (StatedSL n K) := by
  rw [statedScalarKernel, ← map_center_eq_statedScalars]
  exact Subgroup.map_center_eq (specialLinearGroupEquivStatedSL n K)

theorem mem_statedScalarKernel_two_iff (g : StatedSL 2 K) :
    g ∈ statedScalarKernel K 2 ↔ g = 1 ∨ g = statedMinusIdentity K := by
  obtain ⟨a, rfl⟩ := (specialLinearGroupEquivStatedSL 2 K).surjective g
  have hm : specialLinearGroupEquivStatedSL 2 K a ∈ statedScalarKernel K 2 ↔
      a ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    rw [statedScalarKernel, ← map_center_eq_statedScalars]
    constructor
    · rintro ⟨b, hb, hba⟩
      exact (specialLinearGroupEquivStatedSL 2 K).injective hba ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  rw [hm, mem_center_iff_eq_one_or_minusIdentity]
  constructor
  · rintro (rfl | rfl)
    · left
      exact map_one _
    · right
      rfl
  · rintro (h | h)
    · left
      apply (specialLinearGroupEquivStatedSL 2 K).injective
      exact h.trans (map_one _).symm
    · right
      exact (specialLinearGroupEquivStatedSL 2 K).injective h

theorem statedQuotient_two_eq_one_iff (g : StatedSL 2 K) :
    statedQuotient K 2 g = 1 ↔ g = 1 ∨ g = statedMinusIdentity K := by
  exact (QuotientGroup.eq_one_iff g).trans (mem_statedScalarKernel_two_iff K g)

theorem statedMinusIdentity_GL :
    (statedMinusIdentity K : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) (-1 : Kˣ) :=
  Units.ext rfl

@[expose] noncomputable def scalarProjectiveEquivStated (n : ℕ) :
    NativeScalarProjective K n ≃* StatedProj (StatedSL n K) :=
  (scalarProjectiveEquivNative K n).trans (projectiveSpecialLinearGroupEquivStatedProj n K)

theorem scalarProjectiveEquivStated_mk (n : ℕ) (g : SpecialLinearGroup (Fin n) K) :
    scalarProjectiveEquivStated K n (scalarQuotient K n g) =
      statedQuotient K n (specialLinearGroupEquivStatedSL n K g) := by
  exact coordinate_quotient_compatibility K n g

end StatedScalarQuotient

section OriginalProjectionTransport

variable (K : Type) [Field K] {E : Type u} [Group E]

@[expose] noncomputable def projectionToNative
    (pi : E →* StatedProj (StatedSL 2 K)) :
    E →* ProjectiveSpecialLinearGroup (Fin 2) K :=
  (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.toMonoidHom.comp pi

theorem projectionToNative_surjective
    (pi : E →* StatedProj (StatedSL 2 K)) (hpi : Function.Surjective pi) :
    Function.Surjective (projectionToNative K pi) :=
  (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.surjective.comp hpi

theorem projectionToNative_ker (pi : E →* StatedProj (StatedSL 2 K)) :
    (projectionToNative K pi).ker = pi.ker :=
  MonoidHom.ker_mulEquiv_comp pi (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm

theorem original_projection_compatibility_iff
    (pi : E →* StatedProj (StatedSL 2 K)) (g : SpecialLinearGroup (Fin 2) K) (x : E) :
    nativeQuotient K g = projectionToNative K pi x ↔
      statedQuotient K 2 (specialLinearGroupEquivStatedSL 2 K g) = pi x := by
  constructor
  · intro h
    have hc := congrArg (projectiveSpecialLinearGroupEquivStatedProj 2 K) h
    simpa only [nativeQuotient, projectionToNative, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      coordinate_quotient_compatibility] using hc
  · intro h
    apply (projectiveSpecialLinearGroupEquivStatedProj 2 K).injective
    simpa only [nativeQuotient, projectionToNative, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      coordinate_quotient_compatibility] using h

theorem original_projection_comp_compatibility_iff
    (pi : E →* StatedProj (StatedSL 2 K)) (e : E ≃* SpecialLinearGroup (Fin 2) K) :
    (nativeQuotient K).comp e.toMonoidHom = projectionToNative K pi ↔
    (statedQuotient K 2).comp (e.trans (specialLinearGroupEquivStatedSL 2 K)).toMonoidHom =
      pi := by
  rw [MonoidHom.ext_iff, MonoidHom.ext_iff]
  exact forall_congr' (fun x => original_projection_compatibility_iff K pi (e x) x)

end OriginalProjectionTransport

section OriginalScalarProjectionTransport

variable (F : Type u) [Field F] {E : Type v} [Group E]

@[expose] def scalarProjectionToNative (pi : E →* NativeScalarProjective F 2) :
    E →* ProjectiveSpecialLinearGroup (Fin 2) F :=
  (scalarProjectiveEquivNative F 2).toMonoidHom.comp pi

theorem scalarProjectionToNative_surjective
    (pi : E →* NativeScalarProjective F 2) (hpi : Function.Surjective pi) :
    Function.Surjective (scalarProjectionToNative F pi) :=
  (scalarProjectiveEquivNative F 2).surjective.comp hpi

theorem scalarProjectionToNative_ker (pi : E →* NativeScalarProjective F 2) :
    (scalarProjectionToNative F pi).ker = pi.ker :=
  MonoidHom.ker_mulEquiv_comp pi (scalarProjectiveEquivNative F 2)

theorem original_scalar_projection_compatibility_iff
    (pi : E →* NativeScalarProjective F 2) (g : SpecialLinearGroup (Fin 2) F) (x : E) :
    nativeQuotient F g = scalarProjectionToNative F pi x ↔ scalarQuotient F 2 g = pi x := by
  change scalarProjectiveEquivNative F 2 (scalarQuotient F 2 g) =
      scalarProjectiveEquivNative F 2 (pi x) ↔ _
  exact (scalarProjectiveEquivNative F 2).injective.eq_iff

theorem original_scalar_projection_comp_compatibility_iff
    (pi : E →* NativeScalarProjective F 2) (e : E ≃* SpecialLinearGroup (Fin 2) F) :
    (nativeQuotient F).comp e.toMonoidHom = scalarProjectionToNative F pi ↔
    (scalarQuotient F 2).comp e.toMonoidHom = pi := by
  rw [MonoidHom.ext_iff, MonoidHom.ext_iff]
  exact forall_congr' (fun x => original_scalar_projection_compatibility_iff F pi (e x) x)

end OriginalScalarProjectionTransport

section OriginalCoverCardinality

variable (F : Type u) [Field F] {E : Type v} [Group E]

theorem original_cover_card_eq_nativeSL
    (hF : ringChar F ≠ 2) (z : E) (hz : orderOf z = 2)
    (pi : E →* ProjectiveSpecialLinearGroup (Fin 2) F) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z) :
    Nat.card E = Nat.card (SpecialLinearGroup (Fin 2) F) := by
  have hcard : Nat.card pi.ker = 2 := by rw [hker, Nat.card_zpowers, hz]
  have hnative : Nat.card (nativeQuotient F).ker = 2 := by
    rw [nativeQuotient_ker, Nat.card_zpowers, minusIdentity_order F hF]
  have h := Subgroup.card_ker_mul_card_of_surjective hpi
  have h' := Subgroup.card_ker_mul_card_of_surjective (nativeQuotient_surjective F)
  rw [hcard] at h
  rw [hnative] at h'
  exact h.symm.trans h'

end OriginalCoverCardinality

section FiniteOddField

variable (F : Type u) [Field F] [Finite F]

theorem odd_card_of_odd_characteristic (hF : ringChar F ≠ 2) : Odd (Nat.card F) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact FiniteField.odd_card_of_char_ne_two hF

theorem three_le_card_of_odd_characteristic (hF : ringChar F ≠ 2) : 3 ≤ Nat.card F := by
  have hodd := (Nat.odd_iff.mp (odd_card_of_odd_characteristic F hF))
  have hnontrivial : 1 < Nat.card F := Finite.one_lt_card
  omega

end FiniteOddField

section SuppliedQuaternionSylow

variable {E : Type u} [Group E]

theorem supplied_quaternion_sylow_card (S : Sylow 2 E) (n : ℕ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n - 2))) : Nat.card S = 2 ^ n :=
  (Nat.card_congr e.toEquiv).trans
    (QuaternionDoubleCoverUniqueness.quaternion_natCard n hn)

theorem supplied_quaternion_sylow_parameter [Finite E] (S : Sylow 2 E) (n : ℕ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n - 2))) : (Nat.card E).factorization 2 = n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  exact (Sylow.card_eq_multiplicity S).symm.trans (supplied_quaternion_sylow_card S n hn e)

theorem supplied_quaternion_sylow_parameter_int [Finite E] (S : Sylow 2 E) (n : ℤ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n.toNat - 2))) :
    ((Nat.card E).factorization 2 : ℤ) = n := by
  rw [supplied_quaternion_sylow_parameter S n.toNat (by omega) e,
    Int.toNat_of_nonneg (by omega)]

theorem integer_quaternion_exponent (n : ℤ) : (n - 2).toNat = n.toNat - 2 := by
  omega

end SuppliedQuaternionSylow

section NativeCover

variable (F : Type u) [Field F] [Finite F] {E : Type v} [Group E] [Finite E]

theorem quaternion_central_double_cover_native
    (hF : ringChar F ≠ 2) (z : E) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center E)
    (pi : E →* ProjectiveSpecialLinearGroup (Fin 2) F) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (S : Sylow 2 E) (n : ℕ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n - 2))) :
    ∃ iso : E ≃* SpecialLinearGroup (Fin 2) F,
      (nativeQuotient F).comp iso.toMonoidHom = pi ∧ iso z = minusIdentity F := by
  let P : Sylow 2 (SpecialLinearGroup (Fin 2) F) := Classical.choice inferInstance
  obtain ⟨m, hm, ⟨f⟩⟩ := OddFieldSL2.sylow_two_quaternion F
    (odd_card_of_odd_characteristic F hF) P
  obtain ⟨_, iso, hpiiso, hziso⟩ :=
    QuaternionDoubleCoverUniqueness.quaternion_sylow_central_double_cover_uniqueness
      z hz hc pi hpi hker S n hn e
      (minusIdentity F) (minusIdentity_order F hF) (minusIdentity_mem_center F)
      (nativeQuotient F) (nativeQuotient_surjective F) (nativeQuotient_ker F)
      P m hm f
  exact ⟨iso, MonoidHom.ext hpiiso, hziso⟩

theorem quaternion_central_double_cover_native_int
    (hF : ringChar F ≠ 2) (z : E) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center E)
    (pi : E →* ProjectiveSpecialLinearGroup (Fin 2) F) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (S : Sylow 2 E) (n : ℤ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n - 2).toNat)) :
    ∃ iso : E ≃* SpecialLinearGroup (Fin 2) F,
      (nativeQuotient F).comp iso.toMonoidHom = pi ∧ iso z = minusIdentity F :=
  quaternion_central_double_cover_native F hF z hz hc pi hpi hker S n.toNat (by omega)
    (by rw [← integer_quaternion_exponent n]; exact e)

theorem quaternion_central_double_cover_scalar
    (hF : ringChar F ≠ 2) (z : E) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center E)
    (pi : E →* NativeScalarProjective F 2) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (S : Sylow 2 E) (n : ℕ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n - 2))) :
    ∃ iso : E ≃* SpecialLinearGroup (Fin 2) F,
      (scalarQuotient F 2).comp iso.toMonoidHom = pi ∧ iso z = minusIdentity F := by
  obtain ⟨iso, hpiiso, hziso⟩ := quaternion_central_double_cover_native F hF z hz hc
    (scalarProjectionToNative F pi) (scalarProjectionToNative_surjective F pi hpi)
    ((scalarProjectionToNative_ker F pi).trans hker) S n hn e
  exact ⟨iso, (original_scalar_projection_comp_compatibility_iff F pi iso).mp hpiiso,
    hziso⟩

theorem quaternion_central_double_cover_scalar_int
    (hF : ringChar F ≠ 2) (z : E) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center E)
    (pi : E →* NativeScalarProjective F 2) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (S : Sylow 2 E) (n : ℤ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n - 2).toNat)) :
    ∃ iso : E ≃* SpecialLinearGroup (Fin 2) F,
      (scalarQuotient F 2).comp iso.toMonoidHom = pi ∧ iso z = minusIdentity F :=
  quaternion_central_double_cover_scalar F hF z hz hc pi hpi hker S n.toNat (by omega)
    (by rw [← integer_quaternion_exponent n]; exact e)

end NativeCover

section StatedCover

variable (K : Type) [Field K] [Finite K] {E : Type u} [Group E] [Finite E]

theorem quaternion_central_double_cover_stated
    (hK : ringChar K ≠ 2) (z : E) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center E)
    (pi : E →* StatedProj (StatedSL 2 K)) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (S : Sylow 2 E) (n : ℕ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n - 2))) :
    ∃ iso : E ≃* StatedSL 2 K,
      (statedQuotient K 2).comp iso.toMonoidHom = pi ∧ iso z = statedMinusIdentity K := by
  obtain ⟨iso, hpiiso, hziso⟩ := quaternion_central_double_cover_native K hK z hz hc
    (projectionToNative K pi) (projectionToNative_surjective K pi hpi)
    ((projectionToNative_ker K pi).trans hker) S n hn e
  refine ⟨iso.trans (specialLinearGroupEquivStatedSL 2 K),
    (original_projection_comp_compatibility_iff K pi iso).mp hpiiso, ?_⟩
  change specialLinearGroupEquivStatedSL 2 K (iso z) = statedMinusIdentity K
  rw [hziso]
  rfl

theorem quaternion_central_double_cover_stated_int
    (hK : ringChar K ≠ 2) (z : E) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center E)
    (pi : E →* StatedProj (StatedSL 2 K)) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (S : Sylow 2 E) (n : ℤ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n - 2).toNat)) :
    ∃ iso : E ≃* StatedSL 2 K,
      (statedQuotient K 2).comp iso.toMonoidHom = pi ∧ iso z = statedMinusIdentity K :=
  quaternion_central_double_cover_stated K hK z hz hc pi hpi hker S n.toNat (by omega)
    (by rw [← integer_quaternion_exponent n]; exact e)

end StatedCover

end CFSG.Semidihedral.ProjectiveSL2Cover
