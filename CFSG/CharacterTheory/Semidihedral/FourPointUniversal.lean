module

public import CFSG.CharacterTheory.Semidihedral.FourPointPresentation
public import CFSG.CharacterTheory.Semidihedral.FourPointMatrices
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Semidihedral.FourPointUniversal

open Matrix
open FourPointPresentation

@[expose] def letter (i : Fin 4) : FreeGroup (Fin 4) := FreeGroup.of i

@[expose] def rels : Set (FreeGroup (Fin 4)) :=
  {letter 0 ^ 2, letter 1 ^ 2, letter 2 ^ 2, letter 3 ^ 2,
    letter 3 * letter 0 * (letter 0 * letter 3)⁻¹,
    letter 3 * letter 1 * (letter 1 * letter 3)⁻¹,
    letter 3 * letter 2 * (letter 2 * letter 3)⁻¹,
    (letter 0 * letter 1) ^ 3, (letter 1 * letter 2) ^ 3,
    (letter 0 * letter 2) ^ 2 * (letter 3)⁻¹}

abbrev P := PresentedGroup rels

@[expose] def alpha : P := PresentedGroup.of 0
@[expose] def beta : P := PresentedGroup.of 1
@[expose] def gamma : P := PresentedGroup.of 2
@[expose] def zeta : P := PresentedGroup.of 3

theorem alpha_sq : alpha ^ 2 = 1 := by
  change (PresentedGroup.mk rels) (letter 0) ^ 2 = 1
  rw [← _root_.map_pow]
  exact PresentedGroup.one_of_mem (by simp [rels])

theorem beta_sq : beta ^ 2 = 1 := by
  change (PresentedGroup.mk rels) (letter 1) ^ 2 = 1
  rw [← _root_.map_pow]
  exact PresentedGroup.one_of_mem (by simp [rels])

theorem gamma_sq : gamma ^ 2 = 1 := by
  change (PresentedGroup.mk rels) (letter 2) ^ 2 = 1
  rw [← _root_.map_pow]
  exact PresentedGroup.one_of_mem (by simp [rels])

theorem zeta_sq : zeta ^ 2 = 1 := by
  change (PresentedGroup.mk rels) (letter 3) ^ 2 = 1
  rw [← _root_.map_pow]
  exact PresentedGroup.one_of_mem (by simp [rels])

theorem zeta_alpha : zeta * alpha = alpha * zeta := by
  have h := PresentedGroup.one_of_mem (rels := rels)
    (x := letter 3 * letter 0 * (letter 0 * letter 3)⁻¹) (by simp [rels])
  apply eq_of_mul_inv_eq_one
  simpa only [_root_.map_mul, _root_.map_inv, letter, alpha, zeta, PresentedGroup.of] using h

theorem zeta_beta : zeta * beta = beta * zeta := by
  have h := PresentedGroup.one_of_mem (rels := rels)
    (x := letter 3 * letter 1 * (letter 1 * letter 3)⁻¹) (by simp [rels])
  apply eq_of_mul_inv_eq_one
  simpa only [_root_.map_mul, _root_.map_inv, letter, beta, zeta, PresentedGroup.of] using h

theorem zeta_gamma : zeta * gamma = gamma * zeta := by
  have h := PresentedGroup.one_of_mem (rels := rels)
    (x := letter 3 * letter 2 * (letter 2 * letter 3)⁻¹) (by simp [rels])
  apply eq_of_mul_inv_eq_one
  simpa only [_root_.map_mul, _root_.map_inv, letter, gamma, zeta, PresentedGroup.of] using h

theorem alpha_beta_cube : (alpha * beta) ^ 3 = 1 := by
  change ((PresentedGroup.mk rels) (letter 0) * (PresentedGroup.mk rels) (letter 1)) ^ 3 = 1
  rw [← _root_.map_mul, ← _root_.map_pow]
  exact PresentedGroup.one_of_mem (by simp [rels])

theorem beta_gamma_cube : (beta * gamma) ^ 3 = 1 := by
  change ((PresentedGroup.mk rels) (letter 1) * (PresentedGroup.mk rels) (letter 2)) ^ 3 = 1
  rw [← _root_.map_mul, ← _root_.map_pow]
  exact PresentedGroup.one_of_mem (by simp [rels])

theorem alpha_gamma_sq : (alpha * gamma) ^ 2 = zeta := by
  have h := PresentedGroup.one_of_mem (rels := rels)
    (x := (letter 0 * letter 2) ^ 2 * (letter 3)⁻¹) (by simp [rels])
  apply eq_of_mul_inv_eq_one
  simpa only [_root_.map_pow, _root_.map_mul, _root_.map_inv, letter, alpha, gamma, zeta,
    PresentedGroup.of] using h

theorem generators_closure : Subgroup.closure ({alpha, beta, gamma, zeta} : Set P) = ⊤ := by
  apply top_unique
  intro x _
  apply PresentedGroup.generated_by rels
  intro i
  fin_cases i <;> exact Subgroup.subset_closure (by simp [alpha, beta, gamma, zeta])

theorem zeta_mem_center : zeta ∈ Subgroup.center P := by
  have hle : Subgroup.closure ({alpha, beta, gamma, zeta} : Set P) ≤
      Subgroup.centralizer {zeta} := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rcases hx with rfl | rfl | rfl | rfl
    · exact zeta_alpha.symm
    · exact zeta_beta.symm
    · exact zeta_gamma.symm
    · rfl
  apply Subgroup.mem_center_iff.mpr
  intro x
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (hle (by rw [generators_closure]; exact Subgroup.mem_top x))

theorem original_relations : Relations alpha beta gamma zeta :=
  ⟨zeta_mem_center, alpha_sq, beta_sq, gamma_sq, zeta_sq,
    alpha_beta_cube, beta_gamma_cube, alpha_gamma_sq⟩

variable {H : Type*} [Group H]

@[expose] def generatorAssignment (a b c z : H) (i : Fin 4) : H :=
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => z

theorem lift_rels {a b c z : H} (h : Relations a b c z) :
    ∀ r ∈ rels, FreeGroup.lift (generatorAssignment a b c z) r = 1 := by
  intro r hr
  simp only [rels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [_root_.map_pow, _root_.map_mul, _root_.map_inv, letter,
    FreeGroup.lift_apply_of,
    generatorAssignment]
  · exact h.a_sq
  · exact h.b_sq
  · exact h.c_sq
  · exact h.z_sq
  · change (z * a) * (a * z)⁻¹ = 1
    rw [← Subgroup.mem_center_iff.mp h.central a, mul_inv_cancel]
  · change (z * b) * (b * z)⁻¹ = 1
    rw [← Subgroup.mem_center_iff.mp h.central b, mul_inv_cancel]
  · change (z * c) * (c * z)⁻¹ = 1
    rw [← Subgroup.mem_center_iff.mp h.central c, mul_inv_cancel]
  · exact h.ab_cube
  · exact h.bc_cube
  · change (a * c) ^ 2 * z⁻¹ = 1
    rw [h.ac_sq, mul_inv_cancel]

@[expose] def toGroup {a b c z : H} (h : Relations a b c z) : P →* H :=
  PresentedGroup.toGroup (lift_rels h)

@[simp] theorem toGroup_alpha {a b c z : H} (h : Relations a b c z) :
    toGroup h alpha = a := PresentedGroup.toGroup.of (lift_rels h)

@[simp] theorem toGroup_beta {a b c z : H} (h : Relations a b c z) :
    toGroup h beta = b := PresentedGroup.toGroup.of (lift_rels h)

@[simp] theorem toGroup_gamma {a b c z : H} (h : Relations a b c z) :
    toGroup h gamma = c := PresentedGroup.toGroup.of (lift_rels h)

@[simp] theorem toGroup_zeta {a b c z : H} (h : Relations a b c z) :
    toGroup h zeta = z := PresentedGroup.toGroup.of (lift_rels h)

theorem toGroup_surjective {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) :
    Function.Surjective (toGroup h) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨alpha, toGroup_alpha h⟩
  · exact ⟨beta, toGroup_beta h⟩
  · exact ⟨gamma, toGroup_gamma h⟩
  · exact ⟨zeta, toGroup_zeta h⟩

theorem matrix_relations : Relations FourPointMatrices.A FourPointMatrices.B
    FourPointMatrices.C FourPointMatrices.Z :=
  ⟨FourPointMatrices.Z_mem_center, FourPointMatrices.A_square,
    FourPointMatrices.B_square, FourPointMatrices.C_square, FourPointMatrices.Z_square,
    FourPointMatrices.AB_cube, FourPointMatrices.BC_cube, FourPointMatrices.AC_square⟩

theorem matrix_generators_closure :
    Subgroup.closure ({FourPointMatrices.A, FourPointMatrices.B,
      FourPointMatrices.C, FourPointMatrices.Z} :
        Set (GeneralLinearGroup (Fin 2) (ZMod 3))) = ⊤ := by
  apply top_unique
  rw [← FourPointMatrices.generators_closure]
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

@[expose] def toMatrices : P →* GeneralLinearGroup (Fin 2) (ZMod 3) :=
  toGroup matrix_relations

@[simp] theorem toMatrices_alpha : toMatrices alpha = FourPointMatrices.A :=
  toGroup_alpha matrix_relations

@[simp] theorem toMatrices_beta : toMatrices beta = FourPointMatrices.B :=
  toGroup_beta matrix_relations

@[simp] theorem toMatrices_gamma : toMatrices gamma = FourPointMatrices.C :=
  toGroup_gamma matrix_relations

@[simp] theorem toMatrices_zeta : toMatrices zeta = FourPointMatrices.Z :=
  toGroup_zeta matrix_relations

theorem toMatrices_surjective : Function.Surjective toMatrices :=
  toGroup_surjective matrix_relations matrix_generators_closure

theorem presentation_finite_card_bijective :
    Finite P ∧ Nat.card P = 48 ∧ Function.Bijective toMatrices :=
  finite_card_eq_48_of_surjective original_relations generators_closure
    toMatrices toMatrices_surjective FourPointMatrices.GL2_three_card

instance presentation_finite : Finite P := presentation_finite_card_bijective.1

theorem presentation_card : Nat.card P = 48 := presentation_finite_card_bijective.2.1

@[expose] noncomputable def presentationEquivMatrices :
    P ≃* GeneralLinearGroup (Fin 2) (ZMod 3) :=
  MulEquiv.ofBijective toMatrices presentation_finite_card_bijective.2.2

@[simp] theorem presentationEquivMatrices_alpha :
    presentationEquivMatrices alpha = FourPointMatrices.A := toMatrices_alpha

@[simp] theorem presentationEquivMatrices_beta :
    presentationEquivMatrices beta = FourPointMatrices.B := toMatrices_beta

@[simp] theorem presentationEquivMatrices_gamma :
    presentationEquivMatrices gamma = FourPointMatrices.C := toMatrices_gamma

@[simp] theorem presentationEquivMatrices_zeta :
    presentationEquivMatrices zeta = FourPointMatrices.Z := toMatrices_zeta

theorem toGroup_bijective_of_card48 {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    Function.Bijective (toGroup h) :=
  (finite_card_eq_48_of_surjective original_relations generators_closure
    (toGroup h) (toGroup_surjective h hgen) hcard).2.2

@[expose] noncomputable def presentationEquivGroup {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    P ≃* H :=
  MulEquiv.ofBijective (toGroup h) (toGroup_bijective_of_card48 h hgen hcard)

@[simp] theorem presentationEquivGroup_alpha {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    presentationEquivGroup h hgen hcard alpha = a := toGroup_alpha h

@[simp] theorem presentationEquivGroup_beta {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    presentationEquivGroup h hgen hcard beta = b := toGroup_beta h

@[simp] theorem presentationEquivGroup_gamma {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    presentationEquivGroup h hgen hcard gamma = c := toGroup_gamma h

@[simp] theorem presentationEquivGroup_zeta {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    presentationEquivGroup h hgen hcard zeta = z := toGroup_zeta h

@[expose] noncomputable def realizationEquivMatrices {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    H ≃* GeneralLinearGroup (Fin 2) (ZMod 3) :=
  (presentationEquivGroup h hgen hcard).symm.trans presentationEquivMatrices

theorem realizationEquivMatrices_apply_toGroup {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) (x : P) :
    realizationEquivMatrices h hgen hcard (toGroup h x) = toMatrices x := by
  change presentationEquivMatrices
    ((presentationEquivGroup h hgen hcard).symm
      (presentationEquivGroup h hgen hcard x)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

@[simp] theorem realizationEquivMatrices_a {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    realizationEquivMatrices h hgen hcard a = FourPointMatrices.A := by
  simpa only [toGroup_alpha, toMatrices_alpha] using
    realizationEquivMatrices_apply_toGroup h hgen hcard alpha

@[simp] theorem realizationEquivMatrices_b {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    realizationEquivMatrices h hgen hcard b = FourPointMatrices.B := by
  simpa only [toGroup_beta, toMatrices_beta] using
    realizationEquivMatrices_apply_toGroup h hgen hcard beta

@[simp] theorem realizationEquivMatrices_c {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    realizationEquivMatrices h hgen hcard c = FourPointMatrices.C := by
  simpa only [toGroup_gamma, toMatrices_gamma] using
    realizationEquivMatrices_apply_toGroup h hgen hcard gamma

@[simp] theorem realizationEquivMatrices_z {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    realizationEquivMatrices h hgen hcard z = FourPointMatrices.Z := by
  simpa only [toGroup_zeta, toMatrices_zeta] using
    realizationEquivMatrices_apply_toGroup h hgen hcard zeta

theorem exists_matrix_equiv {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48) :
    ∃ theta : H ≃* GeneralLinearGroup (Fin 2) (ZMod 3),
      theta a = FourPointMatrices.A ∧ theta b = FourPointMatrices.B ∧
      theta c = FourPointMatrices.C ∧ theta z = FourPointMatrices.Z :=
  ⟨realizationEquivMatrices h hgen hcard, realizationEquivMatrices_a h hgen hcard,
    realizationEquivMatrices_b h hgen hcard, realizationEquivMatrices_c h hgen hcard,
    realizationEquivMatrices_z h hgen hcard⟩

@[expose] def signToFieldUnits : ℤˣ →* (ZMod 3)ˣ :=
  Units.map (Int.castRingHom (ZMod 3)).toMonoidHom

@[simp] theorem signToFieldUnits_neg_one : signToFieldUnits (-1) = -1 := by
  apply Units.ext
  change ((-1 : ℤ) : ZMod 3) = -1
  simp

theorem signToFieldUnits_injective : Function.Injective signToFieldUnits := by
  intro u v huv
  have hne : (1 : (ZMod 3)ˣ) ≠ -1 := by
    intro heq
    have hval := congrArg Units.val heq
    have hfield : (1 : ZMod 3) ≠ -1 := by decide
    exact hfield hval
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl
  · rfl
  · exact False.elim (hne (by simpa only [map_one, signToFieldUnits_neg_one] using huv))
  · exact False.elim (hne (by simpa only [map_one, signToFieldUnits_neg_one] using huv.symm))
  · rfl

theorem signToFieldUnits_eq_one_iff (u : ℤˣ) : signToFieldUnits u = 1 ↔ u = 1 := by
  constructor
  · intro h
    apply signToFieldUnits_injective
    simpa only [map_one] using h
  · rintro rfl
    exact map_one signToFieldUnits

theorem matrixZ_det : GeneralLinearGroup.det FourPointMatrices.Z = 1 := by
  apply Units.ext
  change FourPointMatrices.matrixZ.det = 1
  decide

theorem determinant_character_eq {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48)
    (pi : H →* Equiv.Perm (Fin 4))
    (ha : pi a = Equiv.swap 0 1) (hb : pi b = Equiv.swap 1 2)
    (hc : pi c = Equiv.swap 2 3) (hz : pi z = 1) :
    GeneralLinearGroup.det.comp (realizationEquivMatrices h hgen hcard).toMonoidHom =
      signToFieldUnits.comp (Equiv.Perm.sign.comp pi) := by
  apply MonoidHom.eq_of_eqOn_dense hgen
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  change GeneralLinearGroup.det (realizationEquivMatrices h hgen hcard x) =
    signToFieldUnits (Equiv.Perm.sign (pi x))
  rcases hx with rfl | rfl | rfl | rfl
  · rw [realizationEquivMatrices_a h hgen hcard, FourPointMatrices.A_det, ha,
      Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 1 by decide), signToFieldUnits_neg_one]
  · rw [realizationEquivMatrices_b h hgen hcard, FourPointMatrices.B_det, hb,
      Equiv.Perm.sign_swap (show (1 : Fin 4) ≠ 2 by decide), signToFieldUnits_neg_one]
  · rw [realizationEquivMatrices_c h hgen hcard, FourPointMatrices.C_det, hc,
      Equiv.Perm.sign_swap (show (2 : Fin 4) ≠ 3 by decide), signToFieldUnits_neg_one]
  · rw [realizationEquivMatrices_z h hgen hcard, matrixZ_det, hz, map_one, map_one]

theorem determinant_eq_sign {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48)
    (pi : H →* Equiv.Perm (Fin 4))
    (ha : pi a = Equiv.swap 0 1) (hb : pi b = Equiv.swap 1 2)
    (hc : pi c = Equiv.swap 2 3) (hz : pi z = 1) (x : H) :
    GeneralLinearGroup.det (realizationEquivMatrices h hgen hcard x) =
      signToFieldUnits (Equiv.Perm.sign (pi x)) :=
  DFunLike.congr_fun (determinant_character_eq h hgen hcard pi ha hb hc hz) x

theorem determinant_one_iff_alternating {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48)
    (pi : H →* Equiv.Perm (Fin 4))
    (ha : pi a = Equiv.swap 0 1) (hb : pi b = Equiv.swap 1 2)
    (hc : pi c = Equiv.swap 2 3) (hz : pi z = 1) (x : H) :
    (GeneralLinearGroup.det (realizationEquivMatrices h hgen hcard x) : ZMod 3) = 1 ↔
      pi x ∈ alternatingGroup (Fin 4) := by
  rw [Units.val_eq_one, determinant_eq_sign h hgen hcard pi ha hb hc hz x,
    signToFieldUnits_eq_one_iff, Equiv.Perm.mem_alternatingGroup]

@[expose] def determinantOne : Subgroup (GeneralLinearGroup (Fin 2) (ZMod 3)) :=
  GeneralLinearGroup.det.ker

@[simp] theorem mem_determinantOne (g : GeneralLinearGroup (Fin 2) (ZMod 3)) :
    g ∈ determinantOne ↔ (GeneralLinearGroup.det g : ZMod 3) = 1 := by
  change GeneralLinearGroup.det g = 1 ↔ (GeneralLinearGroup.det g : ZMod 3) = 1
  exact Units.val_eq_one.symm

@[expose] def alternatingPreimage (pi : H →* Equiv.Perm (Fin 4)) : Subgroup H :=
  (alternatingGroup (Fin 4)).comap pi

theorem alternatingPreimage_map {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48)
    (pi : H →* Equiv.Perm (Fin 4))
    (ha : pi a = Equiv.swap 0 1) (hb : pi b = Equiv.swap 1 2)
    (hc : pi c = Equiv.swap 2 3) (hz : pi z = 1) :
    (alternatingPreimage pi).map (realizationEquivMatrices h hgen hcard).toMonoidHom =
      determinantOne := by
  ext g
  rw [Subgroup.mem_map, mem_determinantOne]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (determinant_one_iff_alternating h hgen hcard pi ha hb hc hz x).mpr hx
  · intro hg
    obtain ⟨x, rfl⟩ := (realizationEquivMatrices h hgen hcard).surjective g
    exact ⟨x, (determinant_one_iff_alternating h hgen hcard pi ha hb hc hz x).mp hg, rfl⟩

@[expose] noncomputable def alternatingEquivDeterminantOne {a b c z : H}
    (h : Relations a b c z) (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤)
    (hcard : Nat.card H = 48) (pi : H →* Equiv.Perm (Fin 4))
    (ha : pi a = Equiv.swap 0 1) (hb : pi b = Equiv.swap 1 2)
    (hc : pi c = Equiv.swap 2 3) (hz : pi z = 1) :
    alternatingPreimage pi ≃* determinantOne :=
  ((realizationEquivMatrices h hgen hcard).subgroupMap (alternatingPreimage pi)).trans
    (MulEquiv.subgroupCongr (alternatingPreimage_map h hgen hcard pi ha hb hc hz))

theorem alternatingEquivDeterminantOne_apply {a b c z : H}
    (h : Relations a b c z) (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤)
    (hcard : Nat.card H = 48) (pi : H →* Equiv.Perm (Fin 4))
    (ha : pi a = Equiv.swap 0 1) (hb : pi b = Equiv.swap 1 2)
    (hc : pi c = Equiv.swap 2 3) (hz : pi z = 1) (x : alternatingPreimage pi) :
    (alternatingEquivDeterminantOne h hgen hcard pi ha hb hc hz x :
      GeneralLinearGroup (Fin 2) (ZMod 3)) = realizationEquivMatrices h hgen hcard x :=
  rfl

theorem exists_matrix_equiv_with_alternating {a b c z : H} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set H) = ⊤) (hcard : Nat.card H = 48)
    (pi : H →* Equiv.Perm (Fin 4))
    (ha : pi a = Equiv.swap 0 1) (hb : pi b = Equiv.swap 1 2)
    (hc : pi c = Equiv.swap 2 3) (hz : pi z = 1) :
    ∃ theta : H ≃* GeneralLinearGroup (Fin 2) (ZMod 3),
      theta a = FourPointMatrices.A ∧ theta b = FourPointMatrices.B ∧
      theta c = FourPointMatrices.C ∧ theta z = FourPointMatrices.Z ∧
      (∀ x : H, (GeneralLinearGroup.det (theta x) : ZMod 3) = 1 ↔
        pi x ∈ alternatingGroup (Fin 4)) ∧
      (alternatingPreimage pi).map theta.toMonoidHom = determinantOne ∧
      ∃ e : alternatingPreimage pi ≃* determinantOne,
        ∀ x, (e x : GeneralLinearGroup (Fin 2) (ZMod 3)) = theta x :=
  ⟨realizationEquivMatrices h hgen hcard, realizationEquivMatrices_a h hgen hcard,
    realizationEquivMatrices_b h hgen hcard, realizationEquivMatrices_c h hgen hcard,
    realizationEquivMatrices_z h hgen hcard,
    determinant_one_iff_alternating h hgen hcard pi ha hb hc hz,
    alternatingPreimage_map h hgen hcard pi ha hb hc hz,
    alternatingEquivDeterminantOne h hgen hcard pi ha hb hc hz,
    alternatingEquivDeterminantOne_apply h hgen hcard pi ha hb hc hz⟩

end CFSG.Semidihedral.FourPointUniversal
