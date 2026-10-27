module

public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ThreeCharacterTable
public import CFSG.CharacterTheory.Wreathed.SelfcentralizingUniqueBlock

public section

namespace CFSG.Semidihedral.Principal

namespace GL2ThreeCharacters

open CFSG.Semidihedral.FourPointMatrices (normalUnit normalUnit_surjective)

@[expose] def InQuaternion (g : G23) : Prop :=
  g ^ 4 = 1 ∧ Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1

instance : DecidablePred InQuaternion := fun g => by
  unfold InQuaternion
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem inQuaternion_coord : ∀ i j : Coord,
    (InQuaternion (normalUnit i) → InQuaternion (normalUnit j) →
      InQuaternion (normalUnit i * normalUnit j)) ∧
    (InQuaternion (normalUnit i) → InQuaternion (normalUnit i)⁻¹) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem centralizer_inQuaternion_coord : ∀ i : Coord,
    (∀ j : Coord, InQuaternion (normalUnit j) →
      normalUnit j * normalUnit i = normalUnit i * normalUnit j) →
    InQuaternion (normalUnit i) := by
  decide

@[expose] def quaternionEight : Subgroup G23 where
  carrier := {g | InQuaternion g}
  one_mem' := by decide
  mul_mem' := by
    intro x y hx hy
    obtain ⟨i, rfl⟩ := normalUnit_surjective x
    obtain ⟨j, rfl⟩ := normalUnit_surjective y
    exact (inQuaternion_coord i j).1 hx hy
  inv_mem' := by
    intro x hx
    obtain ⟨i, rfl⟩ := normalUnit_surjective x
    exact (inQuaternion_coord i i).2 hx

theorem quaternionEight_normal : quaternionEight.Normal := by
  constructor
  intro g hg c
  obtain ⟨h4, hdet⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [conj_pow, h4, mul_one, mul_inv_cancel]
  · have hinv' : (c : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hc : Matrix.det (c : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        Matrix.det ((c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
      rw [← Matrix.det_mul, hinv', Matrix.det_one]
    simp only [Units.val_mul, Matrix.det_mul]
    rw [hdet]
    linear_combination hc

theorem quaternionEight_isPGroup : IsPGroup 2 quaternionEight := by
  intro g
  exact ⟨2, Subtype.ext g.2.1⟩

theorem centralizer_quaternionEight_le :
    Subgroup.centralizer (quaternionEight : Set G23) ≤ quaternionEight := by
  intro x hx
  obtain ⟨i, rfl⟩ := normalUnit_surjective x
  apply centralizer_inQuaternion_coord i
  intro j hj
  exact Subgroup.mem_centralizer_iff.mp hx (normalUnit j) hj

end GL2ThreeCharacters

open GL2ThreeCharacters CFSG.TwoRankLowerBound.Helpers in
theorem GL2_three_all_ordinary_characters_principal_two_block
    (basis : FiniteIrreducibleCharacterBasis (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (a p b : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (ha : orderOf a = 8)
    (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    let H := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)
    let z : H := -1
    let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)
    let ω : ℂ := ξ + ξ ^ 3
    let rep : Fin 8 → H := ![1, z, a ^ 2, p, z * p, b, a, a⁻¹]
    let table : Fin 8 → Fin 8 → ℂ := ![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, -1, -1, -1],
      ![2, 2, 2, -1, -1, 0, 0, 0], ![3, 3, -1, 0, 0, -1, 1, 1], ![3, 3, -1, 0, 0, 1, -1, -1],
      ![4, -4, 0, 1, -1, 0, 0, 0], ![2, -2, 0, -1, 1, 0, ω, -ω], ![2, -2, 0, -1, 1, 0, -ω, ω]]
    coefficientBlock basis (localizedComplexIntegerRing ideal) principal = Finset.univ ∧
    ∃ φ : Fin 8 → basis.index, Function.Bijective φ ∧
      (∀ i j, (basis.representation (φ i)).character (rep j) = table i j) ∧
      ∀ ℓ : basis.index,
        ℓ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
          ∃ i, φ i = ℓ := by
  intro H z ξ ω rep table
  have : quaternionEight.Normal := quaternionEight_normal
  have hblock := (CFSG.Wreathed.selfcentralizing_unique_block 2 quaternionEight
    quaternionEight_isPGroup centralizer_quaternionEight_le ideal basis).1 principal hprincipal
  obtain ⟨-, -, -, -, φ, hφ, -, hval, -⟩ :=
    GL2_three_ordinary_character_table_construction basis a p b ha hp hb hbz
  refine ⟨hblock, φ, hφ, hval, fun ℓ => ?_⟩
  rw [hblock]
  exact ⟨fun _ => hφ.2 ℓ, fun _ => Finset.mem_univ ℓ⟩

end CFSG.Semidihedral.Principal
