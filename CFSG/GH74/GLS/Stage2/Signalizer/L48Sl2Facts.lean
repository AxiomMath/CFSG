module

public import CFSG.GH74.GLS.IVK.L2.TorusCentralizer
public import CFSG.CharacterTheory.PSL2Table.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open CFSG.Semidihedral.OddFieldSL2 CFSG.Semidihedral.MatrixCoverData CFSG.Semidihedral CFSG.GH74.GLS.IVK.L2Torus
open Matrix Subgroup

variable {F : Type} [Field F]

theorem exists_inverting_sl2 [Finite F] (hodd : Odd (Nat.card F)) (a : SL F) (ha : a * a = minusIdentity F) :
    ∃ y : SL F, y * a * y⁻¹ = a⁻¹ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card F hodd
  obtain ⟨P, hP⟩ := exists_conj_J h2 a ha
  set Q : SL F := OddLinearNormals.quarterTurn F with hQ
  have hQinv : ((Q⁻¹ : SL F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
    rw [SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ, OddLinearNormals.quarterTurn]
  have hJ : J F 1 = SpecialLinearGroup.toGL (Q⁻¹) := by
    apply Units.ext
    have h1 : ((SpecialLinearGroup.toGL (Q⁻¹) : GL2 F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := hQinv
    rw [h1, J_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have ha' : a = slConjugation F P Q⁻¹ := by
    apply SpecialLinearGroup.toGL_injective
    rw [slConjugation_toGL, ← hJ]
    exact hP
  obtain ⟨u, v, huv⟩ := sum_two_squares F hodd (-1)
  refine ⟨slConjugation F P (secondGenerator F u v huv), ?_⟩
  have hgi := generators_inversion F u v huv
  have h1 : secondGenerator F u v huv * Q⁻¹ * (secondGenerator F u v huv)⁻¹ = Q := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hgi.symm
  calc slConjugation F P (secondGenerator F u v huv) * a * (slConjugation F P (secondGenerator F u v huv))⁻¹
      = slConjugation F P (secondGenerator F u v huv * Q⁻¹ * (secondGenerator F u v huv)⁻¹) := by
        rw [ha']; simp [map_mul, map_inv]
    _ = slConjugation F P Q := by rw [h1]
    _ = a⁻¹ := by rw [ha']; simp


open CFSG.PSL2Table CFSG.Assembly.LowTwoRank

theorem sl2_facts [Finite F] (hodd : Odd (Nat.card F)) {L : Type} [Group L] (e : L ≃* ↥(StatedSL 2 F)) :
    (∀ x : L, x * x = 1 → x ∈ center L) ∧ (∀ x ∈ center L, x * x = 1) ∧
      (∀ u ∈ center L, ∀ v ∈ center L, u ≠ 1 → v ≠ 1 → u = v) ∧
      ∀ a : L, a * a ∈ center L → a * a ≠ 1 → ∃ y : L, y * a * y⁻¹ = a⁻¹ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card F hodd
  let φ : L ≃* SL F := e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hc : ∀ x : L, x ∈ center L ↔ φ x ∈ center (SL F) := by
    intro x
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro h g
      obtain ⟨g', rfl⟩ := φ.surjective g
      rw [← map_mul, ← map_mul, h g']
    · intro h g
      apply φ.injective
      rw [map_mul, map_mul, h (φ g)]
  have hm1 : (-1 : SL F) ≠ 1 := neg_one_ne_one_SL h2
  have hcen : ∀ x : L, x ∈ center L ↔ φ x = 1 ∨ φ x = -1 := fun x => by
    rw [hc, mem_center_SL_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hcen]
    have hinv : (φ x)⁻¹ = φ x := by
      rw [inv_eq_iff_mul_eq_one, ← map_mul, hx, map_one]
    rcases eq_one_or_minusIdentity_of_inv_eq_self F h2 (φ x) hinv with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro x hx
    rw [hcen] at hx
    apply φ.injective
    rw [map_mul, map_one]
    rcases hx with h | h
    · rw [h, one_mul]
    · rw [h]
      simp
  · intro u hu v hv hu1 hv1
    rw [hcen] at hu hv
    apply φ.injective
    have hu1' : φ u ≠ 1 := fun h => hu1 (φ.injective (by rw [h, map_one]))
    have hv1' : φ v ≠ 1 := fun h => hv1 (φ.injective (by rw [h, map_one]))
    rcases hu with h | h
    · exact absurd h hu1'
    rcases hv with h' | h'
    · exact absurd h' hv1'
    rw [h, h']
  · intro a ha ha1
    rw [hcen] at ha
    have hφ1 : φ a * φ a ≠ 1 := fun h => ha1 (φ.injective (by rw [map_mul, h, map_one]))
    have hφ : φ a * φ a = minusIdentity F := by
      have : φ (a * a) = -1 := by
        rcases ha with h | h
        · exact absurd h (fun h' => hφ1 (by rw [← map_mul]; exact h'))
        · exact h
      rw [← map_mul, this]
      rfl
    obtain ⟨y', hy'⟩ := exists_inverting_sl2 hodd (φ a) hφ
    refine ⟨φ.symm y', ?_⟩
    apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hy']
    exact (map_inv φ a).symm


end CFSG.GH74.GLS.Stage2.Signalizer.L48
