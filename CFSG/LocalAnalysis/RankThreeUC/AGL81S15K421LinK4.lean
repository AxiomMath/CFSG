module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinCen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinDef

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421K4Proof

open Matrix K421CenProof K421LinProof

abbrev K4 : Type := GaloisField 2 2

noncomputable instance : Fintype K4 := Fintype.ofFinite _

theorem card_K4 : Fintype.card K4 = 4 := by
  have h := GaloisField.card 2 2 (by norm_num)
  rw [Nat.card_eq_fintype_card] at h
  simpa using h

theorem exists_omega : ∃ ω : K4, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  by_contra hcon
  have hcon' : ∀ ω : K4, ω ≠ 0 → ω = 1 := fun ω h0 => by_contra fun h1 => hcon ⟨ω, h0, h1⟩
  have hsub : (Finset.univ : Finset K4) ⊆ {0, 1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon' x hx]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, card_K4] at h1
  have h2 : ({0, 1} : Finset K4).card ≤ 2 := Finset.card_le_two
  omega

noncomputable def omega4 : K4 := exists_omega.choose

theorem omega4_ne_zero : omega4 ≠ 0 := exists_omega.choose_spec.1

theorem omega4_ne_one : omega4 ≠ 1 := exists_omega.choose_spec.2

theorem two_eq_zero_K4 : (2 : K4) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K4 2

theorem omega4_cube : omega4 ^ 3 = 1 := by
  have h4 : omega4 ^ 4 = omega4 := by
    have h := FiniteField.pow_card omega4
    rwa [card_K4] at h
  apply mul_left_cancel₀ omega4_ne_zero
  calc omega4 * omega4 ^ 3 = omega4 ^ 4 := by ring
    _ = omega4 := h4
    _ = omega4 * 1 := by ring

theorem omega4_cube' : omega4 * (omega4 * omega4) = 1 := by
  have h := omega4_cube
  linear_combination h

theorem omega4_sq : omega4 * omega4 = omega4 + 1 := by
  have h3 := omega4_cube
  have hq : omega4 ^ 2 + omega4 + 1 = 0 := by
    have h : (omega4 - 1) * (omega4 ^ 2 + omega4 + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) omega4_ne_one
    · exact h
  linear_combination hq - (omega4 + 1) * two_eq_zero_K4

theorem linIndep_one_omega : LinearIndependent (ZMod 2) ![(1 : K4), omega4] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hs : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hs s with rfl | rfl <;> rcases hs t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [zero_smul, one_smul, zero_add] at hst
    exact absurd hst omega4_ne_zero
  · rw [one_smul, zero_smul, add_zero] at hst
    exact absurd hst one_ne_zero
  · rw [one_smul, one_smul] at hst
    exact absurd (by linear_combination hst - two_eq_zero_K4) omega4_ne_one

noncomputable def basis4 : Module.Basis (Fin 2) (ZMod 2) K4 :=
  basisOfLinearIndependentOfCardEqFinrank linIndep_one_omega
    (by rw [Fintype.card_fin, GaloisField.finrank 2 (by norm_num)])

theorem basis4_zero : basis4 0 = 1 := by simp [basis4]

theorem basis4_one : basis4 1 = omega4 := by simp [basis4]

noncomputable def psi4 : K4 →+* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  (Algebra.leftMulMatrix basis4).toRingHom

theorem psi4_omega : psi4 omega4 = Cm := by
  ext i j
  show Algebra.leftMulMatrix basis4 omega4 i j = Cm i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j
  · have h : omega4 * basis4 0 = basis4 1 := by rw [basis4_zero, basis4_one, mul_one]
    fin_cases i <;> simp [h, Cm, Module.Basis.repr_self, Finsupp.single_apply]
  · have h : omega4 * basis4 1 = basis4 1 + basis4 0 := by
      rw [basis4_zero, basis4_one, omega4_sq, add_comm]
    fin_cases i <;> simp [h, Cm, map_add, Module.Basis.repr_self, Finsupp.single_apply]

theorem psi4_commutant (M : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (hM : M * psi4 omega4 = psi4 omega4 * M) : ∃ k : K4, psi4 k = M := by
  classical
  rw [psi4_omega] at hM
  let T : Finset (Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
    Finset.univ.filter fun N => N * Cm = Cm * N
  have hT : T.card = 4 := by
    show (Finset.univ.filter fun N : Matrix (Fin 2) (Fin 2) (ZMod 2) => N * Cm = Cm * N).card = 4
    decide +kernel
  have hsub : (Finset.univ : Finset K4).image psi4 ⊆ T := by
    intro N hN
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hN
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [← psi4_omega, ← map_mul, ← map_mul, mul_comm]
  have hcard : ((Finset.univ : Finset K4).image psi4).card = 4 := by
    rw [Finset.card_image_of_injective _ psi4.injective, Finset.card_univ, card_K4]
  have heq : (Finset.univ : Finset K4).image psi4 = T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hT, hcard])
  have hMT : M ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, hM⟩
  rw [← heq] at hMT
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hMT
  exact ⟨k, hk⟩

@[expose] def Ωstd (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (β × Fin 2) (β × Fin 2) (ZMod 2) :=
  Matrix.of fun i j => if i.1 = j.1 then Cm i.2 j.2 else 0

theorem psiB_scalar_omega (β : Type) [Fintype β] [DecidableEq β] :
    psiB psi4 (Matrix.scalar β omega4) = Ωstd β := by
  ext ⟨b, i⟩ ⟨b', j⟩
  by_cases hb : b = b'
  · subst hb
    show psi4 ((Matrix.scalar β omega4) b b) i j = _
    simp [Matrix.scalar_apply, psi4_omega, Ωstd]
  · show psi4 ((Matrix.scalar β omega4) b b') i j = _
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, hb, Ωstd]

theorem range_Phi4 {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] :
    (Phi psi4 : GL ι (ZMod 2) × GL β K4 →* GL (ι ⊕ (β × Fin 2)) (ZMod 2)).range =
      Subgroup.centralizer ({gGL psi4 omega4 omega4_cube'} :
        Set (GL (ι ⊕ (β × Fin 2)) (ZMod 2))) :=
  range_Phi omega4_sq omega4_cube' psi4_commutant

end K421K4Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
