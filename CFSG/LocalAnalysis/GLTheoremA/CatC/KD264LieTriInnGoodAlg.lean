module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

section Perm

variable {n : Type} [Fintype n] [DecidableEq n]

def cyc3 (a b c : n) : Equiv.Perm n := Equiv.swap a b * Equiv.swap b c

theorem cyc3_apply_a {a b c : n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cyc3 a b c a = b := by
  simp [cyc3, Equiv.swap_apply_of_ne_of_ne hab hac]

theorem cyc3_apply_b {a b c : n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cyc3 a b c b = c := by
  simp [cyc3, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]

theorem cyc3_apply_c {a b c : n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cyc3 a b c c = a := by
  simp [cyc3, hbc.symm, hab]

theorem cyc3_pow_three {a b c : n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cyc3 a b c ^ 3 = 1 := by
  ext x
  by_cases hxa : x = a
  · subst hxa
    simp [pow_succ, cyc3_apply_a hab hbc hac, cyc3_apply_b hab hbc hac, cyc3_apply_c hab hbc hac]
  by_cases hxb : x = b
  · subst hxb
    simp [pow_succ, cyc3_apply_a hab hbc hac, cyc3_apply_b hab hbc hac, cyc3_apply_c hab hbc hac]
  by_cases hxc : x = c
  · subst hxc
    simp [pow_succ, cyc3_apply_a hab hbc hac, cyc3_apply_b hab hbc hac, cyc3_apply_c hab hbc hac]
  · simp [pow_succ, cyc3, Equiv.swap_apply_of_ne_of_ne hxa hxb,
      Equiv.swap_apply_of_ne_of_ne hxb hxc, Equiv.swap_apply_of_ne_of_ne hxa hxc, hxa, hxb, hxc]

theorem sign_cyc3 {a b c : n} (hab : a ≠ b) (hbc : b ≠ c) :
    Equiv.Perm.sign (cyc3 a b c) = 1 := by
  simp [cyc3, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hbc]

end Perm

section Mat

variable {n : Type} [Fintype n] [DecidableEq n] {L : Type} [Field L]

noncomputable def triP (a b c : n) : Matrix n n L := (cyc3 a b c).permMatrix L

def triD (c : n) : n → L := fun x => if x = c then -1 else 1

noncomputable def triZ (a b c : n) : Matrix n n L :=
  (Equiv.swap a b).permMatrix L * diagonal (triD c)

theorem permMatrix_map (σ : L →+* L) (π : Equiv.Perm n) :
    (π.permMatrix L).map σ = π.permMatrix L := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs
  · exact map_one σ
  · exact map_zero σ

theorem permMatrix_transpose_mul (π : Equiv.Perm n) :
    (π.permMatrix L)ᵀ * π.permMatrix L = 1 := by
  rw [transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

theorem triP_transpose_mul (a b c : n) : (triP a b c : Matrix n n L)ᵀ * triP a b c = 1 :=
  permMatrix_transpose_mul _

theorem triP_map (σ : L →+* L) (a b c : n) : (triP a b c : Matrix n n L).map σ = triP a b c :=
  permMatrix_map σ _

theorem triP_pow_three {a b c : n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (triP a b c : Matrix n n L) ^ 3 = 1 := by
  have h : (cyc3 a b c ^ 3).permMatrix L = (triP a b c) ^ 3 := by
    simp only [triP, pow_succ, pow_zero, one_mul, permMatrix_mul]
    simp only [← Matrix.mul_assoc]
  rw [← h, cyc3_pow_three hab hbc hac, permMatrix_one]

theorem det_triP {a b c : n} (hab : a ≠ b) (hbc : b ≠ c) :
    (triP a b c : Matrix n n L).det = 1 := by
  simp [triP, det_permutation, sign_cyc3 hab hbc]

theorem triD_mul_self (c : n) (x : n) : (triD c x : L) * triD c x = 1 := by
  unfold triD
  split_ifs <;> simp

theorem diagonal_triD_map (σ : L →+* L) (c : n) :
    (diagonal (triD c : n → L)).map σ = diagonal (triD c) := by
  rw [diagonal_map (map_zero σ)]
  congr 1
  funext x
  unfold triD
  split_ifs <;> simp

theorem triZ_transpose_mul (a b c : n) : (triZ a b c : Matrix n n L)ᵀ * triZ a b c = 1 := by
  unfold triZ
  rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (_ᵀ),
    permMatrix_transpose_mul, Matrix.one_mul, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext x
  exact triD_mul_self c x

theorem triZ_map (σ : L →+* L) (a b c : n) : (triZ a b c : Matrix n n L).map σ = triZ a b c := by
  unfold triZ
  rw [Matrix.map_mul, permMatrix_map, diagonal_triD_map]

theorem det_triZ {a b c : n} (hab : a ≠ b) :
    (triZ a b c : Matrix n n L).det = 1 := by
  unfold triZ
  rw [det_mul, det_permutation, det_diagonal, Equiv.Perm.sign_swap hab]
  have : ∏ x : n, (triD c x : L) = -1 := by
    unfold triD
    rw [Finset.prod_ite_eq' Finset.univ c (fun _ => (-1 : L))]
    simp
  rw [this]
  simp

theorem triZ_mul_triP_ne {a b c : n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (triZ a b c : Matrix n n L) * triP a b c ≠ triP a b c * triZ a b c := by
  intro h
  have h1 := congrArg (fun M : Matrix n n L => (M *ᵥ Pi.single a 1) a) h
  simp only [← Matrix.mulVec_mulVec, triP, triZ, permMatrix_mulVec, Matrix.mulVec_diagonal,
    Function.comp_apply, Pi.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    cyc3_apply_a hab hbc hac, cyc3_apply_b hab hbc hac, Pi.single_apply, triD, if_neg hbc,
    if_neg hac.symm, if_neg hac, if_true, mul_one, if_neg hab.symm] at h1
  simp at h1

end Mat

section SLPair

open CFSG.RankThree.Classical2 CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {L : Type} [Field L] {ν : ℕ}

theorem mem_fix_of_orthogonal (σ : L ≃+* L) (X : SL(ν, L))
    (hM : (X : Matrix (Fin ν) (Fin ν) L)ᵀ * X = 1)
    (hσ : (X : Matrix (Fin ν) (Fin ν) L).map σ.toRingHom = X) :
    X ∈ fixSubgroup (stdUnitaryEquiv σ) := by
  rw [mem_fixSubgroup, stdUnitaryEquiv_apply]
  apply Subtype.ext
  rw [coe_stdUnitary]
  change (((X : Matrix (Fin ν) (Fin ν) L).map σ.toRingHom)⁻¹)ᵀ = X
  rw [hσ, Matrix.inv_eq_left_inv hM, transpose_transpose]

theorem exists_pair_SL (hν : 3 ≤ ν) :
    ∃ y z : SL(ν, L), y ^ 3 = 1 ∧ y * z ≠ z * y ∧
      ∀ σ : L ≃+* L, y ∈ fixSubgroup (stdUnitaryEquiv σ) ∧ z ∈ fixSubgroup (stdUnitaryEquiv σ) := by
  set a : Fin ν := ⟨0, by omega⟩ with ha
  set b : Fin ν := ⟨1, by omega⟩ with hb
  set c : Fin ν := ⟨2, by omega⟩ with hc
  have hab : a ≠ b := fun h => by simpa [ha, hb] using congrArg Fin.val h
  have hbc : b ≠ c := fun h => by simpa [hb, hc] using congrArg Fin.val h
  have hac : a ≠ c := fun h => by simpa [ha, hc] using congrArg Fin.val h
  obtain ⟨y, hy⟩ : ∃ y : SL(ν, L), (y : Matrix (Fin ν) (Fin ν) L) = triP a b c :=
    ⟨⟨triP a b c, det_triP hab hbc⟩, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : SL(ν, L), (z : Matrix (Fin ν) (Fin ν) L) = triZ a b c :=
    ⟨⟨triZ a b c, det_triZ hab⟩, rfl⟩
  refine ⟨y, z, ?_, ?_, fun σ => ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hy]
    exact triP_pow_three hab hbc hac
  · intro h
    have h' := congrArg (fun x : SL(ν, L) => (x : Matrix (Fin ν) (Fin ν) L)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, hy, hz] at h'
    exact triZ_mul_triP_ne hab hbc hac h'.symm
  · exact mem_fix_of_orthogonal σ y (by rw [hy]; exact triP_transpose_mul a b c)
      (by rw [hy]; exact triP_map _ a b c)
  · exact mem_fix_of_orthogonal σ z (by rw [hz]; exact triZ_transpose_mul a b c)
      (by rw [hz]; exact triZ_map _ a b c)

end SLPair

section SLTwo

variable {K : Type} [Field K]

theorem exists_pair_SL2 : ∃ y z : SL(2, K), y ^ 3 = 1 ∧ y * z ≠ z * y := by
  obtain ⟨y, hy⟩ : ∃ y : SL(2, K), (y : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, -1] :=
    ⟨⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two_of]⟩, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : SL(2, K), (z : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] :=
    ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩, rfl⟩
  refine ⟨y, z, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hy]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h' := congrArg (fun x : SL(2, K) => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [Matrix.SpecialLinearGroup.coe_mul, hy, hz, Matrix.mul_apply, Fin.sum_univ_two] at h'

end SLTwo

section Abstract

theorem perfect_dvd_three_of_central_hom {X G : Type*} [Group X] [Group G] (g : X →* G)
    (hperf : Group.IsPerfect X) (hker : g.ker ≤ Subgroup.center X) {y z : X}
    (hy : y ^ 3 = 1) (hyz : y * z ≠ z * y) :
    ⁅g.range, g.range⁆ = g.range ∧ 3 ∣ Nat.card g.range := by
  refine ⟨?_, ?_⟩
  · have h1 : g.range = (⊤ : Subgroup X).map g := (MonoidHom.range_eq_map g)
    rw [h1, ← Subgroup.map_commutator, ← commutator_def, Group.isPerfect_def.1 hperf]
  · have hw3 : g y ^ 3 = 1 := by rw [← map_pow, hy, map_one]
    have hw1 : g y ≠ 1 := by
      intro h1
      apply hyz
      have hyk : y ∈ g.ker := h1
      exact (Subgroup.mem_center_iff.1 (hker hyk) z).symm
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (g y) = 3 := orderOf_eq_prime hw3 hw1
    have hmem : g y ∈ g.range := ⟨y, rfl⟩
    have h2 : orderOf (⟨g y, hmem⟩ : g.range) = 3 := by
      rw [Subgroup.orderOf_mk, hord]
    rw [← h2]
    exact orderOf_dvd_natCard _

end Abstract

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

end
