module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourKernelStructure

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFourKernel

open Subgroup Matrix LinearFlag LinearFieldFour LinearCover CFSG.ComponentClassification
open scoped commutatorElement

section GraphField

variable {k : Type*} [Field k]

@[expose] def invTransposeSL : SpecialLinearGroup (Fin 3) k →* SpecialLinearGroup (Fin 3) k where
  toFun B := (B⁻¹).transpose
  map_one' := by
    rw [inv_one]
    apply Subtype.ext
    change (1 : Matrix (Fin 3) (Fin 3) k)ᵀ = 1
    exact transpose_one
  map_mul' A B := by
    apply Subtype.ext
    change (adjugate ((A : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k)))ᵀ =
      (adjugate (A : Matrix (Fin 3) (Fin 3) k))ᵀ * (adjugate (B : Matrix (Fin 3) (Fin 3) k))ᵀ
    rw [adjugate_mul_distrib, transpose_mul]

variable [CharP k 2]

@[expose] def sqSL : SpecialLinearGroup (Fin 3) k →* SpecialLinearGroup (Fin 3) k :=
  SpecialLinearGroup.map (frobenius k 2)

@[expose] def graphFieldSL : SpecialLinearGroup (Fin 3) k →* SpecialLinearGroup (Fin 3) k :=
  invTransposeSL.comp sqSL

theorem graphFieldSL_scalars : scalars 3 k ≤ (scalars 3 k).comap graphFieldSL := by
  rintro B ⟨c, hc, hB⟩
  have hsq : sqSL B ∈ scalars 3 k := by
    refine ⟨c ^ 2, by rw [← pow_mul, mul_comm, pow_mul, hc, one_pow], ?_⟩
    change (B : Matrix (Fin 3) (Fin 3) k).map (frobenius k 2) = _
    rw [hB]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [frobenius_def]
    · simp [hij, frobenius_def]
  have hinv : (sqSL B)⁻¹ ∈ scalars 3 k := inv_mem hsq
  obtain ⟨d, hd, hdB⟩ := hinv
  refine ⟨d, hd, ?_⟩
  change (((sqSL B)⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)ᵀ = _
  rw [hdB, scalar_apply, diagonal_transpose]

@[expose] def graphFieldP : projectiveSL 3 k →* projectiveSL 3 k :=
  QuotientGroup.map _ _ graphFieldSL graphFieldSL_scalars

theorem graphFieldP_proj (B : SpecialLinearGroup (Fin 3) k) :
    graphFieldP (proj 3 k B) = proj 3 k (graphFieldSL B) :=
  rfl

@[expose] def jM : Matrix (Fin 3) (Fin 3) k := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

@[expose] def jMat : SpecialLinearGroup (Fin 3) k :=
  ⟨jM, by simp only [jM, det_fin_three]; simp [CharTwo.neg_eq]⟩

theorem jMat_mul_self : (jMat : SpecialLinearGroup (Fin 3) k) * jMat = 1 := by
  apply Subtype.ext
  change (jM : Matrix (Fin 3) (Fin 3) k) * jM = 1
  simp only [jM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sqSL_xMat (a : k) : sqSL (xMat a) = xMat (a ^ 2) := by
  apply Subtype.ext
  change (xM a).map (frobenius k 2) = xM (a ^ 2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xM, frobenius_def]

theorem sqSL_yMat (b : k) : sqSL (yMat b) = yMat (b ^ 2) := by
  apply Subtype.ext
  change (yM b).map (frobenius k 2) = yM (b ^ 2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [yM, frobenius_def]

theorem jMat_mul_invTransposeSL_xMat (c : k) : jMat * invTransposeSL (xMat c) * jMat = yMat c := by
  have hinv : (xMat c)⁻¹ = xMat (-c) :=
    inv_eq_of_mul_eq_one_right (by rw [← xMat_add, add_neg_cancel]; exact (slRoots (K := k)).x_zero)
  change jMat * ((xMat c)⁻¹).transpose * jMat = yMat c
  rw [hinv]
  apply Subtype.ext
  change jM * (xM (-c))ᵀ * jM = yM c
  have ht : (xM (-c))ᵀ = !![1, 0, 0; -c, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [ht]
  simp only [jM, yM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]

theorem jMat_mul_invTransposeSL_yMat (c : k) : jMat * invTransposeSL (yMat c) * jMat = xMat c := by
  have hinv : (yMat c)⁻¹ = yMat (-c) :=
    inv_eq_of_mul_eq_one_right (by rw [← yMat_add, add_neg_cancel]; exact (slRoots (K := k)).y_zero)
  change jMat * ((yMat c)⁻¹).transpose * jMat = xMat c
  rw [hinv]
  apply Subtype.ext
  change jM * (yM (-c))ᵀ * jM = xM c
  have ht : (yM (-c))ᵀ = !![1, 0, 0; 0, 1, 0; 0, -c, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [ht]
  simp only [jM, xM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]

theorem jP_conj_graphFieldP_xP (a : k) :
    proj 3 k jMat * graphFieldP (xP a) * (proj 3 k jMat)⁻¹ = yP (a ^ 2) := by
  have hj : (proj 3 k (jMat : SpecialLinearGroup (Fin 3) k))⁻¹ = proj 3 k jMat := by
    rw [inv_eq_iff_mul_eq_one, ← map_mul, jMat_mul_self, map_one]
  rw [hj, xP, graphFieldP_proj, ← map_mul, ← map_mul, graphFieldSL, MonoidHom.comp_apply,
    sqSL_xMat, jMat_mul_invTransposeSL_xMat]
  rfl

theorem jP_conj_graphFieldP_yP (b : k) :
    proj 3 k jMat * graphFieldP (yP b) * (proj 3 k jMat)⁻¹ = xP (b ^ 2) := by
  have hj : (proj 3 k (jMat : SpecialLinearGroup (Fin 3) k))⁻¹ = proj 3 k jMat := by
    rw [inv_eq_iff_mul_eq_one, ← map_mul, jMat_mul_self, map_one]
  rw [hj, yP, graphFieldP_proj, ← map_mul, ← map_mul, graphFieldSL, MonoidHom.comp_apply,
    sqSL_yMat, jMat_mul_invTransposeSL_yMat]
  rfl

end GraphField

theorem linear_three_four_graph_field_inverts_full_central_two_kernel {k : Type*} [Field k]
    (hk : Nat.card k = 4) {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (η : A →* projectiveSL 3 k) (hη : Function.Surjective η) (hK : η.ker ≤ center A)
    (γ : MulAut A)
    (hγ : ∀ a, η (γ a) = (haveI := charP_two_of_card_eq_four hk; graphFieldP) (η a)) :
    (∀ z ∈ η.ker, (∃ n : ℕ, z ^ 2 ^ n = 1) → γ z = z⁻¹) ∧
      ∀ z ∈ η.ker, z ^ 2 = 1 → γ z = z := by
  have := charP_two_of_card_eq_four hk
  have hker : ∀ z, η z = 1 → z ∈ center A := fun z hz => hK hz
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hk
  have hω3 := omega_cube hk hω0
  have hω2 := omega_mul_omega hk hω0 hω1
  have hω4 := one_add_omega_add_omega_sq hk hω0 hω1
  set u := lift η hη (hP ω hω3)
  have hu : η u = hP ω hω3 := map_lift η hη _
  set j := lift η hη (proj 3 k jMat)
  have hj : η j = proj 3 k jMat := map_lift η hη _
  have hcomm := rootComm_mul_comm η hη hker
  have hγd : ∀ a b : k, j * γ (rootComm η hη a b) * j⁻¹ = (rootComm η hη (b ^ 2) (a ^ 2))⁻¹ := by
    intro a b
    rw [rootComm, map_commutatorElement, conj_commutatorElement, rootComm,
      commutatorElement_inv]
    refine comm_eq η hker ?_ ?_
    · rw [map_mul, map_mul, map_inv, hj, hγ, map_lift, jP_conj_graphFieldP_xP, map_lift]
    · rw [map_mul, map_mul, map_inv, hj, hγ, map_lift, jP_conj_graphFieldP_yP, map_lift]
  have hsmul : ∀ c : k, c ≠ 0 → ∀ a b : k,
      normComm η hη ω (c * a) (c * b) = normComm η hη ω a b := by
    intro c hc a b
    rcases eq_zero_or_eq_one_or hk hω0 hω1 c with rfl | rfl | rfl | rfl
    · exact absurd rfl hc
    · rw [one_mul, one_mul]
    · exact normComm_smul η hη hker hω3 a b
    · rw [← hω2, mul_assoc, mul_assoc, normComm_smul η hη hker hω3,
        normComm_smul η hη hker hω3]
  have hzero_left : ∀ b : k, normComm η hη ω 0 b = 1 := fun b => by
    simp only [normComm, mul_zero, rootComm_zero_left η hη hker, mul_one]
  have hzero_right : ∀ a : k, normComm η hη ω a 0 = 1 := fun a => by
    simp only [normComm, mul_zero, rootComm_zero_right η hη hker, mul_one]
  have hswap : ∀ a b : k, normComm η hη ω (b ^ 2) (a ^ 2) = normComm η hη ω a b := by
    intro a b
    by_cases ha : a = 0
    · rw [ha, hzero_left, show (0 : k) ^ 2 = 0 by ring, hzero_right]
    by_cases hb : b = 0
    · rw [hb, hzero_right, show (0 : k) ^ 2 = 0 by ring, hzero_left]
    have ha3 := pow_three_eq_one hk ha
    have hb3 := pow_three_eq_one hk hb
    have hc : b ^ 2 * a⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero 2 hb) (inv_ne_zero ha)
    rw [← hsmul (b ^ 2 * a⁻¹) hc a b]
    congr 1
    · field_simp
    · field_simp
      linear_combination ha3 - hb3
  have hγk : ∀ a b : k, γ (normComm η hη ω a b) = (normComm η hη ω a b)⁻¹ := by
    intro a b
    have hNc : normComm η hη ω a b ∈ center A := hker _ (map_normComm η hη hω3 hω4 a b)
    have hγNc : γ (normComm η hη ω a b) ∈ center A := apply_mem_center γ hNc
    have e : ∀ x y z : A, j * (x * y * z) * j⁻¹ = (j * x * j⁻¹) * (j * y * j⁻¹) * (j * z * j⁻¹) :=
      fun x y z => by group
    have h2 : j * γ (normComm η hη ω a b) * j⁻¹ = (normComm η hη ω (b ^ 2) (a ^ 2))⁻¹ := by
      simp only [normComm]
      rw [map_mul, map_mul, e, hγd, hγd, hγd,
        inv_mul_inv_mul_inv (hcomm _ _ _ _) (hcomm _ _ _ _) (hcomm _ _ _ _)]
      congr 1
      rw [show (ω * b) ^ 2 = ω * (ω * b ^ 2) by ring, show (ω * a) ^ 2 = ω * (ω * a ^ 2) by ring,
        show (ω * (ω * b)) ^ 2 = ω * b ^ 2 by linear_combination (ω * b ^ 2) * hω3,
        show (ω * (ω * a)) ^ 2 = ω * a ^ 2 by linear_combination (ω * a ^ 2) * hω3,
        mul_assoc, hcomm (ω * (ω * b ^ 2)), ← mul_assoc]
    rw [← conj_of_mem_center j hγNc, h2, hswap]
  set κ₁ := normComm η hη ω 1 1
  set κ₂ := normComm η hη ω ω 1
  let S : Subgroup A :=
    { carrier := {z | z ∈ center A ∧ γ z = z⁻¹}
      one_mem' := ⟨one_mem _, by rw [map_one, inv_one]⟩
      mul_mem' := fun {z₁ z₂} ⟨h₁, g₁⟩ ⟨h₂, g₂⟩ => ⟨mul_mem h₁ h₂, by
        rw [map_mul, g₁, g₂, _root_.mul_inv_rev]
        exact (mem_center_iff.mp (inv_mem h₁) z₂⁻¹).symm⟩
      inv_mem' := fun {z} ⟨h, g⟩ => ⟨inv_mem h, by rw [map_inv, g]⟩ }
  have hS : closure {κ₁, κ₂} ≤ S := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨hker _ (map_normComm η hη hω3 hω4 1 1), hγk 1 1⟩
    · exact ⟨hker _ (map_normComm η hη hω3 hω4 ω 1), hγk ω 1⟩
  have hmain : ∀ z ∈ η.ker, (∃ n : ℕ, z ^ 2 ^ n = 1) → γ z = z⁻¹ := fun z hz hn =>
    (hS (twoPart_le_closure_normComm η hη hker hω3 u hu hk hω0 hω1 z hz hn)).2
  refine ⟨hmain, fun z hz h2 => ?_⟩
  rw [hmain z hz ⟨1, by rwa [pow_one]⟩]
  exact inv_eq_of_mul_eq_one_right (by rwa [← sq])

end LinearFieldFourKernel

end CFSG.LocalAnalysis.ComponentInitial
