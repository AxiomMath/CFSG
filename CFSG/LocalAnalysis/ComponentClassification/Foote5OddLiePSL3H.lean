module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSL3F
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCoreX

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {k : Type} [Field k] {n : ℕ} {X : Type} [Group X]

theorem slConjugation_center (A : GL (Fin n) k) {z : SL(n, k)} (hz : z ∈ center SL(n, k)) :
    slConjugation n k A z = z := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  apply Subtype.ext
  change (slConjugation n k A z : Matrix (Fin n) (Fin n) k) = z
  rw [slConjugation_matrix, ← hr, ← (scalar_commute r (fun _ => Commute.all _ _) A.val).eq,
    Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem slConjugation_signGL_coordBlockSL (σ : Fin n → Bool) (b : Bool) {s : SL(n, k)}
    (hs : s ∈ coordBlockSL k (coordSet σ b)) : slConjugation n k (signGL k σ) s = s := by
  refine slConjugation_diagGL_fixes_coordBlockSL _ ?_ hs
  intro i hi j hj
  rw [mem_coordSet] at hi hj
  rw [hi, hj]

theorem eq_one_of_mem_center_coordBlockSL {J : Finset (Fin n)} {c : Fin n} (hc : c ∉ J)
    {z : SL(n, k)} (hz : z ∈ center SL(n, k)) (hzJ : z ∈ coordBlockSL k J) : z = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h1 := (mem_coordBlockSL_iff.mp hzJ) c c (Or.inl hc)
  simp only [↓reduceIte] at h1
  rw [← hr, scalar_apply, diagonal_apply_eq] at h1
  apply Subtype.ext
  change (z : Matrix (Fin n) (Fin n) k) = 1
  rw [← hr, h1, map_one]

variable [Finite k]

theorem fixed_of_odd (hk : Nat.card k = 3) {Ψ : SL(n, k) →* X}
    (hker : Ψ.ker ≤ center SL(n, k)) {f : X} {σ : Fin n → Bool}
    (hf : ∀ y, f * Ψ y * f⁻¹ = Ψ (slConjugation n k (signGL k σ) y)) {y : SL(n, k)}
    (hyf : f * Ψ y = Ψ y * f) {m : ℕ} (hm : Odd m) (hym : Ψ y ^ m = 1) :
    slConjugation n k (signGL k σ) y = y := by
  set D := slConjugation n k (signGL k σ) with hD
  have h1 : Ψ (D y) = Ψ y := by
    rw [← hf y, hyf, mul_inv_cancel_right]
  set z := D y * y⁻¹ with hz
  have hzc : z ∈ center SL(n, k) := hker (by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, h1, mul_inv_cancel])
  have hDy : D y = z * y := by rw [hz, inv_mul_cancel_right]
  have hcomm : Commute z y := (mem_center_iff.mp hzc y).symm
  have hym' : y ^ m ∈ center SL(n, k) := hker (by rw [MonoidHom.mem_ker, map_pow, hym])
  have h2 : D (y ^ m) = y ^ m := slConjugation_center _ hym'
  rw [map_pow, hDy, hcomm.mul_pow] at h2
  have hzm : z ^ m = 1 := by
    have := congrArg (· * (y ^ m)⁻¹) h2
    simpa using this
  have hz1 : z = 1 := eq_one_of_mul_self (center_mul_self hk hzc) hm hzm
  rw [hDy, hz1, one_mul]

theorem transvection_pow_three (hk : Nat.card k = 3) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (c : k) : (SpecialLinearGroup.transvection hij c) ^ 3 = 1 := by
  have h3 := three_eq_zero_of_card hk
  rw [pow_three', ← SpecialLinearGroup.transvection_add, ← SpecialLinearGroup.transvection_add,
    show c + c + c = 3 * c by ring, h3, zero_mul, SpecialLinearGroup.transvection_coeff_zero]

section Block

variable (hk : Nat.card k = 3) {Ψ : SL(n, k) →* X} (hker : Ψ.ker ≤ center SL(n, k)) {f : X}
  {σ : Fin n → Bool} (hf : ∀ y, f * Ψ y * f⁻¹ = Ψ (slConjugation n k (signGL k σ) y))
  {b : Bool} (hJ : (coordSet σ b).card = 2)

include hk hf hJ in
theorem blockTwo_le_oddClosure :
    (coordBlockSL k (coordSet σ b)).map Ψ ≤
      oddClosure (Ψ.range ⊓ centralizer ({f} : Set X)) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [← range_blockTwo _ hJ] at hs
  obtain ⟨Y, rfl⟩ := hs
  have hC : ∀ s ∈ coordBlockSL k (coordSet σ b), Ψ s ∈ Ψ.range ⊓ centralizer ({f} : Set X) := by
    intro s hs
    refine mem_inf.mpr ⟨⟨s, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hf s
    rw [slConjugation_signGL_coordBlockSL σ b hs] at h1
    calc Ψ s * f = f * Ψ s * f⁻¹ * f := by rw [h1]
      _ = f * Ψ s := by group
  refine Matrix.SL2.transvection_induction
    (fun Y => Ψ (blockTwo (coordSet σ b) hJ Y) ∈ oddClosure (Ψ.range ⊓ centralizer ({f} : Set X)))
    (fun i j hij c => ?_) (fun A B hA hB => ?_) Y
  · refine Subgroup.subset_closure ⟨hC _ ?_, ?_⟩
    · rw [← range_blockTwo _ hJ]
      exact ⟨_, rfl⟩
    · have h3 : Ψ (blockTwo (coordSet σ b) hJ (SpecialLinearGroup.transvection hij c)) ^ 3 = 1 := by
        rw [← map_pow, ← map_pow, transvection_pow_three hk, map_one, map_one]
      exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)
  · rw [map_mul, map_mul]
    exact mul_mem hA hB

include hk hker hf in
theorem conj_mem_blockTwo :
    ∀ t ∈ oddClosure (Ψ.range ⊓ centralizer ({f} : Set X)),
      ∀ h ∈ (coordBlockSL k (coordSet σ b)).map Ψ,
        t * h * t⁻¹ ∈ (coordBlockSL k (coordSet σ b)).map Ψ := by
  have h2 := two_ne_zero_of_card hk
  set H := (coordBlockSL k (coordSet σ b)).map Ψ with hH
  have hle : oddClosure (Ψ.range ⊓ centralizer ({f} : Set X)) ≤ normalizer (H : Set X) := by
    rw [oddClosure, closure_le]
    rintro t ⟨htC, hto⟩
    obtain ⟨⟨y, rfl⟩, hyf⟩ := mem_inf.mp htC
    rw [mem_centralizer_singleton_iff] at hyf
    have hy := fixed_of_odd hk hker hf hyf.symm hto (pow_orderOf_eq_one _)
    have hy' : slConjugation n k (signGL k σ) y⁻¹ = y⁻¹ := by rw [map_inv, hy]
    have hconj : ∀ y' : SL(n, k), slConjugation n k (signGL k σ) y' = y' →
        ∀ h ∈ H, Ψ y' * h * (Ψ y')⁻¹ ∈ H := by
      rintro y' hy'' _ ⟨s, hs, rfl⟩
      refine ⟨y' * s * y'⁻¹, conj_mem_coordBlockSL
        (compIndicator_comm_of_fixed_signGL h2 hy'' b) hs, ?_⟩
      rw [map_mul, map_mul, map_inv]
    rw [SetLike.mem_coe, mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj y hy h hh, fun hh => ?_⟩
    have := hconj y⁻¹ hy' _ hh
    rw [map_inv, inv_inv] at this
    simpa [mul_assoc] using this
  intro t ht h hh
  exact (mem_normalizer_iff.mp (hle ht) h).mp hh

include hker hJ in
omit [Finite k] in
theorem nonempty_blockTwo_equiv {c : Fin n} (hc : c ∉ coordSet σ b) :
    Nonempty (SL(2, k) ≃* (coordBlockSL k (coordSet σ b)).map Ψ) := by
  set K := coordBlockSL k (coordSet σ b) with hK
  have hinj : Function.Injective (Ψ.comp K.subtype) := by
    intro s s' h
    have h2 : ((s⁻¹ * s' : K) : SL(n, k)) ∈ center SL(n, k) := hker (by
      rw [MonoidHom.mem_ker, coe_mul, coe_inv, map_mul, map_inv]
      have : Ψ s = Ψ s' := h
      rw [this, inv_mul_cancel])
    have h3 := eq_one_of_mem_center_coordBlockSL hc h2 (s⁻¹ * s').2
    have h4 : s⁻¹ * s' = 1 := Subtype.ext h3
    exact (inv_mul_eq_one.mp h4)
  have hrange : (Ψ.comp K.subtype).range = K.map Ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((MonoidHom.ofInjective (blockTwo_injective (k := k) (coordSet σ b) hJ)).trans
    (MulEquiv.subgroupCongr (range_blockTwo _ hJ))).trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩

end Block

@[expose] def qOne (k : Type) [Field k] : SL(2, k) :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two_of]⟩

@[expose] def qTwo (k : Type) [Field k] : SL(2, k) :=
  ⟨!![1, 1; 1, 2], by simp [det_fin_two_of]; norm_num⟩

omit [Finite k] in
theorem pow_four_of_mul_self {q : SL(2, k)}
    (hq : (q : Matrix (Fin 2) (Fin 2) k) * q = -1) : q ^ 4 = 1 := by
  apply Subtype.ext
  change (q : Matrix (Fin 2) (Fin 2) k) ^ 4 = 1
  rw [show 4 = 2 + 2 by rfl, pow_add, sq, hq]
  simp

omit [Finite k] in
theorem qOne_pow_four : qOne k ^ 4 = 1 := by
  refine pow_four_of_mul_self ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qOne, Matrix.mul_apply, Fin.sum_univ_two]

theorem qTwo_pow_four (hk : Nat.card k = 3) : qTwo k ^ 4 = 1 := by
  have h3 := three_eq_zero_of_card hk
  refine pow_four_of_mul_self ?_
  ext i j
  fin_cases i <;> fin_cases j
  · simp [qTwo, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h3
  · simp [qTwo, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h3
  · simp [qTwo, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h3
  · simp [qTwo, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination 2 * h3
end CFSG.ComponentClassification.Foote5.OddLieCore
