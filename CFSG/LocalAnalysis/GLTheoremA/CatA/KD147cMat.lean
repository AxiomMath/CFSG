module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open scoped MatrixGroups

def kd147cM (K : Type) [Field K] : SL(2, K) :=
  ⟨!![0, -1; 1, -1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem kd147cM_pow_three (K : Type) [Field K] : kd147cM K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kd147cM, Matrix.mul_apply, Fin.sum_univ_two]

def kd147cL (K : Type) [Field K] : SL(2, K) :=
  ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem kd147cL_mul_ne (K : Type) [Field K] : kd147cL K * kd147cM K ≠ kd147cM K * kd147cL K := by
  intro h
  have h' := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
  have h00 := congrFun (congrFun h' 0) 0
  simp [kd147cM, kd147cL, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem kd147c_three_dvd_card {G : Type*} [Group G] {R : Subgroup G} {g : G} (hg : g ∈ R)
    (h3 : orderOf g = 3) : 3 ∣ Nat.card R := by
  have h := orderOf_dvd_natCard (⟨g, hg⟩ : R)
  rwa [Subgroup.orderOf_mk, h3] at h

section Unitary

variable {L : Type} [Field L]

def kd147cCyc (L : Type) [Field L] : SL(3, L) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

def kd147cSw (L : Type) [Field L] : SL(3, L) :=
  ⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem kd147cCyc_pow_three : kd147cCyc L ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kd147cCyc, Matrix.mul_apply, Fin.sum_univ_three]

theorem kd147cSw_mul_ne : kd147cSw L * kd147cCyc L ≠ kd147cCyc L * kd147cSw L := by
  intro h
  have h' := congrArg (fun B : SL(3, L) => (B : Matrix (Fin 3) (Fin 3) L)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
  have h00 := congrFun (congrFun h' 0) 0
  simp [kd147cSw, kd147cCyc, Matrix.mul_apply, Fin.sum_univ_three] at h00

theorem kd147c_stdUnitary_eq_self (σ : L →+* L) (X : SL(3, L))
    (hmap : (X : Matrix (Fin 3) (Fin 3) L).map σ = X)
    (horth : (X : Matrix (Fin 3) (Fin 3) L) * (X : Matrix (Fin 3) (Fin 3) L)ᵀ = 1) :
    stdUnitary σ X = X := by
  apply Subtype.ext
  rw [coe_stdUnitary, hmap, Matrix.inv_eq_right_inv horth, Matrix.transpose_transpose]

theorem kd147c_stdUnitary_cyc (σ : L →+* L) : stdUnitary σ (kd147cCyc L) = kd147cCyc L := by
  refine kd147c_stdUnitary_eq_self σ _ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [kd147cCyc]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [kd147cCyc, Matrix.mul_apply, Fin.sum_univ_three]

theorem kd147c_stdUnitary_sw (σ : L →+* L) : stdUnitary σ (kd147cSw L) = kd147cSw L := by
  refine kd147c_stdUnitary_eq_self σ _ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [kd147cSw]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [kd147cSw, Matrix.mul_apply, Fin.sum_univ_three]

end Unitary

section Frame

variable {L : Type} [Field L]

theorem kd147c_frameRoots_ncard {τ : Tag} {ν : ℕ} {ρ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (h : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) :
    (frameRoots σ).ncard = ν * (ν - 1) := by
  classical
  have himg : frameRoots σ = (fun p : Fin ν × Fin ν => σ p.1 p.2) ''
      (↑(Finset.univ : Finset (Fin ν)).offDiag : Set (Fin ν × Fin ν)) := by
    ext r
    simp only [frameRoots, Set.mem_setOf_eq, Set.mem_image, Finset.coe_offDiag, Set.mem_offDiag,
      Finset.coe_univ, Set.mem_univ, true_and, Prod.exists]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨i, j, hij, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨i, j, hij, rfl⟩
  have hinj : Set.InjOn (fun p : Fin ν × Fin ν => σ p.1 p.2)
      (↑(Finset.univ : Finset (Fin ν)).offDiag : Set (Fin ν × Fin ν)) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
    simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.coe_univ, Set.mem_univ, true_and]
      at hab hcd
    obtain ⟨h1, h2⟩ := h.eq_of_eq hκ hnorm hab hcd he
    exact Prod.ext h1 h2
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset, Finset.offDiag_card, Finset.card_univ,
    Fintype.card_fin, Nat.mul_sub_one]

end Frame

section Kernel


def kd147cVec (x y : ℤ) : Fin Tag.G2.rank → ℤ := ![x, y]

theorem kd147c_isRoot_10 : IsRoot Tag.G2 (kd147cVec 1 0) := by
  rw [isRoot_iff_mem_artifactRoots]
  decide +kernel

theorem kd147c_isRoot_01 : IsRoot Tag.G2 (kd147cVec 0 1) := by
  rw [isRoot_iff_mem_artifactRoots]
  decide +kernel

theorem kd147c_isRoot_11 : IsRoot Tag.G2 (kd147cVec 1 1) := by
  rw [isRoot_iff_mem_artifactRoots]
  decide +kernel

theorem kd147c_isRoot_12 : IsRoot Tag.G2 (kd147cVec 1 2) := by
  rw [isRoot_iff_mem_artifactRoots]
  decide +kernel

theorem kd147c_rootChar_vec {L : Type} [Field L] (a : Fin Tag.G2.rank → Lˣ) (x y : ℤ) :
    rootChar a (kd147cVec x y) = a 0 ^ x * a 1 ^ y := by
  unfold rootChar
  show ∏ i : Fin 2, a i ^ ((![x, y] : Fin 2 → ℤ) i) = _
  rw [Fin.prod_univ_two]
  rfl

theorem kd147c_unit_sq_add_one {L : Type} [Field L] {x : Lˣ} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    (x : L) ^ 2 + x + 1 = 0 := by
  have h : ((x : L) - 1) * ((x : L) ^ 2 + x + 1) = 0 := by
    have : (x : L) ^ 3 = 1 := by simpa using congrArg (fun u : Lˣ => (u : L)) h3
    linear_combination this
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h)) h1
  · exact h

theorem kd147c_unit_eq_or_inv {L : Type} [Field L] {x y : Lˣ} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  have hX := kd147c_unit_sq_add_one hx3 hx1
  have hY := kd147c_unit_sq_add_one hy3 hy1
  have h3 : (x : L) ^ 3 = 1 := by simpa using congrArg (fun u : Lˣ => (u : L)) hx3
  have hinv : ((x⁻¹ : Lˣ) : L) = (x : L) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right (by linear_combination h3)
  have h : ((y : L) - x) * ((y : L) - (x : L) ^ 2) = 0 := by
    linear_combination hY - (y : L) * hX + h3
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (Units.ext (by linear_combination h))
  · exact Or.inr (Units.ext (by rw [hinv]; linear_combination h))

theorem kd147c_exists_kernel_root {L : Type} [Field L] (a : Fin Tag.G2.rank → Lˣ)
    (ha : ∀ i, a i ^ 3 = 1) : ∃ γ, IsRoot Tag.G2 γ ∧ rootChar a γ = 1 := by
  by_cases hx : a 0 = 1
  · exact ⟨kd147cVec 1 0, kd147c_isRoot_10, by rw [kd147c_rootChar_vec, hx]; simp⟩
  by_cases hy : a 1 = 1
  · exact ⟨kd147cVec 0 1, kd147c_isRoot_01, by rw [kd147c_rootChar_vec, hy]; simp⟩
  rcases kd147c_unit_eq_or_inv (ha 0) hx (ha 1) hy with h | h
  · refine ⟨kd147cVec 1 2, kd147c_isRoot_12, ?_⟩
    rw [kd147c_rootChar_vec, h]
    calc a 0 ^ (1 : ℤ) * a 0 ^ (2 : ℤ) = a 0 ^ 3 := by
          rw [← _root_.zpow_add]
          norm_num
      _ = 1 := ha 0
  · refine ⟨kd147cVec 1 1, kd147c_isRoot_11, ?_⟩
    rw [kd147c_rootChar_vec, h]
    simp

theorem kd147c_twistKind_cases (ρ : Equiv.Perm (Fin Tag.G2.rank → ℤ)) {L : Type} [Field L]
    (χ : Multiplicative (Fin Tag.G2.rank → ℤ) →* Lˣ) (i : KernelComponent χ) :
    twistKind ρ χ i = .inner ∨ twistKind ρ χ i = .suN := by
  have hrk : compRank (componentRoots χ i) ≤ 2 := compRank_le_rank (componentRoots χ i)
  unfold twistKind
  split_ifs with h1 h2 h3 h4
  · exact Or.inl rfl
  · exfalso
    rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  · exfalso
    omega
  · exact Or.inr rfl
  · exact Or.inl rfl

end Kernel

end CFSG.LocalAnalysis.GLTheoremA
