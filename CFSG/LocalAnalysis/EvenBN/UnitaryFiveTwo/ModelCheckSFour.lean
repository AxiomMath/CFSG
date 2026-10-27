module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckZ2
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix Certificates.U52Yamada

@[expose] def a₂Coord (M : Matrix (Fin 5) (Fin 5) F4) : Fin 2 → F4 := ![M 2 1, M 2 0]

theorem a₂Coord_mul {a b : SU52} (ha : a ∈ A₂sub) (hb : b ∈ A₂sub) :
    a₂Coord (mat (a * b)) = a₂Coord (mat a) + a₂Coord (mat b) := by
  obtain ⟨haS, -⟩ := mem_A₂sub.1 ha
  obtain ⟨hbS, hb0⟩ := mem_A₂sub.1 hb
  funext i
  fin_cases i
  · change mat (a * b) 2 1 = mat a 2 1 + mat b 2 1
    exact mat_mul_two_one haS hbS
  · change mat (a * b) 2 0 = mat a 2 0 + mat b 2 0
    rw [mat_mul_two_zero haS hbS, hb0, mul_zero, add_zero]

theorem mem_Fsub_iff_a₂Coord {a : SU52} (ha : a ∈ A₂sub) : a ∈ Fsub ↔ a₂Coord (mat a) = 0 := by
  obtain ⟨haS, h10⟩ := mem_A₂sub.1 ha
  rw [mem_Fsub]
  constructor
  · rintro ⟨-, h21, -, h20⟩
    funext i
    fin_cases i
    · exact h21
    · exact h20
  · intro h
    exact ⟨haS, congrFun h 0, h10, congrFun h 1⟩

theorem a₂Coord_one : a₂Coord (1 : Matrix (Fin 5) (Fin 5) F4) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem inv_mul_mem_Fsub_iff_a₂Coord {a a' : SU52} (ha : a ∈ A₂sub) (ha' : a' ∈ A₂sub) :
    a⁻¹ * a' ∈ Fsub ↔ a₂Coord (mat a) = a₂Coord (mat a') := by
  have hinv : a₂Coord (mat a⁻¹) = -a₂Coord (mat a) := by
    have := a₂Coord_mul (inv_mem ha) ha
    rw [inv_mul_cancel, mat_one, a₂Coord_one] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  rw [mem_Fsub_iff_a₂Coord (mul_mem (inv_mem ha) ha'), a₂Coord_mul (inv_mem ha) ha', hinv,
    neg_add_eq_zero]

@[expose] def nfA₂ (c : Fin 2 → F4) : SU52 :=
  x₁SU (c 0) (c 0 * bar (c 0) * F4.ω) (valid_mul_omega (c 0)) *
    x₄SU (c 1) (c 1 * bar (c 1) * F4.ω) (valid_mul_omega (c 1))

theorem nfA₂_mem (c : Fin 2 → F4) : nfA₂ c ∈ A₂sub :=
  mul_mem (X₁sub_le_A₂sub (x₁SU_mem _ _ _)) (X₄sub_le_A₂sub (x₄SU_mem _ _ _))

theorem a₂Coord_nfA₂ (c : Fin 2 → F4) : a₂Coord (mat (nfA₂ c)) = c := by
  rw [nfA₂, mat_mul, mat_x₁SU, mat_x₄SU]
  funext i
  fin_cases i <;> simp [a₂Coord, x₁Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem mat_inv_vSU : mat vSU⁻¹ = vMat := mat_inv_eq (by rw [mat_vSU]; decide)

theorem vMat_conj_apply (M : Matrix (Fin 5) (Fin 5) F4) (i j : Fin 5) :
    (vMat * M * vMat) i j = M (![1, 0, 2, 4, 3] i) (![1, 0, 2, 4, 3] j) := by
  fin_cases i <;> fin_cases j <;>
    simp [vMat, Matrix.mul_apply, Fin.sum_univ_five, Matrix.vecMul, dotProduct]

theorem vSU_conj_mem_A₂sub {a : SU52} (ha : a ∈ A₂sub) : vSU * a * vSU⁻¹ ∈ A₂sub := by
  obtain ⟨haS, h10⟩ := mem_A₂sub.1 ha
  obtain ⟨hl, hd⟩ := mem_Ssub.1 haS
  have h43 : mat a 4 3 = 0 := by rw [mat_four_three haS, h10, map_zero]
  have hm : mat (vSU * a * vSU⁻¹) = vMat * mat a * vMat := by
    rw [mat_mul, mat_mul, mat_vSU, mat_inv_vSU]
  refine mem_A₂sub.2 ⟨mem_Ssub.2 ⟨fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · rw [hm, vMat_conj_apply]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first | exact h10 | exact h43 | exact hl _ _ (by decide)
  · rw [hm, vMat_conj_apply]
    fin_cases i <;> exact hd _
  · rw [hm, vMat_conj_apply]
    exact hl 0 1 (by decide)

theorem K₂sub_le_normalizer_A₂sub : K₂sub ≤ normalizer (A₂sub : Set SU52) :=
  sup_le (fun _ hx => mem_normalizer_fintype fun _ ha => Ssub_conj_mem_A₂sub
      (X₂sub_le_Ssub hx) ha)
    (zpowers_le.2 (mem_normalizer_fintype fun _ ha => vSU_conj_mem_A₂sub ha))

@[expose] def k2Gen : Fin 3 → SU52 := ![x₂SU 1, x₂SU F4.ω, vSU]

@[expose] def k2Mat : Fin 3 → Matrix (Fin 2) (Fin 2) F4 :=
  ![!![1, 0; 1, 1], !![1, 0; F4.ω, 1], !![0, 1; 1, 0]]

theorem k2Gen_mem (i : Fin 3) : k2Gen i ∈ K₂sub := by
  fin_cases i
  · exact mem_sup_left (x₂SU_mem 1)
  · exact mem_sup_left (x₂SU_mem F4.ω)
  · exact mem_sup_right (mem_zpowers vSU)

theorem a₂Coord_conj_x₂SU (γ : F4) (a : SU52) :
    a₂Coord (mat (x₂SU γ * a * (x₂SU γ)⁻¹)) =
      ![a₂Coord (mat a) 0, a₂Coord (mat a) 1 + γ * a₂Coord (mat a) 0] := by
  rw [mat_mul, mat_mul, mat_inv_of_x₂ (mat_x₂SU γ), mat_x₂SU]
  funext i
  fin_cases i
  · simp [a₂Coord, x₂Mat, Matrix.mul_apply, Fin.sum_univ_five, Matrix.vecMul, dotProduct]
  · simp [a₂Coord, x₂Mat, Matrix.mul_apply, Fin.sum_univ_five, Matrix.vecMul, dotProduct]
    ring

theorem a₂Coord_conj_vSU (a : SU52) :
    a₂Coord (mat (vSU * a * vSU⁻¹)) = ![a₂Coord (mat a) 1, a₂Coord (mat a) 0] := by
  have hm : mat (vSU * a * vSU⁻¹) = vMat * mat a * vMat := by
    rw [mat_mul, mat_mul, mat_vSU, mat_inv_vSU]
  rw [hm]
  funext i
  fin_cases i <;> simp [a₂Coord, vMat_conj_apply]

theorem k2Gen_conj (i : Fin 3) {a : SU52} (ha : a ∈ A₂sub) :
    k2Gen i * a * (k2Gen i)⁻¹ ∈ A₂sub ∧
      a₂Coord (mat (k2Gen i * a * (k2Gen i)⁻¹)) = (k2Mat i).mulVec (a₂Coord (mat a)) := by
  refine ⟨(mem_normalizer_iff.1 (K₂sub_le_normalizer_A₂sub (k2Gen_mem i)) a).1 ha, ?_⟩
  fin_cases i
  · change a₂Coord (mat (x₂SU 1 * a * (x₂SU 1)⁻¹)) = _
    rw [a₂Coord_conj_x₂SU]
    funext j
    fin_cases j
    · simp [k2Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [k2Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
  · change a₂Coord (mat (x₂SU F4.ω * a * (x₂SU F4.ω)⁻¹)) = _
    rw [a₂Coord_conj_x₂SU]
    funext j
    fin_cases j
    · simp [k2Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [k2Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
  · change a₂Coord (mat (vSU * a * vSU⁻¹)) = _
    rw [a₂Coord_conj_vSU]
    funext j
    fin_cases j <;> simp [k2Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[expose] def k2Word (w : List (Fin 3)) : SU52 := (w.map k2Gen).prod

@[expose] def k2WordMat (w : List (Fin 3)) : Matrix (Fin 2) (Fin 2) F4 := (w.map k2Mat).prod

theorem k2Word_mem (w : List (Fin 3)) : k2Word w ∈ K₂sub := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact k2Gen_mem i

theorem k2WordMat_append (w w' : List (Fin 3)) :
    k2WordMat (w ++ w') = k2WordMat w * k2WordMat w' := by
  rw [k2WordMat, k2WordMat, k2WordMat, List.map_append, List.prod_append]

theorem k2Word_conj (w : List (Fin 3)) {a : SU52} (ha : a ∈ A₂sub) :
    k2Word w * a * (k2Word w)⁻¹ ∈ A₂sub ∧
      a₂Coord (mat (k2Word w * a * (k2Word w)⁻¹)) = (k2WordMat w).mulVec (a₂Coord (mat a)) := by
  induction w with
  | nil =>
    refine ⟨by simpa [k2Word] using ha, ?_⟩
    simp [k2Word, k2WordMat]
  | cons i w ih =>
    have e : k2Word (i :: w) * a * (k2Word (i :: w))⁻¹ =
        k2Gen i * (k2Word w * a * (k2Word w)⁻¹) * (k2Gen i)⁻¹ := by
      change (k2Gen i * k2Word w) * a * (k2Gen i * k2Word w)⁻¹ = _
      group
    obtain ⟨h1, h2⟩ := k2Gen_conj i ih.1
    refine ⟨e ▸ h1, ?_⟩
    rw [e, h2, ih.2]
    change (k2Mat i).mulVec ((k2WordMat w).mulVec _) = (k2Mat i * k2WordMat w).mulVec _
    rw [Matrix.mulVec_mulVec]

@[expose] def toBaseWords : List (List (Fin 3)) :=
  [[2], [1, 2, 1, 0, 2], [1, 0, 2, 1, 2], [], [0], [1], [1, 0], [1, 2, 1, 0], [1, 2], [1, 2, 1],
    [1, 2, 0], [1, 0, 2, 1], [1, 0, 2], [1, 0, 2, 0], [1, 0, 2, 1, 0]]

@[expose] def fromBaseWords : List (List (Fin 3)) :=
  [[2], [2, 1, 0, 2, 1], [2, 1, 2, 1, 0], [], [0], [1], [1, 0], [1, 0, 2, 1], [2, 1], [1, 2, 1],
    [0, 2, 1], [1, 2, 1, 0], [2, 1, 0], [0, 2, 1, 0], [1, 0, 2, 1, 0]]

theorem toBase_check : ∀ c : Fin 2 → F4, c ≠ 0 →
    ∃ w ∈ toBaseWords, (k2WordMat w).mulVec c = ![1, 0] := by
  unfold toBaseWords k2WordMat k2Mat
  decide

theorem fromBase_check : ∀ c : Fin 2 → F4, c ≠ 0 →
    ∃ w ∈ fromBaseWords, (k2WordMat w).mulVec ![1, 0] = c := by
  unfold fromBaseWords k2WordMat k2Mat
  decide

theorem exists_K₂sub_conj_mem {a a' : SU52} (ha : a ∈ A₂sub) (haF : a ∉ Fsub)
    (ha' : a' ∈ A₂sub) (ha'F : a' ∉ Fsub) :
    ∃ n ∈ K₂sub, a'⁻¹ * (n * a * n⁻¹) ∈ Fsub := by
  have hc : a₂Coord (mat a) ≠ 0 := fun h => haF ((mem_Fsub_iff_a₂Coord ha).2 h)
  have hc' : a₂Coord (mat a') ≠ 0 := fun h => ha'F ((mem_Fsub_iff_a₂Coord ha').2 h)
  obtain ⟨w₁, -, hw₁⟩ := toBase_check _ hc
  obtain ⟨w₂, -, hw₂⟩ := fromBase_check _ hc'
  obtain ⟨hmem, hcoord⟩ := k2Word_conj (w₂ ++ w₁) ha
  refine ⟨k2Word (w₂ ++ w₁), k2Word_mem _, (inv_mul_mem_Fsub_iff_a₂Coord ha' hmem).2 ?_⟩
  rw [hcoord, k2WordMat_append, ← Matrix.mulVec_mulVec, hw₁, hw₂]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
