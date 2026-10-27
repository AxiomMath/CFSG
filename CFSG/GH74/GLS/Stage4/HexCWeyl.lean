module

public import CFSG.GH74.GLS.Stage4.HexCData

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {root : ℤ → Subgroup G} {F : Type} [Field F]

theorem weyl_mem {n : G} (hn : ActsPos 6 root n (fun q => 4 - q)) {i : ℤ} (hi1 : 1 ≤ i)
    (hi5 : i ≤ 5) {x : G} (hx : x ∈ root i) : n * x * n⁻¹ ∈ root (6 - i) := by
  have h := hn (i - 1) x (by rw [Rt_of_lt (by omega) (by omega)]; simpa using hx)
  rwa [Rt_of_lt (p := 4 - (i - 1)) (by omega) (by omega), show 4 - (i - 1) + 1 = 6 - i by ring] at h

theorem weyl_coords (D : HexData root F) {n : G} (hn : ActsPos 6 root n (fun q => 4 - q)) :
    (∃ f : F → F, ∀ d, n * D.p1 d * n⁻¹ = D.p5 (f d)) ∧
      (∃ f : F → F, ∀ d, n * D.p5 d * n⁻¹ = D.p1 (f d)) ∧
      (∃ f : F → F, ∀ d, n * D.p2 d * n⁻¹ = D.p4 (f d)) ∧
      (∃ f : F → F, ∀ d, n * D.p4 d * n⁻¹ = D.p2 (f d)) := by
  have h1 : ∀ d, ∃ c, D.p5 c = n * D.p1 d * n⁻¹ := fun d =>
    D.p5_surj _ (by simpa using weyl_mem hn (i := 1) (by norm_num) (by norm_num) (D.p1_mem d))
  have h5 : ∀ d, ∃ c, D.p1 c = n * D.p5 d * n⁻¹ := fun d =>
    D.p1_surj _ (by simpa using weyl_mem hn (i := 5) (by norm_num) (by norm_num) (D.p5_mem d))
  have h2 : ∀ d, ∃ c, D.p4 c = n * D.p2 d * n⁻¹ := fun d =>
    D.p4_surj _ (by simpa using weyl_mem hn (i := 2) (by norm_num) (by norm_num) (D.p2_mem d))
  have h4 : ∀ d, ∃ c, D.p2 c = n * D.p4 d * n⁻¹ := fun d =>
    D.p2_surj _ (by simpa using weyl_mem hn (i := 4) (by norm_num) (by norm_num) (D.p4_mem d))
  choose f1 hf1 using h1
  choose f5 hf5 using h5
  choose f2 hf2 using h2
  choose f4 hf4 using h4
  exact ⟨⟨f1, fun d => (hf1 d).symm⟩, ⟨f5, fun d => (hf5 d).symm⟩, ⟨f2, fun d => (hf2 d).symm⟩,
    ⟨f4, fun d => (hf4 d).symm⟩⟩

theorem conj_add_of {p q : F → G} (hp : ∀ c d, p (c + d) = p c * p d)
    (hq : ∀ c d, q (c + d) = q c * q d) (hqi : Function.Injective q) {n : G} {f : F → F}
    (hf : ∀ d, n * p d * n⁻¹ = q (f d)) (d d' : F) : f (d + d') = f d + f d' := by
  apply hqi
  rw [hq, ← hf, ← hf, ← hf, hp]
  group

theorem weyl_sq (D : HexData root F) {n : G} (hn : n = D.φ (sl2W F)) : n * n = D.T (-1) := by
  rw [hn, ← map_mul, sl2W_mul_self, D.T_eq]

theorem sl2_BR : sl2W F * sl2U (1 : F) * (sl2W F)⁻¹ =
    (sl2U (1 : F))⁻¹ * sl2W F * (sl2U (1 : F))⁻¹ := by
  have h1 : sl2W F * sl2U (1 : F) = sl2L (-1) * sl2W F := sl2W_mul_sl2U 1
  have hinv : (sl2U (1 : F))⁻¹ = sl2U (-1) := by
    rw [inv_eq_iff_mul_eq_one, ← sl2U_add]; simp [sl2U_zero]
  have h2 : sl2U (-1 : F) * sl2W F * sl2U (-1) = sl2L (-1) := by
    apply sl2_ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hinv, h2, h1]; group

theorem weyl_BR (D : HexData root F) {n : G} (hn : n = D.φ (sl2W F)) :
    n * D.p6 1 * n⁻¹ = (D.p6 1)⁻¹ * n * (D.p6 1)⁻¹ := by
  have h := congrArg D.φ (sl2_BR (F := F))
  simpa [map_mul, map_inv, hn, D.p6_eq] using h

end CFSG.GH74.GLS.Stage4.Hex
