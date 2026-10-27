module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSevenFrame
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSevenHom
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSevenRefl
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace OmSeven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] noncomputable def pairRot (Q : QuadraticForm K V) (x y : V) : V ≃ₗ[K] V :=
  reflect Q x * reflect Q y

theorem pairRot_mem_orthogonalGroup (Q : QuadraticForm K V) (x y : V) :
    pairRot Q x y ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (reflect_mem_orthogonalGroup Q x) (reflect_mem_orthogonalGroup Q y)

theorem reflect_apply_left {Q : QuadraticForm K V} {x y : V} (hxy : Q x = Q y)
    (hB : polar Q x y = Q y) (hy : Q y ≠ 0) : reflect Q x y = y - x := by
  have hx : Q x ≠ 0 := hxy ▸ hy
  rw [reflect_apply hx, hB, ← hxy, div_self hx, one_smul]

theorem reflect_apply_right {Q : QuadraticForm K V} {x y : V} (hB : polar Q x y = Q y)
    (hy : Q y ≠ 0) : reflect Q y x = x - y := by
  rw [reflect_apply hy, polar_comm, hB, div_self hy, one_smul]

theorem pairRot_pow_three {Q : QuadraticForm K V} {x y : V} (hxy : Q x = Q y)
    (hB : polar Q x y = Q y) (hy : Q y ≠ 0) : pairRot Q x y ^ 3 = 1 :=
  reflect_mul_reflect_pow_three hxy hB hy

theorem pairRot_apply_y {Q : QuadraticForm K V} {x y : V} (hxy : Q x = Q y)
    (hB : polar Q x y = Q y) (hy : Q y ≠ 0) : pairRot Q x y y = x - y := by
  rw [pairRot, LinearEquiv.mul_apply, reflect_apply_vec_self hy, map_neg,
    reflect_apply_left hxy hB hy]
  abel

theorem pairRot_apply_of_polar_eq_zero {Q : QuadraticForm K V} {x y w : V}
    (hx : polar Q x w = 0) (hy : polar Q y w = 0) : pairRot Q x y w = w := by
  rw [pairRot, LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero hy,
    reflect_apply_of_polar_eq_zero hx]

theorem commute_pairRot {Q : QuadraticForm K V} {x y x' y' : V} (h1 : polar Q x x' = 0)
    (h2 : polar Q x y' = 0) (h3 : polar Q y x' = 0) (h4 : polar Q y y' = 0) :
    Commute (pairRot Q x y) (pairRot Q x' y') := by
  have c : ∀ {a b : V}, polar Q a b = 0 → Commute (reflect Q a) (reflect Q b) :=
    fun h => reflect_mul_comm_of_polar_eq_zero h
  exact ((c h1).mul_right (c h2)).mul_left ((c h3).mul_right (c h4))

theorem commute_pairRot_of_goodPair {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x y : V} (hxy : GoodPair Q g x y) :
    Commute g (pairRot Q x y) := by
  obtain ⟨hQe, hB, hy, h⟩ := hxy
  have hconj : g * pairRot Q x y * g⁻¹ = reflect Q (g x) * reflect Q (g y) := by
    simp only [pairRot, mul_assoc, ← reflect_conj hg]
    group
  have key : g * pairRot Q x y * g⁻¹ = pairRot Q x y := by
    rw [hconj]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      rfl
    · rw [h1, h2, reflect_neg_vec]
      have h5 := reflect_conj (reflect_mem_orthogonalGroup Q y) (x - y)
      have h6 : reflect Q y (x - y) = x := by
        rw [map_sub, reflect_apply_right hB hy, reflect_apply_vec_self hy]
        abel
      rw [reflect_inv, h6] at h5
      calc reflect Q y * reflect Q (x - y) = reflect Q y * reflect Q (x - y) * reflect Q y *
            reflect Q y := by rw [mul_assoc _ (reflect Q y) (reflect Q y), reflect_mul_self,
              mul_one]
        _ = reflect Q x * reflect Q y := by rw [h5]
  exact mul_inv_eq_iff_eq_mul.1 key

theorem pairRot_apply_y_ne {Q : QuadraticForm K V} {x y : V} (h3 : (3 : K) ≠ 0)
    (hxy : Q x = Q y) (hB : polar Q x y = Q y) (hy : Q y ≠ 0) : pairRot Q x y y ≠ y := by
  rw [pairRot_apply_y hxy hB hy]
  intro h
  have hx : x = (2 : K) • y := by
    rw [two_smul]
    exact (sub_eq_iff_eq_add.1 h)
  have h1 : Q x = 4 * Q y := by
    rw [hx, map_smul_eq_sq]
    norm_num
  rw [hxy] at h1
  apply hy
  have h4 : (3 : K) * Q y = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 h4).resolve_left h3

theorem exists_hom_triple [Finite K] (hK : Odd (Nat.card K)) (h3 : (3 : K) ≠ 0)
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 7 ≤ Module.finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1) :
    ∃ f : (Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) →*
        (V ≃ₗ[K] V), Function.Injective f ∧
      (∀ a, f a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧ ∀ a, Commute g (f a) := by
  obtain ⟨x, y, hgood, horth⟩ := exists_frame hK h3 3 V Q hQ (by omega) g hg hg3
  set u : Fin 3 → (V ≃ₗ[K] V) := fun i => pairRot Q (x i) (y i) with hu
  have hu3 : ∀ i, u i ^ 3 = 1 := fun i =>
    pairRot_pow_three (hgood i).1 (hgood i).2.1 (hgood i).2.2.1
  have huc : ∀ i j, Commute (u i) (u j) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨o1, o2, o3, o4⟩ := horth i j hij
      exact commute_pairRot o1 o2 o3 o4
  have hfix : ∀ i j, i ≠ j → u i • y j = y j := by
    intro i j hij
    obtain ⟨o1, o2, o3, o4⟩ := horth i j hij
    exact pairRot_apply_of_polar_eq_zero o2 o4
  have hmove : ∀ i, u i • y i ≠ y i := fun i =>
    pairRot_apply_y_ne h3 (hgood i).1 (hgood i).2.1 (hgood i).2.2.1
  have huO : ∀ i, u i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun i =>
    pairRot_mem_orthogonalGroup Q _ _
  have hug : ∀ i, Commute g (u i) := fun i => commute_pairRot_of_goodPair hg (hgood i)
  refine ⟨tripleHom u hu3 huc, tripleHom_injective u hu3 huc y hfix hmove, ?_, ?_⟩
  · rintro ⟨a, b, c⟩
    rw [tripleHom_apply]
    exact mul_mem (pow_mem (huO 0) _) (mul_mem (pow_mem (huO 1) _) (pow_mem (huO 2) _))
  · rintro ⟨a, b, c⟩
    rw [tripleHom_apply]
    exact ((hug 0).pow_right _).mul_right (((hug 1).pow_right _).mul_right ((hug 2).pow_right _))

end OmSeven

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
