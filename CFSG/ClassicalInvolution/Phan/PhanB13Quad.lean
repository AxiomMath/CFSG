module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Field
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.PhanB3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary

structure QData (F K : Type) [Field F] [Field K] [Algebra F K] (σ : K ≃+* K) where
  i : K
  hi : i * i = algebraMap F K (-1)
  re : K → F
  im : K → F
  decomp : ∀ z, z = algebraMap F K (re z) + algebraMap F K (im z) * i
  ind : ∀ a b : F, algebraMap F K a + algebraMap F K b * i = 0 → a = 0 ∧ b = 0
  σ_alg : ∀ a : F, σ (algebraMap F K a) = algebraMap F K a
  σ_i : σ i = -i

namespace QData

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ : K ≃+* K} (Q : QData F K σ)

theorem hi' : Q.i * Q.i = -1 := by rw [Q.hi]; simp

theorem re_im_eq {z : K} {a b : F} (h : z = algebraMap F K a + algebraMap F K b * Q.i) :
    Q.re z = a ∧ Q.im z = b := by
  have h1 := Q.decomp z
  have h2 : algebraMap F K (Q.re z - a) + algebraMap F K (Q.im z - b) * Q.i = 0 := by
    rw [map_sub, map_sub]
    linear_combination (-1 : K) * h1 + h
  obtain ⟨e1, e2⟩ := Q.ind _ _ h2
  exact ⟨sub_eq_zero.mp e1, sub_eq_zero.mp e2⟩

theorem re_add (z w : K) : Q.re (z + w) = Q.re z + Q.re w :=
  (Q.re_im_eq (a := Q.re z + Q.re w) (b := Q.im z + Q.im w)
    (by rw [map_add, map_add]; linear_combination Q.decomp z + Q.decomp w)).1

theorem im_add (z w : K) : Q.im (z + w) = Q.im z + Q.im w :=
  (Q.re_im_eq (a := Q.re z + Q.re w) (b := Q.im z + Q.im w)
    (by rw [map_add, map_add]; linear_combination Q.decomp z + Q.decomp w)).2

theorem re_neg (z : K) : Q.re (-z) = -Q.re z :=
  (Q.re_im_eq (a := -Q.re z) (b := -Q.im z)
    (by rw [map_neg, map_neg]; linear_combination -Q.decomp z)).1

theorem im_neg (z : K) : Q.im (-z) = -Q.im z :=
  (Q.re_im_eq (a := -Q.re z) (b := -Q.im z)
    (by rw [map_neg, map_neg]; linear_combination -Q.decomp z)).2

theorem re_sub (z w : K) : Q.re (z - w) = Q.re z - Q.re w := by
  rw [sub_eq_add_neg, Q.re_add, Q.re_neg, ← sub_eq_add_neg]

theorem im_sub (z w : K) : Q.im (z - w) = Q.im z - Q.im w := by
  rw [sub_eq_add_neg, Q.im_add, Q.im_neg, ← sub_eq_add_neg]

theorem mul_decomp (z w : K) : z * w =
    algebraMap F K (Q.re z * Q.re w - Q.im z * Q.im w) +
      algebraMap F K (Q.re z * Q.im w + Q.im z * Q.re w) * Q.i := by
  rw [map_sub, map_add, map_mul, map_mul, map_mul, map_mul]
  calc z * w = (algebraMap F K (Q.re z) + algebraMap F K (Q.im z) * Q.i) *
        (algebraMap F K (Q.re w) + algebraMap F K (Q.im w) * Q.i) := by
        rw [← Q.decomp z, ← Q.decomp w]
    _ = _ := by
        linear_combination (algebraMap F K (Q.im z) * algebraMap F K (Q.im w)) * Q.hi'

theorem re_mul (z w : K) : Q.re (z * w) = Q.re z * Q.re w - Q.im z * Q.im w :=
  (Q.re_im_eq (Q.mul_decomp z w)).1

theorem im_mul (z w : K) : Q.im (z * w) = Q.re z * Q.im w + Q.im z * Q.re w :=
  (Q.re_im_eq (Q.mul_decomp z w)).2

theorem re_alg (a : F) : Q.re (algebraMap F K a) = a :=
  (Q.re_im_eq (a := a) (b := 0) (by rw [map_zero]; ring)).1

theorem im_alg (a : F) : Q.im (algebraMap F K a) = 0 :=
  (Q.re_im_eq (a := a) (b := 0) (by rw [map_zero]; ring)).2

theorem re_i : Q.re Q.i = 0 :=
  (Q.re_im_eq (a := 0) (b := 1) (by rw [map_zero, map_one]; ring)).1

theorem im_i : Q.im Q.i = 1 :=
  (Q.re_im_eq (a := 0) (b := 1) (by rw [map_zero, map_one]; ring)).2

theorem re_one : Q.re 1 = 1 := by simpa using Q.re_alg 1

theorem im_one : Q.im 1 = 0 := by simpa using Q.im_alg 1

theorem re_zero : Q.re 0 = 0 := by simpa using Q.re_alg 0

theorem im_zero : Q.im 0 = 0 := by simpa using Q.im_alg 0

theorem σ_decomp (z : K) :
    σ z = algebraMap F K (Q.re z) + algebraMap F K (-Q.im z) * Q.i := by
  conv_lhs => rw [Q.decomp z]
  rw [map_add, map_mul, Q.σ_alg, Q.σ_alg, Q.σ_i, map_neg]
  ring

theorem re_σ (z : K) : Q.re (σ z) = Q.re z := (Q.re_im_eq (Q.σ_decomp z)).1

theorem im_σ (z : K) : Q.im (σ z) = -Q.im z := (Q.re_im_eq (Q.σ_decomp z)).2

theorem re_mul_σ (z : K) : Q.re (z * σ z) = Q.re z * Q.re z + Q.im z * Q.im z := by
  rw [Q.re_mul, Q.re_σ, Q.im_σ]; ring

theorem im_mul_σ (z : K) : Q.im (z * σ z) = 0 := by
  rw [Q.im_mul, Q.re_σ, Q.im_σ]; ring

def cpl (a b : F) : K := algebraMap F K a + algebraMap F K b * Q.i

theorem re_cpl (a b : F) : Q.re (Q.cpl a b) = a := (Q.re_im_eq rfl).1

theorem im_cpl (a b : F) : Q.im (Q.cpl a b) = b := (Q.re_im_eq rfl).2

theorem cpl_re_im (z : K) : Q.cpl (Q.re z) (Q.im z) = z := (Q.decomp z).symm

theorem re_inj {z w : K} (h1 : Q.re z = Q.re w) (h2 : Q.im z = Q.im w) : z = w := by
  rw [Q.decomp z, Q.decomp w, h1, h2]

theorem exists_of_card {p f : ℕ} [Fact p.Prime] {F K : Type} [Field F] [Finite F] [Field K]
    [Finite K] [CharP K p] [Algebra F K] (hF : Nat.card F = p ^ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hmod : p ^ f % 4 = 3) :
    Nonempty (QData F K (unitaryInvolution K p f)) := by
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact Nat.odd_iff.mpr (by omega)
  have E : QuadExt F K (unitaryInvolution K p f) := QuadExt.of_card hF hK hodd
  have : Fintype F := Fintype.ofFinite F
  have hnsq : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, not_not, ← Nat.card_eq_fintype_card, hF]
    exact hmod
  obtain ⟨r, hr⟩ := E.isSquare (-1)
  have hr' : r * r = algebraMap F K (-1) := hr.symm
  have hσ := E.sigma_eq_neg hnsq hr'
  have hne := not_mem_range_of_sq hnsq hr'
  have hli := linearIndependent_one_r hne
  let b := E.basisOneR hne
  have hb0 : b 0 = 1 := (E.basisOneR_apply hne 0).trans (by simp)
  have hb1 : b 1 = r := (E.basisOneR_apply hne 1).trans (by simp)
  refine ⟨⟨r, hr', fun z => b.repr z 0, fun z => b.repr z 1, fun z => ?_, ?_, E.fix, hσ⟩⟩
  · have h := b.sum_repr z
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
    exact h.symm
  · intro a c h
    rw [LinearIndependent.pair_iff] at hli
    exact hli a c (by simpa [Algebra.smul_def] using h)

end QData

end CFSG.ClassicalInvolution.PhanB3
