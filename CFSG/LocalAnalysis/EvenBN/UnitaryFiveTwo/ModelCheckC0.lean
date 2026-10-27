module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA2
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer
open scoped commutatorElement

theorem comm_three_shape {g : SU52}
    (h₁ : g * x₄SU 0 1 zero_one_rel = x₄SU 0 1 zero_one_rel * g)
    (h₂ : g * x₁SU 0 1 zero_one_rel = x₁SU 0 1 zero_one_rel * g) (h₃ : g * x₃SU 1 = x₃SU 1 * g) :
    (∀ i j : Fin 5, i < j → mat g i j = 0) ∧ mat g 1 1 = mat g 0 0 ∧ mat g 3 3 = mat g 0 0 ∧
      mat g 4 4 = mat g 0 0 ∧ mat g 1 0 = 0 := by
  have e1 : mat g * x₄Mat 0 1 = x₄Mat 0 1 * mat g := by
    have := congrArg mat h₁
    rwa [mat_mul, mat_mul, mat_x₄SU] at this
  have e2 : mat g * x₁Mat 0 1 = x₁Mat 0 1 * mat g := by
    have := congrArg mat h₂
    rwa [mat_mul, mat_mul, mat_x₁SU] at this
  have e3 : mat g * x₃Mat 1 = x₃Mat 1 * mat g := by
    have := congrArg mat h₃
    rwa [mat_mul, mat_mul, mat_x₃SU] at this
  have E1 : ∀ i j, (mat g * x₄Mat 0 1) i j = (x₄Mat 0 1 * mat g) i j := fun i j => by rw [e1]
  have E2 : ∀ i j, (mat g * x₁Mat 0 1) i j = (x₁Mat 0 1 * mat g) i j := fun i j => by rw [e2]
  have E3 : ∀ i j, (mat g * x₃Mat 1) i j = (x₃Mat 1 * mat g) i j := fun i j => by rw [e3]
  have c24 : mat g 2 4 = 0 := by simpa [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] using E1 2 0
  have c34 : mat g 3 4 = 0 := by simpa [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] using E1 3 0
  have c14 : mat g 1 4 = 0 := by simpa [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] using E1 1 0
  have c01 : mat g 0 1 = 0 := by simpa [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] using E1 4 1
  have c02 : mat g 0 2 = 0 := by simpa [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] using E1 4 2
  have c03 : mat g 0 3 = 0 := by simpa [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] using E1 4 3
  have c04 : mat g 0 4 = 0 := by simpa [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] using E1 4 4
  have c44 : mat g 4 4 = mat g 0 0 := by
    have := E1 4 0
    simp [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] at this
    linear_combination this
  have d23 : mat g 2 3 = 0 := by simpa [x₁Mat, Matrix.mul_apply, Fin.sum_univ_five] using E2 2 1
  have d10 : mat g 1 0 = 0 := by simpa [x₁Mat, Matrix.mul_apply, Fin.sum_univ_five] using E2 3 0
  have d12 : mat g 1 2 = 0 := by simpa [x₁Mat, Matrix.mul_apply, Fin.sum_univ_five] using E2 3 2
  have d13 : mat g 1 3 = 0 := by simpa [x₁Mat, Matrix.mul_apply, Fin.sum_univ_five] using E2 3 3
  have d33 : mat g 3 3 = mat g 1 1 := by
    have := E2 3 1
    simp [x₁Mat, Matrix.mul_apply, Fin.sum_univ_five] at this
    linear_combination this
  have f33 : mat g 3 3 = mat g 0 0 := by
    have := E3 3 0
    simp [x₃Mat, Matrix.mul_apply, Fin.sum_univ_five] at this
    linear_combination this
  refine ⟨fun i j hij => ?_, by rw [← d33, f33], f33, c44, d10⟩
  fin_cases i <;> fin_cases j <;> first
    | exact absurd hij (by decide)
    | assumption

theorem comm_Fsub_shape {g : SU52} (h : ∀ z ∈ Fsub, g * z = z * g) :
    (∀ i j : Fin 5, i < j → mat g i j = 0) ∧ mat g 1 1 = mat g 0 0 ∧ mat g 3 3 = mat g 0 0 ∧
      mat g 4 4 = mat g 0 0 ∧ mat g 1 0 = 0 :=
  comm_three_shape (h _ (x₄SU_zero_one_mem_Fsub zero_one_rel))
    (h _ (show x₁SU 0 1 zero_one_rel ∈ Fsub from genFSU_mem 0)) (h _ (x₃SU_mem_Fsub 1))

theorem e₂Mat_comm_genF (j : Fin 4) :
    e₂Mat * Certificates.U52Yamada.genF j = Certificates.U52Yamada.genF j * e₂Mat := by
  ext i k
  rw [e₂Mat, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp [Certificates.U52Yamada.genF, x₁Mat, x₃Mat, x₄Mat, mul_comm]

theorem e₂SU_comm_Fsub {z : SU52} (hz : z ∈ Fsub) : e₂SU * z = z * e₂SU := by
  have hgen : ∀ j, e₂SU * genFSU j = genFSU j * e₂SU := fun j =>
    ext_mat (by rw [mat_mul, mat_mul, mat_e₂SU, mat_genFSU, e₂Mat_comm_genF])
  have hle : closure (Set.range genFSU) ≤ (centralizer ({e₂SU} : Set SU52)) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    exact mem_centralizer_singleton_iff.2 (hgen j).symm
  rw [closure_genFSU] at hle
  exact (mem_centralizer_singleton_iff.1 (hle hz)).symm

theorem mat_mul_zero_zero {g h : SU52} (hg : ∀ i j : Fin 5, i < j → mat g i j = 0) :
    mat (g * h) 0 0 = mat g 0 0 * mat h 0 0 := by
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_five, hg 0 1 (by decide), hg 0 2 (by decide),
    hg 0 3 (by decide), hg 0 4 (by decide)]
  ring

theorem mat_e₂_mul_apply (x : SU52) (i j : Fin 5) :
    mat (e₂SU * x) i j = ![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] i * mat x i j := by
  rw [mat_mul, mat_e₂SU, e₂Mat, Matrix.diagonal_mul]

theorem mem_A₂sub_of_comm_Fsub_of_one {g : SU52} (h : ∀ z ∈ Fsub, g * z = z * g)
    (h1 : mat g 0 0 = 1) : g ∈ A₂sub := by
  obtain ⟨hlow, h11, h33, h44, h10⟩ := comm_Fsub_shape h
  have hdet0 := (mem_SU52.1 g.2).2
  change (mat g).det = 1 at hdet0
  rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => hlow i j hij), Fin.prod_univ_five]
    at hdet0
  have hdet : mat g 2 2 = 1 := by simpa [h11, h33, h44, h1] using hdet0
  refine mem_A₂sub.2 ⟨mem_Ssub.2 ⟨hlow, fun i => ?_⟩, h10⟩
  fin_cases i
  · exact h1
  · exact h11.trans h1
  · exact hdet
  · exact h33.trans h1
  · exact h44.trans h1

theorem mat_pow_zero_zero {g : SU52} (hlow : ∀ i j : Fin 5, i < j → mat g i j = 0) (n : ℕ) :
    mat (g ^ n) 0 0 = mat g 0 0 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]; rfl
  | succ n ih => rw [pow_succ', mat_mul_zero_zero hlow, ih, pow_succ']

theorem mat_e₂_pow_mul_zero_zero (k : ℕ) (g : SU52) :
    mat (e₂SU ^ k * g) 0 0 = F4.ω ^ k * mat g 0 0 := by
  induction k with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ', mul_assoc, mat_e₂_mul_apply, ih, pow_succ', mul_assoc]
    rfl

theorem exists_e₂_pow_mul_mem_A₂sub {g : SU52} (h : ∀ z ∈ Fsub, g * z = z * g) :
    ∃ k : ℕ, e₂SU ^ k * g ∈ A₂sub := by
  obtain ⟨hlow, h11, h33, h44, -⟩ := comm_Fsub_shape h
  have hdet := (mem_SU52.1 g.2).2
  change (mat g).det = 1 at hdet
  rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => hlow i j hij), Fin.prod_univ_five,
    h11, h33, h44] at hdet
  have hlam : ∀ x y : F4, x * x * y * x * x = 1 →
      x = 1 ∨ F4.ω ^ 2 * x = 1 ∨ F4.ω * x = 1 := by decide
  have hc : ∀ k : ℕ, ∀ z ∈ Fsub, e₂SU ^ k * g * z = z * (e₂SU ^ k * g) := by
    intro k z hz
    have hk : e₂SU ^ k * z = z * e₂SU ^ k := (Commute.pow_left (e₂SU_comm_Fsub hz) k).eq
    rw [mul_assoc, h z hz, ← mul_assoc, hk, mul_assoc]
  rcases hlam _ _ hdet with e | e | e
  · exact ⟨0, by rw [pow_zero, one_mul]; exact mem_A₂sub_of_comm_Fsub_of_one h e⟩
  · exact ⟨2, mem_A₂sub_of_comm_Fsub_of_one (hc 2) (by rw [mat_e₂_pow_mul_zero_zero]; exact e)⟩
  · exact ⟨1, mem_A₂sub_of_comm_Fsub_of_one (hc 1) (by
      rw [mat_e₂_pow_mul_zero_zero, pow_one]; exact e)⟩

theorem mem_A₂sub_of_comm_Fsub_of_pow {g : SU52} (h : ∀ z ∈ Fsub, g * z = z * g) {j : ℕ}
    (hj : g ^ 2 ^ j = 1) : g ∈ A₂sub := by
  obtain ⟨hlow, h11, h33, h44, -⟩ := comm_Fsub_shape h
  refine mem_A₂sub_of_comm_Fsub_of_one h ?_
  have hp := mat_pow_zero_zero hlow (2 ^ j)
  rw [hj, mat_one] at hp
  have hdet := (mem_SU52.1 g.2).2
  change (mat g).det = 1 at hdet
  rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => hlow i j hij), Fin.prod_univ_five,
    h11, h33, h44] at hdet
  have hne : mat g 0 0 ≠ 0 := fun e => by rw [e] at hdet; simp at hdet
  have h3 : mat g 0 0 ^ 3 = 1 := by
    have : ∀ x : F4, x ≠ 0 → x ^ 3 = 1 := by decide
    exact this _ hne
  have hord : orderOf (mat g 0 0) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hord2 : orderOf (mat g 0 0) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one (by
    change (1 : Matrix (Fin 5) (Fin 5) F4) 0 0 = mat g 0 0 ^ 2 ^ j at hp
    rw [← hp]; rfl)
  have h1 : orderOf (mat g 0 0) = 1 := by
    have hc : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
    exact Nat.dvd_one.1 (hc ▸ Nat.dvd_gcd hord hord2)
  exact orderOf_eq_one_iff.1 h1

theorem Ssub_conj_mem_A₂sub {s a : SU52} (hs : s ∈ Ssub) (ha : a ∈ A₂sub) :
    s * a * s⁻¹ ∈ A₂sub := by
  obtain ⟨haS, ha0⟩ := mem_A₂sub.1 ha
  refine mem_A₂sub.2 ⟨mul_mem (mul_mem hs haS) (inv_mem hs), ?_⟩
  have hinv : mat s⁻¹ 1 0 = -mat s 1 0 := by
    have := mat_mul_one_zero hs (inv_mem hs)
    rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)] at this
    linear_combination -this
  rw [mat_mul_one_zero (mul_mem hs haS) (inv_mem hs), mat_mul_one_zero hs haS, ha0, hinv]
  ring

theorem e₂_conj_x₁Mat (a b : F4) : e₂Mat * x₁Mat a b = x₁Mat (F4.ω * a) b * e₂Mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e₂Mat, x₁Mat, Matrix.mul_apply, Matrix.diagonal, bar_apply] <;>
    revert a b <;> decide

theorem e₂_conj_x₄Mat (a b : F4) : e₂Mat * x₄Mat a b = x₄Mat (F4.ω * a) b * e₂Mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e₂Mat, x₄Mat, Matrix.mul_apply, Matrix.diagonal, bar_apply] <;>
    revert a b <;> decide

theorem mat_e₂_conj_x₁ {x : SU52} {a b : F4} (hx : mat x = x₁Mat a b) :
    mat (e₂SU * x * e₂SU⁻¹) = x₁Mat (F4.ω * a) b := by
  rw [mat_mul, mat_mul, mat_e₂SU, hx, e₂_conj_x₁Mat, Matrix.mul_assoc, ← mat_e₂SU, ← mat_mul,
    mul_inv_cancel, mat_one, Matrix.mul_one]

theorem mat_e₂_conj_x₄ {x : SU52} {a b : F4} (hx : mat x = x₄Mat a b) :
    mat (e₂SU * x * e₂SU⁻¹) = x₄Mat (F4.ω * a) b := by
  rw [mat_mul, mat_mul, mat_e₂SU, hx, e₂_conj_x₄Mat, Matrix.mul_assoc, ← mat_e₂SU, ← mat_mul,
    mul_inv_cancel, mat_one, Matrix.mul_one]

theorem exists_valid (a : F4) : ∃ b : F4, a * bar a = b + bar b := by
  revert a
  simp only [bar_apply]
  decide

theorem F4_eq_of_add_eq_zero : ∀ a b : F4, 0 = a + b → b = a := by decide

theorem omega_mul_add (c : F4) : F4.ω * (F4.ω * c) + F4.ω * c = c := by
  revert c
  decide

theorem exists_commutator_e₂_x₁ {g : SU52} (hg : g ∈ X₁sub) :
    ∃ x ∈ X₁sub, ⁅e₂SU, x⁆⁻¹ * g ∈ Fsub := by
  obtain ⟨c, d, hcd⟩ := mem_X₁sub.1 hg
  obtain ⟨b, hb⟩ := exists_valid (F4.ω * c)
  set x := x₁SU (F4.ω * c) b hb with hx
  have hxm : mat x = x₁Mat (F4.ω * c) b := rfl
  refine ⟨x, x₁SU_mem _ _ _, ?_⟩
  have hcx : e₂SU * x * e₂SU⁻¹ ∈ X₁sub := mem_X₁sub.2 ⟨_, _, mat_e₂_conj_x₁ hxm⟩
  have hk : ⁅e₂SU, x⁆ ∈ X₁sub := by
    rw [commutatorElement_def]
    exact mul_mem hcx (inv_mem (x₁SU_mem _ _ _))
  have hX₁S : ∀ y ∈ X₁sub, y ∈ Ssub := fun y hy =>
    mem_sup_left (mem_sup_left (mem_sup_left hy))
  have hk21 : mat ⁅e₂SU, x⁆ 2 1 = c := by
    rw [commutatorElement_def, mat_mul_two_one (hX₁S _ hcx) (hX₁S _ (inv_mem (x₁SU_mem _ _ _))),
      mat_e₂_conj_x₁ hxm, mat_inv_of_x₁ hxm]
    exact omega_mul_add c
  have hinv : mat ⁅e₂SU, x⁆⁻¹ 2 1 = c := by
    have := mat_mul_two_one (hX₁S _ hk) (hX₁S _ (inv_mem hk))
    rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide), hk21] at this
    exact F4_eq_of_add_eq_zero _ _ this
  have hmem : ⁅e₂SU, x⁆⁻¹ * g ∈ X₁sub := mul_mem (inv_mem hk) hg
  obtain ⟨a', b', hm⟩ := mem_X₁sub.1 hmem
  have ha' : a' = 0 := by
    have := mat_mul_two_one (hX₁S _ (inv_mem hk)) (hX₁S _ hg)
    rw [hm, x₁Mat_apply_two_one, hinv, hcd, x₁Mat_apply_two_one] at this
    rw [this]
    exact CharTwo.add_self_eq_zero c
  subst ha'
  exact mem_sup_left (mem_sup_left ⟨0, b', rfl, hm⟩)

theorem exists_commutator_e₂_x₄ {g : SU52} (hg : g ∈ X₄sub) :
    ∃ x ∈ X₄sub, ⁅e₂SU, x⁆⁻¹ * g ∈ Fsub := by
  obtain ⟨c, d, hcd⟩ := mem_X₄sub.1 hg
  obtain ⟨b, hb⟩ := exists_valid (F4.ω * c)
  set x := x₄SU (F4.ω * c) b hb with hx
  have hxm : mat x = x₄Mat (F4.ω * c) b := rfl
  refine ⟨x, x₄SU_mem _ _ _, ?_⟩
  have hcx : e₂SU * x * e₂SU⁻¹ ∈ X₄sub := mem_X₄sub.2 ⟨_, _, mat_e₂_conj_x₄ hxm⟩
  have hk : ⁅e₂SU, x⁆ ∈ X₄sub := by
    rw [commutatorElement_def]
    exact mul_mem hcx (inv_mem (x₄SU_mem _ _ _))
  have hX₄S : ∀ y ∈ X₄sub, y ∈ Ssub := fun y hy => mem_sup_right hy
  have h21 : ∀ y ∈ X₄sub, mat y 2 1 = 0 := fun y hy => by
    obtain ⟨a, b, h⟩ := mem_X₄sub.1 hy
    rw [h]
    rfl
  have h10 : ∀ y ∈ X₄sub, mat y 1 0 = 0 := fun y hy => by
    obtain ⟨a, b, h⟩ := mem_X₄sub.1 hy
    rw [h]
    rfl
  have hadd : ∀ y ∈ X₄sub, ∀ y' ∈ X₄sub, mat (y * y') 2 0 = mat y 2 0 + mat y' 2 0 := by
    intro y hy y' hy'
    rw [mat_mul_two_zero (hX₄S _ hy) (hX₄S _ hy'), h21 y hy, zero_mul, add_zero]
  have hk20 : mat ⁅e₂SU, x⁆ 2 0 = c := by
    rw [commutatorElement_def, hadd _ hcx _ (inv_mem (x₄SU_mem _ _ _)), mat_e₂_conj_x₄ hxm,
      mat_inv_of_x₄ hxm]
    exact omega_mul_add c
  have hinv : mat ⁅e₂SU, x⁆⁻¹ 2 0 = c := by
    have := hadd _ hk _ (inv_mem hk)
    rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide), hk20] at this
    exact F4_eq_of_add_eq_zero _ _ this
  have hmem : ⁅e₂SU, x⁆⁻¹ * g ∈ X₄sub := mul_mem (inv_mem hk) hg
  obtain ⟨a', b', hm⟩ := mem_X₄sub.1 hmem
  have ha' : a' = 0 := by
    have := hadd _ (inv_mem hk) _ hg
    rw [hm, x₄Mat_apply_two_zero, hinv, hcd, x₄Mat_apply_two_zero] at this
    rw [this]
    exact CharTwo.add_self_eq_zero c
  subst ha'
  exact mem_sup_right ⟨0, b', rfl, hm⟩

theorem A₂sub_le_commutator :
    A₂sub ≤ ⁅zpowers e₂SU ⊔ A₂sub, zpowers e₂SU ⊔ A₂sub⁆ := by
  set E := zpowers e₂SU ⊔ A₂sub with hE
  have he₂ : e₂SU ∈ E := mem_sup_left (mem_zpowers _)
  have hA : A₂sub ≤ E := le_sup_right
  have hF : Fsub ≤ ⁅E, E⁆ := by
    rw [← closure_genFSU, closure_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha, b, hb, e⟩ := exists_genFSU_eq_commutator j
    rw [e]
    exact commutator_mem_commutator (hA ha) (hA hb)
  have hX₁ : X₁sub ≤ ⁅E, E⁆ := fun g hg => by
    obtain ⟨x, hx, hz⟩ := exists_commutator_e₂_x₁ hg
    have : g = ⁅e₂SU, x⁆ * (⁅e₂SU, x⁆⁻¹ * g) := by group
    rw [this]
    exact mul_mem (commutator_mem_commutator he₂ (hA (X₁sub_le_A₂sub hx))) (hF hz)
  have hX₄ : X₄sub ≤ ⁅E, E⁆ := fun g hg => by
    obtain ⟨x, hx, hz⟩ := exists_commutator_e₂_x₄ hg
    have : g = ⁅e₂SU, x⁆ * (⁅e₂SU, x⁆⁻¹ * g) := by group
    rw [this]
    exact mul_mem (commutator_mem_commutator he₂ (hA (X₄sub_le_A₂sub hx))) (hF hz)
  have hX₃ : X₃sub ≤ ⁅E, E⁆ := fun g hg => hF (mem_sup_left (mem_sup_right hg))
  exact sup_le (sup_le hX₁ hX₃) hX₄

theorem commutator_mem_A₂sub_of_comm_Fsub {g h : SU52} (hg : ∀ z ∈ Fsub, g * z = z * g)
    (hh : ∀ z ∈ Fsub, h * z = z * h) : ⁅g, h⁆ ∈ A₂sub := by
  have hinv : ∀ {x : SU52}, (∀ z ∈ Fsub, x * z = z * x) → ∀ z ∈ Fsub, x⁻¹ * z = z * x⁻¹ :=
    fun hx z hz => (Commute.inv_left (hx z hz : Commute _ _)).eq
  have hmul : ∀ {x y : SU52}, (∀ z ∈ Fsub, x * z = z * x) → (∀ z ∈ Fsub, y * z = z * y) →
      ∀ z ∈ Fsub, x * y * z = z * (x * y) := fun hx hy z hz => by
    rw [mul_assoc, hy z hz, ← mul_assoc, hx z hz, mul_assoc]
  have hc : ∀ z ∈ Fsub, ⁅g, h⁆ * z = z * ⁅g, h⁆ := by
    rw [commutatorElement_def]
    exact hmul (hmul (hmul hg hh) (hinv hg)) (hinv hh)
  refine mem_A₂sub_of_comm_Fsub_of_one hc ?_
  have hlow : ∀ {x : SU52}, (∀ z ∈ Fsub, x * z = z * x) → ∀ i j : Fin 5, i < j →
      mat x i j = 0 := fun hx => (comm_Fsub_shape hx).1
  have hlam : ∀ {x : SU52}, (∀ z ∈ Fsub, x * z = z * x) → mat x⁻¹ 0 0 * mat x 0 0 = 1 := by
    intro x hx
    rw [← mat_mul_zero_zero (hlow (hinv hx)), inv_mul_cancel, mat_one]
    rfl
  rw [commutatorElement_def, mat_mul_zero_zero (hlow (hmul (hmul hg hh) (hinv hg))),
    mat_mul_zero_zero (hlow (hmul hg hh)), mat_mul_zero_zero (hlow hg)]
  calc mat g 0 0 * mat h 0 0 * mat g⁻¹ 0 0 * mat h⁻¹ 0 0 =
      (mat g⁻¹ 0 0 * mat g 0 0) * (mat h⁻¹ 0 0 * mat h 0 0) := by ring
    _ = 1 := by rw [hlam hg, hlam hh, one_mul]

theorem mem_Fsub_of_comm_e₂ {a : SU52} (ha : a ∈ A₂sub) (h : e₂SU * a = a * e₂SU) :
    a ∈ Fsub := by
  have hd : ∀ i, (![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) i ≠ 0 := by
    rw [bar_apply]
    decide
  have hconj : e₂SU * a * e₂SU⁻¹ = a := by rw [h, mul_inv_cancel_right]
  have e21 := mat_conj_diag (x := a) hd (mat_e₂SU.trans rfl) 2 1
  have e20 := mat_conj_diag (x := a) hd (mat_e₂SU.trans rfl) 2 0
  rw [hconj] at e21 e20
  have key : ∀ x : F4, x = bar F4.ω * x * F4.ω⁻¹ → x = 0 := by
    rw [bar_apply]
    decide
  obtain ⟨haS, ha10⟩ := mem_A₂sub.1 ha
  exact mem_Fsub.2 ⟨haS, key _ e21, ha10, key _ e20⟩

theorem mat_zero_zero_ne_zero {g : SU52} (hlow : ∀ i j : Fin 5, i < j → mat g i j = 0) :
    mat g 0 0 ≠ 0 := fun e => by
  have hdet := (mem_SU52.1 g.2).2
  change (mat g).det = 1 at hdet
  rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => hlow i j hij), Fin.prod_univ_five, e]
    at hdet
  simp at hdet

theorem exists_conj_mul_fld_ne (s : SU52) : ∃ z ∈ Fsub, (MulAut.conj s * fld) z ≠ z := by
  refine by_contra fun hne => ?_
  have hcon : ∀ z ∈ Fsub, (MulAut.conj s * fld) z = z := fun z hz =>
    by_contra fun h => hne ⟨z, hz, h⟩
  have hfix : ∀ z ∈ Fsub, fld z = z → s * z = z * s := fun z hz hf => by
    have e := hcon z hz
    rw [MulAut.mul_apply, hf, MulAut.conj_apply] at e
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [e]
  obtain ⟨hlow, -, h33, -, -⟩ := comm_three_shape
    (hfix _ (x₄SU_zero_one_mem_Fsub zero_one_rel) fld_x₄SU_zero_one)
    (hfix _ (show x₁SU 0 1 zero_one_rel ∈ Fsub from genFSU_mem 0) fld_x₁SU_zero_one)
    (hfix _ (x₃SU_mem_Fsub 1) fld_x₃SU_one)
  have e := hcon _ (x₃SU_mem_Fsub F4.ω)
  rw [MulAut.mul_apply, fld_x₃SU, MulAut.conj_apply] at e
  have e' : mat s * x₃Mat (bar F4.ω) = x₃Mat F4.ω * mat s := by
    have := congrArg mat (show s * x₃SU (bar F4.ω) = x₃SU F4.ω * s by
      calc s * x₃SU (bar F4.ω) = s * x₃SU (bar F4.ω) * s⁻¹ * s := by group
        _ = x₃SU F4.ω * s := by rw [e])
    rwa [mat_mul, mat_mul, mat_x₃SU, mat_x₃SU] at this
  have e30 := congrFun (congrFun e' 3) 0
  simp [x₃Mat, Matrix.mul_apply, Fin.sum_univ_five] at e30
  have key : mat s 0 0 * (bar F4.ω - F4.ω) = 0 := by linear_combination e30 - bar F4.ω * h33
  have hω : bar F4.ω - F4.ω ≠ 0 := by
    rw [bar_apply]
    decide
  exact mat_zero_zero_ne_zero hlow ((mul_eq_zero.1 key).resolve_right hω)

theorem conj_mem_A₂sub_of_mem_normalizer {n a : SU52} (hn : n ∈ normalizer (Fsub : Set SU52))
    (ha : a ∈ A₂sub) : n * a * n⁻¹ ∈ A₂sub := by
  refine mem_A₂sub_of_comm_Fsub_of_pow (j := 8) (fun z hz => ?_) ?_
  · have hz' : n⁻¹ * z * n ∈ Fsub := by
      have := (mem_normalizer_iff.1 (inv_mem hn) z).1 hz
      simpa using this
    have e := Fsub_comm_A₂ ha hz'
    calc n * a * n⁻¹ * z = n * (a * (n⁻¹ * z * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * z * n) * a) * n⁻¹ := by rw [e]
      _ = z * (n * a * n⁻¹) := by group
  · have h8 : a ^ 2 ^ 8 = 1 := by
      have := congrArg Subtype.val (pow_card_eq_one' (G := A₂sub) (x := ⟨a, ha⟩))
      rwa [card_A₂sub] at this
    rw [conj_pow, h8, mul_one, mul_inv_cancel]

@[expose] def y₅SU : SU52 := x₂SU F4.ω * vSU

theorem y₅SU_mem_N0sub : y₅SU ∈ N0sub :=
  mul_mem (subset_closure ⟨4, rfl⟩) (subset_closure ⟨0, rfl⟩)

theorem orderOf_y₅SU : orderOf y₅SU = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (ext_mat ?_) fun h => ?_
  · have e : mat (y₅SU ^ 5) = (x₂Mat F4.ω * vMat) ^ 5 := by
      simp only [pow_succ, pow_zero, one_mul, mat_mul]
      rfl
    rw [e, mat_one]
    decide +kernel
  · have := congrFun (congrFun (congrArg mat h) 0) 0
    revert this
    change (x₂Mat F4.ω * vMat) 0 0 = (1 : Matrix (Fin 5) (Fin 5) F4) 0 0 → False
    decide +kernel

@[expose] noncomputable def levSU (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det) : SU52 :=
  ρ.symm (CFSG.RankThree.PartOne.U5K.Hyp.lev (hK := hF4) A hA)

theorem levSU_conj_mem_A₂sub (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det) {g : SU52}
    (hg : g ∈ A₂sub) : levSU A hA * g * (levSU A hA)⁻¹ ∈ A₂sub := by
  rw [mem_A₂sub_iff_ρ] at hg ⊢
  rw [map_mul, map_mul, map_inv, levSU, MulEquiv.apply_symm_apply]
  exact CFSG.RankThree.PartOne.U5K.Hyp.lev_conj_mem_Ssub A hA hg

theorem levSU_conj_mem_Fsub (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det) {g : SU52}
    (hg : g ∈ Fsub) : levSU A hA * g * (levSU A hA)⁻¹ ∈ Fsub := by
  rw [Fsub_eq_comap_Vsub] at hg ⊢
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hg ⊢
  rw [map_mul, map_mul, map_inv, levSU, MulEquiv.apply_symm_apply]
  exact CFSG.RankThree.PartOne.U5K.Hyp.lev_conj_mem_Vsub A hA hg

theorem eq_bot_or_eq_Fsub_or_eq_A₂sub {R : Subgroup SU52} (hR : R ≤ A₂sub)
    (hL : ∀ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det), ∀ r ∈ R,
      levSU A hA * r * (levSU A hA)⁻¹ ∈ R) :
    R = ⊥ ∨ R = Fsub ∨ R = A₂sub := by
  have hR' : R.map ρ.toMonoidHom ≤ CFSG.RankThree.PartOne.U5K.Hyp.Ssub hF4 := by
    rw [map_le_iff_le_comap, ← A₂sub_eq_comap_Ssub]
    exact hR
  have hL' : ∀ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det), ∀ r ∈ R.map ρ.toMonoidHom,
      CFSG.RankThree.PartOne.U5K.Hyp.lev A hA * r * (CFSG.RankThree.PartOne.U5K.Hyp.lev A hA)⁻¹ ∈
        R.map ρ.toMonoidHom := by
    rintro A hA _ ⟨r, hr, rfl⟩
    refine ⟨levSU A hA * r * (levSU A hA)⁻¹, hL A hA r hr, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv, levSU, MulEquiv.apply_symm_apply]
  have hc : ∀ R' : Subgroup _, R.map ρ.toMonoidHom = R' → R = R'.comap ρ.toMonoidHom :=
    fun R' e => by rw [← e, comap_map_eq_self_of_injective ρ.injective]
  rcases CFSG.RankThree.PartOne.U5K.Hyp.irreducible_Ssub hR' hL' with e | e | e
  · left
    rw [hc _ e, eq_bot_iff]
    intro g hg
    exact mem_bot.2 (ρ.injective (by rw [map_one]; exact mem_bot.1 (mem_comap.1 hg)))
  · right; left
    rw [hc _ e, ← Fsub_eq_comap_Vsub]
  · right; right
    rw [hc _ e, ← A₂sub_eq_comap_Ssub]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
