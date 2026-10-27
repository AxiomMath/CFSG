module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckS
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckAut
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

theorem lower_of_mem_normalizer_Ssub {s : SU52} (hs : s ∈ normalizer (Ssub : Set SU52)) :
    ∀ i j : Fin 5, i < j → mat s i j = 0 := by
  have hρ : ρ s ∈ normalizer (hypUnitriangular hF4 2 1 : Set (hypSU hF4 2 1)) := by
    refine mem_normalizer_iff.2 fun u => ?_
    obtain ⟨g, rfl⟩ := ρ.surjective u
    rw [← map_inv, ← map_mul, ← map_mul, ← mem_Ssub_iff_ρ, ← mem_Ssub_iff_ρ]
    exact mem_normalizer_iff.1 hs g
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular hF4
    (by norm_num) (by norm_num)] at hρ
  have hT := (mem_hypBorel_iff_blockTriangular hF4 (by norm_num) (ρ s)).1 hρ
  intro i j hij
  rw [← mat_ρ_apply]
  exact hT ((fullPos_yIdx_lt_iff i j).2 hij)

theorem DiagSub_le_normalizer_Ssub : DiagSub ≤ normalizer (Ssub : Set SU52) := by
  rintro g ⟨α, β, γ, hα, hβ, hγ, hgm⟩
  have hd : ∀ i, (![α, β, γ, β, α] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simpa
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨h1, h2⟩ := mem_Ssub.1 hx
  exact mem_Ssub.2 ⟨fun i j hij => by rw [mat_conj_diag hd hgm, h1 i j hij, mul_zero, zero_mul],
    fun i => by rw [mat_conj_diag hd hgm, h2 i, mul_one, mul_inv_cancel₀ (hd i)]⟩

theorem Esub_le_normalizer_Ssub : Esub ≤ normalizer (Ssub : Set SU52) :=
  Esub_le_DiagSub.trans DiagSub_le_normalizer_Ssub

theorem e₂SU_mem_normalizer_Ssub : e₂SU ∈ normalizer (Ssub : Set SU52) :=
  Esub_le_normalizer_Ssub (mem_sup_right (mem_zpowers _))

theorem mat_npow (g : SU52) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

@[expose] def eTorDiag (i j : Fin 3) : Fin 5 → F4 := fun k =>
  (![1, F4.ω, F4.ω, F4.ω, 1] : Fin 5 → F4) k ^ (i : ℕ) *
    (![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) k ^ (j : ℕ)

theorem mat_eTor (i j : Fin 3) :
    mat (e₁SU ^ (i : ℕ) * e₂SU ^ (j : ℕ)) = Matrix.diagonal (eTorDiag i j) := by
  rw [mat_mul, mat_npow, mat_npow, mat_e₁SU, mat_e₂SU, e₁Mat, e₂Mat, Matrix.diagonal_pow,
    Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]
  rfl

theorem eTor_mem_Esub (i j : Fin 3) : e₁SU ^ (i : ℕ) * e₂SU ^ (j : ℕ) ∈ Esub :=
  mul_mem (mem_sup_left (npow_mem_zpowers _ _)) (mem_sup_right (npow_mem_zpowers _ _))

theorem eTorDiag_ne_zero : ∀ i j k, eTorDiag i j k ≠ 0 := by
  unfold eTorDiag
  simp only [bar_apply]
  decide

theorem exists_eTorDiag : ∀ a b c d e : F4, bar a * e = 1 → bar b * d = 1 → bar c * c = 1 →
    a * b * c * d * e = 1 → ∃ i j : Fin 3, eTorDiag i j = ![a, b, c, d, e] := by
  unfold eTorDiag
  simp only [bar_apply]
  decide

theorem inv_mul_mem_Ssub_of_diag {t s : SU52} {d : Fin 5 → F4}
    (ht : mat t = Matrix.diagonal d) (hd0 : ∀ i, d i ≠ 0)
    (hs : ∀ i j : Fin 5, i < j → mat s i j = 0) (hd : ∀ i, mat s i i = d i) :
    t⁻¹ * s ∈ Ssub := by
  have hinv : mat t⁻¹ = Matrix.diagonal fun i => (d i)⁻¹ := mat_inv_eq (by
    rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd0 i))
  refine mem_Ssub.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [mat_mul, hinv, Matrix.diagonal_mul, hs i j hij, mul_zero]
  · rw [mat_mul, hinv, Matrix.diagonal_mul, hd i, inv_mul_cancel₀ (hd0 i)]

theorem diag_facts_of_lower {s : SU52} (hs : ∀ i j : Fin 5, i < j → mat s i j = 0) :
    bar (mat s 0 0) * mat s 4 4 = 1 ∧ bar (mat s 1 1) * mat s 3 3 = 1 ∧
      bar (mat s 2 2) * mat s 2 2 = 1 ∧
      mat s 0 0 * mat s 1 1 * mat s 2 2 * mat s 3 3 * mat s 4 4 = 1 := by
  obtain ⟨hU, hdet⟩ := mem_SU52.1 s.2
  have u01 := hs 0 1 (by decide)
  have u02 := hs 0 2 (by decide)
  have u03 := hs 0 3 (by decide)
  have u04 := hs 0 4 (by decide)
  have u12 := hs 1 2 (by decide)
  have u13 := hs 1 3 (by decide)
  have u14 := hs 1 4 (by decide)
  have u23 := hs 2 3 (by decide)
  have u24 := hs 2 4 (by decide)
  have u34 := hs 3 4 (by decide)
  have e04 := congrFun (congrFun hU 0) 4
  have e13 := congrFun (congrFun hU 1) 3
  have e22 := congrFun (congrFun hU 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_five, J5, u01, u02, u03, u04, u12, u13, u14, u23, u24,
    u34] at e04 e13 e22
  have hlt : (mat s).IsLowerTriangular := fun i j hij =>
    hs i j (OrderDual.toDual_lt_toDual.1 hij)
  have hdet' := Matrix.det_of_isLowerTriangular (mat s) hlt
  rw [hdet, Fin.prod_univ_five] at hdet'
  exact ⟨e04, e13, e22, hdet'.symm⟩

theorem exists_mul_of_mem_normalizer_Ssub {n : SU52} (hn : n ∈ normalizer (Ssub : Set SU52)) :
    ∃ i j : Fin 3, (e₁SU ^ (i : ℕ) * e₂SU ^ (j : ℕ))⁻¹ * n ∈ Ssub ∧
      ∀ k, mat n k k = eTorDiag i j k := by
  have hlow := lower_of_mem_normalizer_Ssub hn
  obtain ⟨h04, h13, h22, hdet⟩ := diag_facts_of_lower hlow
  obtain ⟨i, j, hij⟩ := exists_eTorDiag _ _ _ _ _ h04 h13 h22 hdet
  have hd : ∀ k, mat n k k = eTorDiag i j k := fun k => by
    rw [hij]
    fin_cases k <;> rfl
  exact ⟨i, j, inv_mul_mem_Ssub_of_diag (mat_eTor i j) (eTorDiag_ne_zero i j) hlow hd, hd⟩

theorem normalizer_Ssub : normalizer (Ssub : Set SU52) = Ssub ⊔ Esub := by
  refine le_antisymm (fun n hn => ?_) (sup_le le_normalizer Esub_le_normalizer_Ssub)
  obtain ⟨i, j, hu, -⟩ := exists_mul_of_mem_normalizer_Ssub hn
  have := mul_mem (mem_sup_right (eTor_mem_Esub i j)) (mem_sup_left hu)
  rwa [mul_inv_cancel_left] at this

theorem normalizer_Ssub_conj_mem_commutator {n x : SU52}
    (hn : n ∈ normalizer (Ssub : Set SU52)) (hx : x ∈ ⁅Ssub, Ssub⁆) :
    n * x * n⁻¹ ∈ ⁅Ssub, Ssub⁆ := by
  have hle : ⁅Ssub, Ssub⁆ ≤ (⁅Ssub, Ssub⁆ : Subgroup SU52).comap (MulAut.conj n).toMonoidHom := by
    rw [commutator_le]
    intro g hg h hh
    change n * ⁅g, h⁆ * n⁻¹ ∈ ⁅Ssub, Ssub⁆
    rw [show n * ⁅g, h⁆ * n⁻¹ = ⁅n * g * n⁻¹, n * h * n⁻¹⁆ by
      simp only [commutatorElement_def]
      group]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hn g).1 hg)
      ((mem_normalizer_iff.1 hn h).1 hh)
  exact hle hx

theorem normalizer_Ssub_conj_mem_Fsub {n f : SU52} (hn : n ∈ normalizer (Ssub : Set SU52))
    (hf : f ∈ Fsub) : n * f * n⁻¹ ∈ Fsub := by
  rw [← Ssub_inf_centralizer_commutator_Ssub] at hf ⊢
  obtain ⟨hfS, hfC⟩ := mem_inf.1 hf
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 hn f).1 hfS, mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : n⁻¹ * y * n ∈ ⁅Ssub, Ssub⁆ := by
    have := normalizer_Ssub_conj_mem_commutator (inv_mem hn) hy
    rwa [inv_inv] at this
  have hc := mem_centralizer_iff.1 hfC _ hy'
  calc y * (n * f * n⁻¹) = n * (n⁻¹ * y * n * f) * n⁻¹ := by group
    _ = n * (f * (n⁻¹ * y * n)) * n⁻¹ := by rw [hc]
    _ = n * f * n⁻¹ * y := by group

theorem mem_X₄sub_sup_Fsub_iff_mat {x : SU52} :
    x ∈ X₄sub ⊔ Fsub ↔ x ∈ Ssub ∧ mat x 2 1 = 0 ∧ mat x 1 0 = 0 := by
  rw [← commutator_Ssub_eq_X₄sub_sup_Fsub, commutator_Ssub, mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff]

theorem normalizer_Ssub_conj_mem_X₄sub_sup_Fsub {n x : SU52}
    (hn : n ∈ normalizer (Ssub : Set SU52)) (hx : x ∈ X₄sub ⊔ Fsub) :
    n * x * n⁻¹ ∈ X₄sub ⊔ Fsub := by
  rw [← commutator_Ssub_eq_X₄sub_sup_Fsub] at hx ⊢
  exact normalizer_Ssub_conj_mem_commutator hn hx

theorem inv_mul_mem_Fsub_iff_of_mem {x y : SU52} (hx : x ∈ X₄sub ⊔ Fsub)
    (hy : y ∈ X₄sub ⊔ Fsub) : x⁻¹ * y ∈ Fsub ↔ mat x 2 0 = mat y 2 0 := by
  have hxy : x⁻¹ * y ∈ X₄sub ⊔ Fsub := mul_mem (inv_mem hx) hy
  obtain ⟨hxyS, h21, h10⟩ := mem_X₄sub_sup_Fsub_iff_mat.1 hxy
  obtain ⟨hxS, x21, -⟩ := mem_X₄sub_sup_Fsub_iff_mat.1 hx
  obtain ⟨hyS, -, y10⟩ := mem_X₄sub_sup_Fsub_iff_mat.1 hy
  have hinv : mat x⁻¹ 2 0 = - mat x 2 0 := by
    have := mat_mul_two_zero hxS (inv_mem hxS)
    rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide), x21, zero_mul, add_zero] at this
    linear_combination -this
  have e : mat (x⁻¹ * y) 2 0 = mat y 2 0 - mat x 2 0 := by
    rw [mat_mul_two_zero (inv_mem hxS) hyS, y10, mul_zero, add_zero, hinv]
    ring
  rw [mem_Fsub, e, sub_eq_zero]
  exact ⟨fun h => h.2.2.2.symm, fun h => ⟨hxyS, h21, h10, h.symm⟩⟩

theorem mat_inv_zero_zero_mul {n : SU52} (hn : n ∈ normalizer (Ssub : Set SU52)) :
    mat n⁻¹ 0 0 * mat n 0 0 = 1 := by
  have hlow := lower_of_mem_normalizer_Ssub (inv_mem hn)
  have h : (mat n⁻¹ * mat n) 0 0 = 1 := by
    rw [← mat_mul, inv_mul_cancel, mat_one, Matrix.one_apply_eq]
  simp [Matrix.mul_apply, Fin.sum_univ_five, hlow 0 1 (by decide), hlow 0 2 (by decide),
    hlow 0 3 (by decide), hlow 0 4 (by decide)] at h
  exact h

theorem mat_conj_two_zero_of_mem_normalizer {n x : SU52}
    (hn : n ∈ normalizer (Ssub : Set SU52)) (hx : x ∈ X₄sub ⊔ Fsub) :
    mat (n * x * n⁻¹) 2 0 = mat n 2 2 * mat n⁻¹ 0 0 * mat x 2 0 := by
  have hlow := lower_of_mem_normalizer_Ssub hn
  obtain ⟨hxS, x21, x10⟩ := mem_X₄sub_sup_Fsub_iff_mat.1 hx
  obtain ⟨xl, xd⟩ := mem_Ssub.1 hxS
  have hnn : (mat n * mat n⁻¹) 2 0 = 0 := by
    rw [← mat_mul, mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)]
  have n23 := hlow 2 3 (by decide)
  have n24 := hlow 2 4 (by decide)
  have x01 := xl 0 1 (by decide)
  have x02 := xl 0 2 (by decide)
  have x03 := xl 0 3 (by decide)
  have x04 := xl 0 4 (by decide)
  have x12 := xl 1 2 (by decide)
  have x13 := xl 1 3 (by decide)
  have x14 := xl 1 4 (by decide)
  have x23 := xl 2 3 (by decide)
  have x24 := xl 2 4 (by decide)
  have x00 := xd 0
  have x11 := xd 1
  have x22 := xd 2
  rw [mat_mul, mat_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_five, n23, n24, x01, x02, x03, x04, x12, x13, x14, x23,
    x24, x00, x11, x22, x21, x10] at hnn ⊢
  linear_combination hnn

theorem mat_conj_e₂_two_zero (x : SU52) : mat (e₂SU * x * e₂SU⁻¹) 2 0 = F4.ω * mat x 2 0 := by
  have hd : ∀ i, (![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simp only [bar_apply] <;> decide
  rw [mat_conj_diag hd (by rw [mat_e₂SU, e₂Mat])]
  change bar F4.ω * mat x 2 0 * F4.ω⁻¹ = F4.ω * mat x 2 0
  have h : bar F4.ω * F4.ω⁻¹ = F4.ω := by
    rw [bar_apply]
    decide
  linear_combination mat x 2 0 * h

theorem mem_Fsub_of_conj_e₂ {x : SU52} (hx : x ∈ X₄sub ⊔ Fsub)
    (h : x⁻¹ * (e₂SU * x * e₂SU⁻¹) ∈ Fsub) : x ∈ Fsub := by
  have e := (inv_mul_mem_Fsub_iff_of_mem hx
    (normalizer_Ssub_conj_mem_X₄sub_sup_Fsub e₂SU_mem_normalizer_Ssub hx)).1 h
  rw [mat_conj_e₂_two_zero] at e
  have key : ∀ t : F4, t = F4.ω * t → t = 0 := by decide
  obtain ⟨hxS, h21, h10⟩ := mem_X₄sub_sup_Fsub_iff_mat.1 hx
  exact mem_Fsub.2 ⟨hxS, h21, h10, key _ e⟩

theorem mem_ZX₄sub_of_conj_e₂ {x : SU52} (hx : x ∈ X₄sub)
    (h : x⁻¹ * (e₂SU * x * e₂SU⁻¹) ∈ ZX₄sub) : x ∈ ZX₄sub := by
  have hF := mem_Fsub_of_conj_e₂ (mem_sup_left hx) (mem_sup_right h)
  obtain ⟨a, b, hm⟩ := mem_X₄sub.1 hx
  have h20 := (mem_Fsub.1 hF).2.2.2
  rw [hm] at h20
  change a = 0 at h20
  subst h20
  exact mem_x₄Sub.2 ⟨0, b, rfl, hm⟩

theorem eq_Fsub_or_eq_of_conj_e₂ {R : Subgroup SU52} (hFR : Fsub ≤ R) (hR : R ≤ X₄sub ⊔ Fsub)
    (he : ∀ r ∈ R, e₂SU * r * e₂SU⁻¹ ∈ R) : R = Fsub ∨ R = X₄sub ⊔ Fsub := by
  by_cases hRF : R ≤ Fsub
  · exact Or.inl (le_antisymm hRF hFR)
  right
  refine le_antisymm hR fun y hy => ?_
  obtain ⟨r, hrR, hrF⟩ := IsConcreteLE.not_le_iff_exists.1 hRF
  have hr := hR hrR
  have hr20 : mat r 2 0 ≠ 0 := fun h0 => hrF (by
    obtain ⟨hrS, h21, h10⟩ := mem_X₄sub_sup_Fsub_iff_mat.1 hr
    exact mem_Fsub.2 ⟨hrS, h21, h10, h0⟩)
  have hr₁R : e₂SU * r * e₂SU⁻¹ ∈ R := he r hrR
  have hr₂R : e₂SU * (e₂SU * r * e₂SU⁻¹) * e₂SU⁻¹ ∈ R := he _ hr₁R
  have h₁ := mat_conj_e₂_two_zero r
  have h₂ : mat (e₂SU * (e₂SU * r * e₂SU⁻¹) * e₂SU⁻¹) 2 0 = F4.ω * (F4.ω * mat r 2 0) := by
    rw [mat_conj_e₂_two_zero, h₁]
  have hmem : ∀ w ∈ R, mat w 2 0 = mat y 2 0 → y ∈ R := fun w hw hwy => by
    have hwy' : w⁻¹ * y ∈ Fsub := (inv_mul_mem_Fsub_iff_of_mem (hR hw) hy).2 hwy
    rw [show y = w * (w⁻¹ * y) by group]
    exact mul_mem hw (hFR hwy')
  have key : ∀ α β : F4, α ≠ 0 → β = 0 ∨ β = α ∨ β = F4.ω * α ∨ β = F4.ω * (F4.ω * α) := by
    decide
  rcases key _ (mat y 2 0) hr20 with h0 | h0 | h0 | h0
  · obtain ⟨hyS, h21, h10⟩ := mem_X₄sub_sup_Fsub_iff_mat.1 hy
    exact hFR (mem_Fsub.2 ⟨hyS, h21, h10, h0⟩)
  · exact hmem r hrR h0.symm
  · exact hmem _ hr₁R (h₁.trans h0.symm)
  · exact hmem _ hr₂R (h₂.trans h0.symm)

theorem eTorDiag_two_eq_cases : ∀ i j : Fin 3, eTorDiag i j 2 = eTorDiag i j 0 →
    (i = 0 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by
  unfold eTorDiag
  simp only [bar_apply]
  decide

theorem e₁_mul_e₂_sq : e₁SU ^ 1 * e₂SU ^ 2 = (e₁SU ^ 2 * e₂SU) ^ 2 := by
  have hc : Commute (e₁SU ^ 2) e₂SU := Commute.pow_left (e₁SU_mul_e₂SU : Commute e₁SU e₂SU) 2
  have h3 : e₁SU ^ 3 = 1 := by
    rw [← orderOf_e₁SU]
    exact pow_orderOf_eq_one _
  rw [hc.mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, h3, one_mul]

theorem eTor_mem_zpowers_of_two_eq {i j : Fin 3} (h : eTorDiag i j 2 = eTorDiag i j 0) :
    e₁SU ^ (i : ℕ) * e₂SU ^ (j : ℕ) ∈ zpowers (e₁SU ^ 2 * e₂SU) := by
  rcases eTorDiag_two_eq_cases i j h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change e₁SU ^ 0 * e₂SU ^ 0 ∈ _
    rw [pow_zero, pow_zero, mul_one]
    exact one_mem _
  · change e₁SU ^ 2 * e₂SU ^ 1 ∈ _
    rw [pow_one]
    exact mem_zpowers _
  · change e₁SU ^ 1 * e₂SU ^ 2 ∈ _
    rw [e₁_mul_e₂_sq]
    exact npow_mem_zpowers _ _

theorem mem_Ssub_sup_zpowers_of_conj_mem {s : SU52} (hs : s ∈ normalizer (Ssub : Set SU52))
    (h : ∀ x ∈ X₄sub ⊔ Fsub, x⁻¹ * (s * x * s⁻¹) ∈ Fsub) :
    s ∈ Ssub ⊔ zpowers (e₁SU ^ 2 * e₂SU) := by
  have hx : x₄SU 1 F4.ω one_omega_rel ∈ X₄sub ⊔ Fsub := mem_sup_left (x₄SU_mem _ _ _)
  have e := (inv_mul_mem_Fsub_iff_of_mem hx (normalizer_Ssub_conj_mem_X₄sub_sup_Fsub hs hx)).1
    (h _ hx)
  rw [mat_conj_two_zero_of_mem_normalizer hs hx, mat_x₄SU] at e
  change (1 : F4) = mat s 2 2 * mat s⁻¹ 0 0 * 1 at e
  have h00 := mat_inv_zero_zero_mul hs
  have h22 : mat s 2 2 = mat s 0 0 := by
    linear_combination (-mat s 0 0) * e - mat s 2 2 * h00
  obtain ⟨i, j, hu, hd⟩ := exists_mul_of_mem_normalizer_Ssub hs
  have hij : eTorDiag i j 2 = eTorDiag i j 0 := by rw [← hd, ← hd, h22]
  have := mul_mem (mem_sup_right (eTor_mem_zpowers_of_two_eq hij)) (mem_sup_left hu)
  rwa [mul_inv_cancel_left] at this

theorem conj_mem_of_mem_Ssub_sup_zpowers {s : SU52}
    (hs : s ∈ Ssub ⊔ zpowers (e₁SU ^ 2 * e₂SU)) :
    s ∈ normalizer (Ssub : Set SU52) ∧ ∀ x ∈ X₄sub ⊔ Fsub, x⁻¹ * (s * x * s⁻¹) ∈ Fsub := by
  let T : Subgroup SU52 :=
    { carrier := {s | s ∈ normalizer (Ssub : Set SU52) ∧
        ∀ x ∈ X₄sub ⊔ Fsub, x⁻¹ * (s * x * s⁻¹) ∈ Fsub}
      mul_mem' := fun {s t} ⟨hs, hs'⟩ ⟨ht, ht'⟩ => ⟨mul_mem hs ht, fun x hx => by
        have h1 := hs' _ hx
        have h2 := normalizer_Ssub_conj_mem_Fsub hs (ht' x hx)
        rw [show x⁻¹ * (s * t * x * (s * t)⁻¹) =
          x⁻¹ * (s * x * s⁻¹) * (s * (x⁻¹ * (t * x * t⁻¹)) * s⁻¹) by group]
        exact mul_mem h1 h2⟩
      one_mem' := ⟨one_mem _, fun x _ => by
        rw [one_mul, inv_one, mul_one, inv_mul_cancel]
        exact one_mem _⟩
      inv_mem' := fun {s} ⟨hs, hs'⟩ => ⟨inv_mem hs, fun x hx => by
        have h1 := hs' _ (normalizer_Ssub_conj_mem_X₄sub_sup_Fsub (inv_mem hs) hx)
        have e : (s⁻¹ * x * s⁻¹⁻¹)⁻¹ * (s * (s⁻¹ * x * s⁻¹⁻¹) * s⁻¹) =
            (x⁻¹ * (s⁻¹ * x * s⁻¹⁻¹))⁻¹ := by group
        rw [e] at h1
        exact inv_mem_iff.1 h1⟩ }
  have hS : Ssub ≤ T := fun s hs => ⟨le_normalizer hs, fun x hx => by
    have h := (mem_X₄sub_sup_Fsub_iff.1 (inv_mem hx)).2 s hs
    rw [inv_inv] at h
    rw [show x⁻¹ * (s * x * s⁻¹) = (s * x⁻¹ * s⁻¹ * x)⁻¹ by group]
    exact inv_mem h⟩
  have hm : mat (e₁SU ^ 2 * e₂SU) = Matrix.diagonal (eTorDiag 2 1) := by
    have := mat_eTor 2 1
    rwa [show ((2 : Fin 3) : ℕ) = 2 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl, pow_one] at this
  have hN : e₁SU ^ 2 * e₂SU ∈ normalizer (Ssub : Set SU52) := Esub_le_normalizer_Ssub
    (mul_mem (pow_mem (mem_sup_left (mem_zpowers _)) 2) (mem_sup_right (mem_zpowers _)))
  have ht : e₁SU ^ 2 * e₂SU ∈ T := ⟨hN, fun x hx => by
    refine (inv_mul_mem_Fsub_iff_of_mem hx (normalizer_Ssub_conj_mem_X₄sub_sup_Fsub hN hx)).2 ?_
    rw [mat_conj_diag (eTorDiag_ne_zero 2 1) hm]
    have h20 : eTorDiag 2 1 2 = eTorDiag 2 1 0 := by
      unfold eTorDiag
      simp only [bar_apply]
      decide
    rw [h20, mul_comm (eTorDiag 2 1 0), mul_assoc, mul_inv_cancel₀ (eTorDiag_ne_zero 2 1 0),
      mul_one]⟩
  exact (sup_le hS (zpowers_le.2 ht)) hs

theorem mem_Ssub_sup_zpowers_iff {s : SU52} :
    s ∈ Ssub ⊔ zpowers (e₁SU ^ 2 * e₂SU) ↔ s ∈ normalizer (Ssub : Set SU52) ∧
      ∀ x ∈ X₄sub ⊔ Fsub, x⁻¹ * (s * x * s⁻¹) ∈ Fsub :=
  ⟨conj_mem_of_mem_Ssub_sup_zpowers, fun h => mem_Ssub_sup_zpowers_of_conj_mem h.1 h.2⟩

theorem not_conj_fld_trivial {s : SU52} (hs : ∀ x ∈ Ssub, s * fld x * s⁻¹ ∈ Ssub) :
    ¬ ∀ x ∈ X₄sub ⊔ Fsub, x⁻¹ * (s * fld x * s⁻¹) ∈ Fsub := by
  intro h
  have hn : s ∈ normalizer (Ssub : Set SU52) := mem_normalizer_fintype fun x hx => by
    have := hs (fld x) (fld_mem_Ssub hx)
    rwa [fld_fld] at this
  have key : ∀ (a b : F4) (hab : a * bar a = b + bar b),
      a = mat s 2 2 * mat s⁻¹ 0 0 * bar a := by
    intro a b hab
    have hx : x₄SU a b hab ∈ X₄sub ⊔ Fsub := mem_sup_left (x₄SU_mem _ _ _)
    have hfx : fld (x₄SU a b hab) ∈ X₄sub ⊔ Fsub := by
      rw [fld_x₄SU]
      exact mem_sup_left (x₄SU_mem _ _ _)
    have e := (inv_mul_mem_Fsub_iff_of_mem hx
      (normalizer_Ssub_conj_mem_X₄sub_sup_Fsub hn hfx)).1 (h _ hx)
    rw [mat_conj_two_zero_of_mem_normalizer hn hfx, fld_x₄SU] at e
    simp only [mat_x₄SU] at e
    exact e
  have e1 := key 1 F4.ω one_omega_rel
  have e2 := key F4.ω F4.ω omega_omega_rel
  rw [map_one, mul_one] at e1
  rw [← e1, one_mul, bar_ω] at e2
  exact absurd e2 (by decide)

theorem eq_Ssub_of_isPGroup {Q : Subgroup SU52} (hQ : IsPGroup 2 Q) (hSQ : Ssub ≤ Q) :
    Q = Ssub := by
  obtain ⟨P, hP⟩ := exists_sylow_Ssub
  rw [← hP] at hSQ ⊢
  exact P.is_maximal' hQ hSQ

theorem mat_mul_self_of_lower {s t : SU52} (hs : ∀ i j : Fin 5, i < j → mat s i j = 0)
    (ht : ∀ i j : Fin 5, i < j → mat t i j = 0) (k : Fin 5) :
    mat (s * t) k k = mat s k k * mat t k k := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single k]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [ht l k h, mul_zero]
    · rw [hs k l h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem exists_eq_conj_of_mem_of_isPGroup {Q : Subgroup (MulAut SU52)} (hQ : IsPGroup 2 Q)
    (hQS : ∀ α ∈ Q, ∀ x ∈ Ssub, α x ∈ Ssub)
    (he : ∀ α ∈ Q, MulAut.conj e₁SU * α * (MulAut.conj e₁SU)⁻¹ ∈ Q)
    {α : MulAut SU52} (hα : α ∈ Q) : ∃ s ∈ Ssub, α = MulAut.conj s := by
  have inner : ∀ n : SU52, MulAut.conj n ∈ Q → n ∈ Ssub := by
    intro n hn
    have hnN : n ∈ normalizer (Ssub : Set SU52) :=
      mem_normalizer_fintype fun x hx => hQS _ hn x hx
    obtain ⟨k, hk⟩ := hQ ⟨_, hn⟩
    have h1 : (MulAut.conj n) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hk' : n ^ 2 ^ k = 1 := (conj_eq_one_iff _).1 (by rw [map_pow, h1])
    have hZ : IsPGroup 2 (zpowers n) := IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk')
    have hsup := (IsPGroup.of_card card_Ssub).to_sup_of_normal_left' hZ (zpowers_le.2 hnN)
    rw [← eq_Ssub_of_isPGroup hsup le_sup_left]
    exact mem_sup_right (mem_zpowers n)
  obtain ⟨n, rfl | rfl⟩ := exists_eq_conj_or_eq_conj_mul_fld α
  · exact ⟨n, inner n hα, rfl⟩
  exfalso
  have hnN : n ∈ normalizer (Ssub : Set SU52) := mem_normalizer_fintype fun x hx => by
    have := hQS _ hα (fld x) (fld_mem_Ssub hx)
    simpa [MulAut.mul_apply, MulAut.conj_apply, fld_fld] using this
  have hγ : MulAut.conj e₁SU * (MulAut.conj n * fld) * (MulAut.conj e₁SU)⁻¹ *
      (MulAut.conj n * fld)⁻¹ = MulAut.conj (e₁SU * n * e₁SU * n⁻¹) := by
    rw [mul_inv_rev, fld_inv]
    refine MulEquiv.ext fun g => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
      fld_fld, fld_e₁SU, inv_inv]
  have hm := inner _ (by
    rw [← hγ]
    exact mul_mem (he _ hα) (inv_mem hα))
  have he₁N : e₁SU ∈ normalizer (Ssub : Set SU52) :=
    Esub_le_normalizer_Ssub (mem_sup_left (mem_zpowers _))
  have l1 := lower_of_mem_normalizer_Ssub he₁N
  have l2 := lower_of_mem_normalizer_Ssub hnN
  have l3 := lower_of_mem_normalizer_Ssub (mul_mem he₁N hnN)
  have l4 := lower_of_mem_normalizer_Ssub (mul_mem (mul_mem he₁N hnN) he₁N)
  have l5 := lower_of_mem_normalizer_Ssub (inv_mem hnN)
  have d := (mem_Ssub.1 hm).2 1
  rw [mat_mul_self_of_lower l4 l5, mat_mul_self_of_lower l3 l1, mat_mul_self_of_lower l1 l2,
    mat_e₁SU, e₁Mat, Matrix.diagonal_apply_eq] at d
  have dn : mat n 1 1 * mat n⁻¹ 1 1 = 1 := by
    rw [← mat_mul_self_of_lower l2 l5, mul_inv_cancel, mat_one, Matrix.one_apply_eq]
  change F4.ω * mat n 1 1 * F4.ω * mat n⁻¹ 1 1 = 1 at d
  have h : F4.ω * F4.ω = 1 := by linear_combination d - F4.ω * F4.ω * dn
  exact absurd h (by decide)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
