module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSTwo
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckAut
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix Certificates.U52Yamada
open scoped commutatorElement

theorem mem_A₁sub_sup_Fsub_iff {x : SU52} : x ∈ A₁sub ⊔ Fsub ↔ x ∈ Ssub ∧ mat x 2 1 = 0 := by
  constructor
  · intro hx
    let T : Subgroup SU52 :=
      { carrier := {g | g ∈ Ssub ∧ mat g 2 1 = 0}
        mul_mem' := fun {g h} ⟨hg, hg0⟩ ⟨hh, hh0⟩ =>
          ⟨mul_mem hg hh, by rw [mat_mul_two_one hg hh, hg0, hh0, add_zero]⟩
        one_mem' := ⟨one_mem _, rfl⟩
        inv_mem' := fun {g} ⟨hg, hg0⟩ =>
          ⟨inv_mem hg, inv_entry_eq_zero (by decide) (mat_mul_two_one hg (inv_mem hg)) hg0⟩ }
    have hle : A₁sub ⊔ Fsub ≤ T := sup_le (fun g hg => ⟨(mem_A₁sub.1 hg).1, (mem_A₁sub.1 hg).2.1⟩)
      fun g hg => ⟨(mem_Fsub.1 hg).1, (mem_Fsub.1 hg).2.1⟩
    exact hle hx
  · rintro ⟨hx, h0⟩
    obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, -, k₁, -, -⟩ :=
      exists_eq_nf_coord hx
    rw [h0] at k₁
    rw [← k₁] at e₁
    have h1 : g₁ ∈ Fsub := mem_sup_left (mem_sup_left (mem_x₁Sub.2 ⟨0, b₁, rfl, e₁⟩))
    have h2 : g₂ * g₃ * g₄ ∈ A₁sub := mul_mem (mul_mem (X₂sub_le_A₁sub (mem_X₂sub.2 ⟨a₂, e₂⟩))
      (X₃sub_le_A₁sub (mem_X₃sub.2 ⟨a₃, e₃⟩))) (X₄sub_le_A₁sub' (mem_X₄sub.2 ⟨a₄, b₄, e₄⟩))
    rw [show g₁ * g₂ * g₃ * g₄ = g₁ * (g₂ * g₃ * g₄) by group]
    exact mul_mem (mem_sup_right h1) (mem_sup_left h2)

theorem mat_mul_self_two_zero {x : SU52} (hx : x ∈ Ssub) :
    mat (x * x) 2 0 = mat x 2 1 * mat x 1 0 := by
  rw [mat_mul_two_zero hx hx, add_right_comm, CharTwo.add_self_eq_zero, zero_add]

theorem commutator_mem_Fsub_of_mem_A₁sub_sup_Fsub {x y : SU52} (hx : x ∈ A₁sub ⊔ Fsub)
    (hy : y ∈ A₁sub ⊔ Fsub) : x * y * x⁻¹ * y⁻¹ ∈ Fsub := by
  obtain ⟨hxS, hx21⟩ := mem_A₁sub_sup_Fsub_iff.1 hx
  obtain ⟨hyS, hy21⟩ := mem_A₁sub_sup_Fsub_iff.1 hy
  have hc : ⁅x, y⁆ ∈ ZX₁sub ⊔ X₃sub ⊔ X₄sub := commutator_Ssub ▸ commutator_mem_commutator hxS hyS
  obtain ⟨hcS, hc21, hc10⟩ := mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff.1 hc
  have hc20 := mat_commutator_two_zero hxS hyS
  rw [hx21, hy21, zero_mul, zero_mul, sub_zero] at hc20
  exact mem_Fsub.2 ⟨hcS, hc21, hc10, hc20⟩

theorem mul_self_mem_Fsub_of_mem_A₁sub_sup_Fsub {x : SU52} (hx : x ∈ A₁sub ⊔ Fsub) :
    x * x ∈ Fsub := by
  obtain ⟨hxS, hx21⟩ := mem_A₁sub_sup_Fsub_iff.1 hx
  refine mem_Fsub.2 ⟨mul_mem hxS hxS, ?_, ?_, ?_⟩
  · rw [mat_mul_two_one hxS hxS, hx21, add_zero]
  · rw [mat_mul_one_zero hxS hxS, CharTwo.add_self_eq_zero]
  · rw [mat_mul_self_two_zero hxS, hx21, zero_mul]

theorem le_A₁sub_sup_Fsub_or_le_A₂sub {E : Subgroup SU52} (hE : E ≤ Ssub)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ Fsub) (hs : ∀ x ∈ E, x * x ∈ Fsub) :
    E ≤ A₁sub ⊔ Fsub ∨ E ≤ A₂sub := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨x, hxE, hx1⟩ := IsConcreteLE.not_le_iff_exists.1 hne.1
  obtain ⟨y, hyE, hy2⟩ := IsConcreteLE.not_le_iff_exists.1 hne.2
  have hxS := hE hxE
  have hyS := hE hyE
  have hx21 : mat x 2 1 ≠ 0 := fun h => hx1 (mem_A₁sub_sup_Fsub_iff.2 ⟨hxS, h⟩)
  have hy10 : mat y 1 0 ≠ 0 := fun h => hy2 (mem_A₂sub.2 ⟨hyS, h⟩)
  have hxx := (mem_Fsub.1 (hs x hxE)).2.2.2
  have hyy := (mem_Fsub.1 (hs y hyE)).2.2.2
  rw [mat_mul_self_two_zero hxS] at hxx
  rw [mat_mul_self_two_zero hyS] at hyy
  have hx10 : mat x 1 0 = 0 := (mul_eq_zero.1 hxx).resolve_left hx21
  have hy21 : mat y 2 1 = 0 := (mul_eq_zero.1 hyy).resolve_right hy10
  have hxy := (mem_Fsub.1 (hc x hxE y hyE)).2.2.2
  change mat ⁅x, y⁆ 2 0 = 0 at hxy
  rw [mat_commutator_two_zero hxS hyS, hx10, hy21, zero_mul, sub_zero] at hxy
  exact mul_ne_zero hx21 hy10 hxy

theorem mat_conj_two_one_of_mem_normalizer {n x : SU52}
    (hn : n ∈ normalizer (Ssub : Set SU52)) (hx : x ∈ Ssub) :
    mat (n * x * n⁻¹) 2 1 = mat n 2 2 * mat n⁻¹ 1 1 * mat x 2 1 := by
  have hlow := lower_of_mem_normalizer_Ssub hn
  have hlow' := lower_of_mem_normalizer_Ssub (inv_mem hn)
  obtain ⟨xl, xd⟩ := mem_Ssub.1 hx
  have hnn : (mat n * mat n⁻¹) 2 1 = 0 := by
    rw [← mat_mul, mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)]
  have n23 := hlow 2 3 (by decide)
  have n24 := hlow 2 4 (by decide)
  have m01 := hlow' 0 1 (by decide)
  have x12 := xl 1 2 (by decide)
  have x13 := xl 1 3 (by decide)
  have x14 := xl 1 4 (by decide)
  have x23 := xl 2 3 (by decide)
  have x24 := xl 2 4 (by decide)
  have x01 := xl 0 1 (by decide)
  have x02 := xl 0 2 (by decide)
  have x03 := xl 0 3 (by decide)
  have x04 := xl 0 4 (by decide)
  have x11 := xd 1
  have x22 := xd 2
  rw [mat_mul, mat_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_five, n23, n24, m01, x01, x02, x03, x04, x12, x13, x14,
    x23, x24, x11, x22] at hnn ⊢
  linear_combination hnn

theorem mat_conj_one_zero_of_mem_normalizer {n x : SU52}
    (hn : n ∈ normalizer (Ssub : Set SU52)) (hx : x ∈ Ssub) :
    mat (n * x * n⁻¹) 1 0 = mat n 1 1 * mat n⁻¹ 0 0 * mat x 1 0 := by
  have hlow := lower_of_mem_normalizer_Ssub hn
  obtain ⟨xl, xd⟩ := mem_Ssub.1 hx
  have hnn : (mat n * mat n⁻¹) 1 0 = 0 := by
    rw [← mat_mul, mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)]
  have n12 := hlow 1 2 (by decide)
  have n13 := hlow 1 3 (by decide)
  have n14 := hlow 1 4 (by decide)
  have x01 := xl 0 1 (by decide)
  have x02 := xl 0 2 (by decide)
  have x03 := xl 0 3 (by decide)
  have x04 := xl 0 4 (by decide)
  have x12 := xl 1 2 (by decide)
  have x13 := xl 1 3 (by decide)
  have x14 := xl 1 4 (by decide)
  have x00 := xd 0
  have x11 := xd 1
  rw [mat_mul, mat_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_five, n12, n13, n14, x01, x02, x03, x04, x12, x13, x14,
    x00, x11] at hnn ⊢
  linear_combination hnn

theorem mem_commutator_Ssub_iff {x : SU52} :
    x ∈ ⁅Ssub, Ssub⁆ ↔ x ∈ Ssub ∧ mat x 2 1 = 0 ∧ mat x 1 0 = 0 := by
  rw [commutator_Ssub, mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff]

theorem inv_mul_mem_commutator_iff {x y : SU52} (hx : x ∈ Ssub) (hy : y ∈ Ssub) :
    x⁻¹ * y ∈ ⁅Ssub, Ssub⁆ ↔ mat x 2 1 = mat y 2 1 ∧ mat x 1 0 = mat y 1 0 := by
  have hxi := inv_mem hx
  have h21 : mat x⁻¹ 2 1 = -mat x 2 1 := by
    have := mat_mul_two_one hx hxi
    rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)] at this
    linear_combination -this
  have h10 : mat x⁻¹ 1 0 = -mat x 1 0 := by
    have := mat_mul_one_zero hx hxi
    rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)] at this
    linear_combination -this
  rw [mem_commutator_Ssub_iff, mat_mul_two_one hxi hy, mat_mul_one_zero hxi hy, h21, h10,
    neg_add_eq_zero, neg_add_eq_zero]
  exact ⟨fun h => h.2, fun h => ⟨mul_mem hxi hy, h⟩⟩

theorem e₁SU_mem_normalizer_Ssub : e₁SU ∈ normalizer (Ssub : Set SU52) :=
  Esub_le_normalizer_Ssub (mem_sup_left (mem_zpowers _))

theorem mat_conj_e₁_one_zero (x : SU52) : mat (e₁SU * x * e₁SU⁻¹) 1 0 = F4.ω * mat x 1 0 := by
  have hd : ∀ i, (![1, F4.ω, F4.ω, F4.ω, 1] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> decide
  rw [mat_conj_diag hd (by rw [mat_e₁SU, e₁Mat])]
  change F4.ω * mat x 1 0 * (1 : F4)⁻¹ = F4.ω * mat x 1 0
  rw [inv_one, mul_one]

theorem F4_eq_of_ne_zero : ∀ α β : F4, α ≠ 0 →
    β = 0 ∨ β = α ∨ β = F4.ω * α ∨ β = F4.ω * (F4.ω * α) := by
  decide

theorem le_of_coord_omega {R₀ R : Subgroup SU52} {B : Set SU52} (κ : SU52 → F4)
    (hR₀R : R₀ ≤ R) (hRB : ∀ r ∈ R, r ∈ B)
    (hcl : ∀ x ∈ B, ∀ y ∈ B, κ x = κ y → x⁻¹ * y ∈ R₀) (hz : ∀ y ∈ B, κ y = 0 → y ∈ R₀)
    (φ : SU52 → SU52) (hφR : ∀ r ∈ R, φ r ∈ R) (hφ : ∀ r ∈ R, κ (φ r) = F4.ω * κ r)
    {r : SU52} (hr : r ∈ R) (hr0 : κ r ≠ 0) {y : SU52} (hy : y ∈ B) : y ∈ R := by
  have hmem : ∀ w ∈ R, κ w = κ y → y ∈ R := fun w hw hwy => by
    rw [show y = w * (w⁻¹ * y) by group]
    exact mul_mem hw (hR₀R (hcl w (hRB w hw) y hy hwy))
  rcases F4_eq_of_ne_zero _ (κ y) hr0 with h0 | h0 | h0 | h0
  · exact hR₀R (hz y hy h0)
  · exact hmem r hr h0.symm
  · exact hmem _ (hφR r hr) ((hφ r hr).trans h0.symm)
  · exact hmem _ (hφR _ (hφR r hr))
      (((hφ _ (hφR r hr)).trans (by rw [hφ r hr])).trans h0.symm)

theorem A₁sub_inf_commutator_Ssub : A₁sub ⊓ ⁅Ssub, Ssub⁆ = X₃sub ⊔ X₄sub := by
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le X₃sub_le_A₁sub X₄sub_le_A₁sub')
    (sup_le X₃sub_le_commutator_Ssub X₄sub_le_commutator_Ssub))
  obtain ⟨hxA, hxS'⟩ := mem_inf.1 hx
  obtain ⟨-, -, h10⟩ := mem_commutator_Ssub_iff.1 hxS'
  obtain ⟨a₂, a₃, a₄, b₄, hv, e⟩ := exists_nf_of_mem_A₁sub hxA
  have ha₂ : a₂ = 0 := by
    have := congrFun (congrFun e 1) 0
    rw [h10] at this
    simpa [x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] using this.symm
  subst ha₂
  rw [x₂Mat_zero, Matrix.one_mul] at e
  have hv' : a₄ * bar a₄ = b₄ + bar b₄ := hv
  have e' : x = x₃SU a₃ * x₄SU a₄ b₄ hv' := ext_mat (by rw [mat_mul, mat_x₃SU, mat_x₄SU, e])
  rw [e']
  exact mul_mem (mem_sup_left (x₃SU_mem _)) (mem_sup_right (x₄SU_mem _ _ _))

theorem eTorDiag_eq_cases : ∀ i j : Fin 3, eTorDiag i j 1 = eTorDiag i j 0 →
    eTorDiag i j 2 = eTorDiag i j 1 → i = 0 ∧ j = 0 := by
  unfold eTorDiag
  simp only [bar_apply]
  decide

theorem mem_Ssub_of_conj_mem_commutator {s : SU52} (hs : s ∈ normalizer (Ssub : Set SU52))
    (h : ∀ x ∈ Ssub, x⁻¹ * (s * x * s⁻¹) ∈ ⁅Ssub, Ssub⁆) : s ∈ Ssub := by
  have hl := lower_of_mem_normalizer_Ssub hs
  have hl' := lower_of_mem_normalizer_Ssub (inv_mem hs)
  have hd : ∀ k, mat s⁻¹ k k * mat s k k = 1 := fun k => by
    rw [← mat_mul_self_of_lower hl' hl, inv_mul_cancel, mat_one, Matrix.one_apply_eq]
  have hx₂ : x₂SU 1 ∈ Ssub := X₂sub_le_Ssub (x₂SU_mem 1)
  have hx₁ : x₁SU 1 F4.ω one_omega_rel ∈ Ssub :=
    mem_sup_left (mem_sup_left (mem_sup_left (x₁SU_mem _ _ _)))
  have e₂ := ((inv_mul_mem_commutator_iff hx₂ ((mem_normalizer_iff.1 hs _).1 hx₂)).1
    (h _ hx₂)).2
  have e₁ := ((inv_mul_mem_commutator_iff hx₁ ((mem_normalizer_iff.1 hs _).1 hx₁)).1
    (h _ hx₁)).1
  rw [mat_conj_one_zero_of_mem_normalizer hs hx₂, mat_x₂SU] at e₂
  rw [mat_conj_two_one_of_mem_normalizer hs hx₁, mat_x₁SU] at e₁
  change (1 : F4) = mat s 1 1 * mat s⁻¹ 0 0 * 1 at e₂
  change (1 : F4) = mat s 2 2 * mat s⁻¹ 1 1 * 1 at e₁
  have h11 : mat s 1 1 = mat s 0 0 := by
    linear_combination (-mat s 0 0) * e₂ - mat s 1 1 * hd 0
  have h22 : mat s 2 2 = mat s 1 1 := by
    linear_combination (-mat s 1 1) * e₁ - mat s 2 2 * hd 1
  obtain ⟨i, j, hu, hdi⟩ := exists_mul_of_mem_normalizer_Ssub hs
  obtain ⟨rfl, rfl⟩ := eTorDiag_eq_cases i j (by rw [← hdi, ← hdi, h11])
    (by rw [← hdi, ← hdi, h22])
  simpa using hu

theorem not_conj_fld_trivial_mod_commutator {s : SU52}
    (hs : ∀ x ∈ Ssub, s * fld x * s⁻¹ ∈ Ssub) :
    ¬ ∀ x ∈ Ssub, x⁻¹ * (s * fld x * s⁻¹) ∈ ⁅Ssub, Ssub⁆ := by
  intro h
  have hn : s ∈ normalizer (Ssub : Set SU52) := mem_normalizer_fintype fun x hx => by
    have := hs (fld x) (fld_mem_Ssub hx)
    rwa [fld_fld] at this
  have key : ∀ c : F4, c = mat s 1 1 * mat s⁻¹ 0 0 * bar c := by
    intro c
    have hx : x₂SU c ∈ Ssub := X₂sub_le_Ssub (x₂SU_mem c)
    have hfx : fld (x₂SU c) ∈ Ssub := X₂sub_le_Ssub (by rw [fld_x₂SU]; exact x₂SU_mem _)
    have e := ((inv_mul_mem_commutator_iff hx ((mem_normalizer_iff.1 hn _).1 hfx)).1
      (h _ hx)).2
    rw [mat_conj_one_zero_of_mem_normalizer hn hfx, fld_x₂SU] at e
    simp only [mat_x₂SU] at e
    exact e
  have e1 := key 1
  have e2 := key F4.ω
  rw [map_one, mul_one] at e1
  rw [← e1, one_mul, bar_ω] at e2
  exact absurd e2 (by decide)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
