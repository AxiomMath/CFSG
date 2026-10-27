module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSEleven
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6LMod
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag Matrix Certificates.U52Yamada
open scoped commutatorElement

theorem uSU_comm_e₁e₂ : uSU * (e₁SU * e₂SU) = (e₁SU * e₂SU) * uSU :=
  ext_mat (by simp only [mat_mul, mat_uSU, mat_e₁SU, mat_e₂SU]; decide +kernel)

theorem uSU_conj_mem_A₁sub {a : SU52} (ha : a ∈ A₁sub) : uSU * a * uSU⁻¹ ∈ A₁sub :=
  conj_mem_A₁sub_of_comm_z (show uSU * zSU = zSU * uSU from genSU_comm_zSU 0 (by decide)) ha

@[expose] def diagSLM : Matrix (Fin 2) (Fin 2) F4 := Matrix.diagonal ![F4.ω, F4.ω * F4.ω]

theorem det_diagSLM : diagSLM.det = 1 := by
  rw [diagSLM, Matrix.det_diagonal, Fin.prod_univ_two]
  decide +kernel

theorem isUnit_det_diagSLM : IsUnit diagSLM.det := by
  rw [det_diagSLM]
  exact isUnit_one

theorem barInvT_diagSLM : barInvT hF4 diagSLM = diagSLM := barInvT_eq (by
  rw [hF4_bar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSLM, Matrix.mul_apply, Fin.sum_univ_two, bar_apply] <;> decide)

theorem levSU_diagSLM : levSU diagSLM isUnit_det_diagSLM = e₁SU * e₂SU := by
  refine ext_mat ?_
  ext i j
  rw [mat_levSU, det_diagSLM, map_one, div_one, CFSG.ClassicalGroups.UnitaryFlag.oddDiag,
    barInvT_diagSLM, mat_e₁e₂]
  fin_cases i <;> fin_cases j <;>
    simp [yIdx, blk3, diagSLM, Matrix.diagonal, Matrix.fromBlocks] <;> decide

theorem e₁e₂_mem_K₂sub : e₁SU * e₂SU ∈ K₂sub := by
  rw [K₂sub_eq_levSLHom_range]
  exact ⟨⟨diagSLM, det_diagSLM⟩, levSU_diagSLM⟩

@[expose] def a₀SU : SU52 := x₂SU 1 * (vSU * x₂SU 1 * vSU⁻¹)

theorem mat_a₀SU : mat a₀SU = x₂Mat 1 * (vMat * x₂Mat 1 * vMat) := by
  simp only [a₀SU, vSU_inv, mat_mul, mat_x₂SU, mat_vSU]

theorem x₁Mat_mul_a₀_eq : ∀ c d : F4, x₁Mat c d * (x₂Mat 1 * (vMat * x₂Mat 1 * vMat)) =
    (x₂Mat 1 * (vMat * x₂Mat 1 * vMat)) * x₄Mat c d := by
  unfold x₁Mat x₂Mat x₄Mat vMat
  simp only [bar_apply]
  decide +kernel

theorem x₁SU_eq_conj_x₄SU (c d : F4) (h : c * bar c = d + bar d) :
    x₁SU c d h = a₀SU * x₄SU c d h * a₀SU⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  refine ext_mat ?_
  rw [mat_mul, mat_mul, mat_x₁SU, mat_x₄SU, mat_a₀SU]
  exact x₁Mat_mul_a₀_eq c d

theorem X₁sub_le_A₁sub_sup_conj_X₂sub :
    X₁sub ≤ A₁sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom := by
  have ha₀ : a₀SU ∈ A₁sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom := by
    unfold a₀SU
    exact mul_mem (mem_sup_left (X₂sub_le_A₁sub (x₂SU_mem 1)))
      (mem_sup_right (Subgroup.mem_map_of_mem (MulAut.conj vSU).toMonoidHom (x₂SU_mem 1)))
  intro g hg
  obtain ⟨c, d, hm⟩ := mem_X₁sub.1 hg
  have h : c * bar c = d + bar d := x₁_coord_rel hm
  have hg' : g = a₀SU * x₄SU c d h * a₀SU⁻¹ := by
    rw [← x₁SU_eq_conj_x₄SU c d h]
    exact ext_mat (by rw [mat_x₁SU, hm])
  rw [hg']
  exact mul_mem (mul_mem ha₀ (mem_sup_left (X₄sub_le_A₁sub' (x₄SU_mem c d h)))) (inv_mem ha₀)

theorem A₂sub_sup_K₂sub_eq :
    A₂sub ⊔ K₂sub = A₁sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom := by
  have hX₂R : X₂sub ≤ A₁sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom :=
    X₂sub_le_A₁sub.trans le_sup_left
  have hX₃R : X₃sub ≤ A₁sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom :=
    X₃sub_le_A₁sub.trans le_sup_left
  have hX₄R : X₄sub ≤ A₁sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom :=
    X₄sub_le_A₁sub'.trans le_sup_left
  have hXvR : X₂sub.map (MulAut.conj vSU).toMonoidHom ≤
      A₁sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom := le_sup_right
  have hA₂R : A₂sub ≤ A₁sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom :=
    sup_le (sup_le X₁sub_le_A₁sub_sup_conj_X₂sub hX₃R) hX₄R
  have hK₂R : K₂sub ≤ A₁sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom := by
    rw [K₂sub_eq_sup_conj]
    exact sup_le hX₂R hXvR
  have hXvA : X₂sub.map (MulAut.conj vSU).toMonoidHom ≤ A₂sub ⊔ K₂sub := by
    have hXvK : X₂sub.map (MulAut.conj vSU).toMonoidHom ≤ K₂sub := by
      rw [K₂sub_eq_sup_conj]
      exact le_sup_right
    exact hXvK.trans le_sup_right
  have hX₂A : X₂sub ≤ A₂sub ⊔ K₂sub := X₂sub_le_K₂sub.trans le_sup_right
  have hX₃A : X₃sub ≤ A₂sub ⊔ K₂sub :=
    ((le_sup_right.trans le_sup_left : X₃sub ≤ A₂sub)).trans le_sup_left
  have hX₄A : X₄sub ≤ A₂sub ⊔ K₂sub := X₄sub_le_A₂sub.trans le_sup_left
  exact le_antisymm (sup_le hA₂R hK₂R)
    (sup_le (sup_le (sup_le hX₂A hX₃A) hX₄A) hXvA)

theorem row3_x₄Mat_mul (b : F4) (M : Matrix (Fin 5) (Fin 5) F4) (j : Fin 5) :
    (x₄Mat 0 b * M) 3 j = M 3 j := by
  simp [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem mem_A₁sub_of_comm_mod_ZX₄sub {s : SU52} (hs : s ∈ Ssub)
    (h : ∀ a ∈ A₁sub, s * a * s⁻¹ * a⁻¹ ∈ ZX₄sub) : s ∈ A₁sub := by
  obtain ⟨c, b, hc, hcm⟩ := mem_x₄Sub.1 (h _ (X₂sub_le_A₁sub (x₂SU_mem 1)))
  subst hc
  have e : s * x₂SU 1 = (s * x₂SU 1 * s⁻¹ * (x₂SU 1)⁻¹) * x₂SU 1 * s := by group
  have e3 : mat ((s * x₂SU 1 * s⁻¹ * (x₂SU 1)⁻¹) * x₂SU 1 * s) =
      x₄Mat 0 b * x₂Mat 1 * mat s := by
    rw [mat_mul, mat_mul, hcm, mat_x₂SU]
  have em : mat (s * x₂SU 1) = mat ((s * x₂SU 1 * s⁻¹ * (x₂SU 1)⁻¹) * x₂SU 1 * s) :=
    congrArg mat e
  rw [e3, mat_mul, mat_x₂SU] at em
  have h30 := congrFun (congrFun em 3) 0
  rw [mul_assoc, row3_x₄Mat_mul] at h30
  have hS31 : mat s 3 1 = 0 := by
    simp [x₂Mat, Matrix.mul_apply, Fin.sum_univ_five] at h30
    linear_combination h30
  obtain ⟨a₁, b₁, -, -, -, -, g₁, -, -, -, hg₁, -, -, -, -, -, h21, h31, -⟩ :=
    exists_eq_nf_coord hs
  have hb₁ : b₁ = 0 := by
    rw [← h31]
    exact hS31
  have hv : a₁ * bar a₁ = 0 := by
    have := x₁_coord_rel hg₁
    rwa [hb₁, map_zero, add_zero] at this
  have ha₁ : a₁ = 0 := by
    have key : ∀ a : F4, a * bar a = 0 → a = 0 := by
      simp only [bar_apply]
      decide +kernel
    exact key a₁ hv
  exact mem_A₁sub.2 ⟨hs, by rw [h21, ha₁], hS31⟩

theorem mat_pow_gen (g : SU52) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

theorem exists_orderOf_eleven : ∃ x ∈ A₂sub ⊔ K₂sub ⊔ zpowers uSU, orderOf x = 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine ⟨uSU * vSU * x₁SU 1 F4.ω one_omega_rel * x₃SU F4.ω, ?_, ?_⟩
  · refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
    · exact mem_sup_right (mem_zpowers uSU)
    · exact mem_sup_left (mem_sup_right vSU_mem_K₂sub)
    · exact mem_sup_left (mem_sup_left (X₁sub_le_A₂sub (x₁SU_mem _ _ _)))
    · exact mem_sup_left (mem_sup_left
        ((le_sup_right.trans le_sup_left : X₃sub ≤ A₂sub) (x₃SU_mem _)))
  · apply orderOf_eq_prime
    · apply ext_mat
      rw [mat_pow_gen, mat_one]
      simp only [mat_mul, mat_uSU, mat_vSU, mat_x₁SU, mat_x₃SU]
      decide +kernel
    · intro h
      have hm := congrArg mat h
      simp only [mat_mul, mat_uSU, mat_vSU, mat_x₁SU, mat_x₃SU, mat_one] at hm
      revert hm
      decide +kernel

theorem mat_comm_e₁e₂ (g : SU52) : mat ⁅g, e₁SU * e₂SU⁆ =
    mat g * mat (e₁SU * e₂SU) * mat g⁻¹ * mat (e₁SU * e₂SU)⁻¹ := by
  simp only [commutatorElement_def, mat_mul]

theorem x₂SU_eq_comm_e₁e₂ (a : F4) : x₂SU a = ⁅x₂SU (F4.ω * a), e₁SU * e₂SU⁆ := by
  have hinv : mat (x₂SU (F4.ω * a))⁻¹ = x₂Mat (F4.ω * a) := mat_inv_of_x₂ (mat_x₂SU _)
  refine ext_mat ?_
  rw [mat_comm_e₁e₂]
  simp only [mat_x₂SU, mat_e₁e₂, mat_e₁e₂_inv, hinv]
  exact x₂_e₁e₂_check a

theorem x₃SU_eq_comm_e₁e₂ (a : F4) : x₃SU a = ⁅x₃SU (F4.ω * a), e₁SU * e₂SU⁆ := by
  have hinv : mat (x₃SU (F4.ω * a))⁻¹ = x₃Mat (F4.ω * a) := mat_inv_of_x₃ (mat_x₃SU _)
  refine ext_mat ?_
  rw [mat_comm_e₁e₂]
  simp only [mat_x₃SU, mat_e₁e₂, mat_e₁e₂_inv, hinv]
  exact x₃_e₁e₂_check a

theorem commutator_K₂sub_self : ⁅K₂sub, K₂sub⁆ = K₂sub := by
  apply le_antisymm
  · rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · have hX : X₂sub ≤ ⁅K₂sub, K₂sub⁆ := by
      intro x hx
      obtain ⟨c, hc⟩ := mem_X₂sub.1 hx
      have e : x = x₂SU c := ext_mat (by rw [hc, mat_x₂SU])
      rw [e, x₂SU_eq_comm_e₁e₂ c]
      exact commutator_mem_commutator (X₂sub_le_K₂sub (x₂SU_mem _)) e₁e₂_mem_K₂sub
    have hXv : X₂sub.map (MulAut.conj vSU).toMonoidHom ≤ ⁅K₂sub, K₂sub⁆ := by
      rintro _ ⟨x, hx, rfl⟩
      have e : (MulAut.conj vSU).toMonoidHom x = ⁅vSU, x⁆ * x := by
        rw [commutatorElement_def]
        show vSU * x * vSU⁻¹ = vSU * x * vSU⁻¹ * x⁻¹ * x
        group
      rw [e]
      exact mul_mem (commutator_mem_commutator vSU_mem_K₂sub (X₂sub_le_K₂sub hx)) (hX hx)
    have key : X₂sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom ≤ ⁅K₂sub, K₂sub⁆ :=
      sup_le hX hXv
    rw [← K₂sub_eq_sup_conj] at key
    exact key

theorem K₂sub_conj_mem_Fsub {k f : SU52} (hk : k ∈ K₂sub) (hf : f ∈ Fsub) :
    k * f * k⁻¹ ∈ Fsub := by
  rw [K₂sub_eq_levSLHom_range] at hk
  obtain ⟨V, rfl⟩ := hk
  have e : levSLHom V = levHom (Matrix.SpecialLinearGroup.toGL V) := rfl
  rw [e, levHom_apply]
  exact levSU_conj_mem_Fsub _ _ hf

theorem commutator_Fsub_K₂sub : ⁅Fsub, K₂sub⁆ = Fsub := by
  apply le_antisymm
  · rw [commutator_le]
    intro f hf k hk
    rw [commutatorElement_def]
    have hc : k * f⁻¹ * k⁻¹ ∈ Fsub := K₂sub_conj_mem_Fsub hk (inv_mem hf)
    have e : f * k * f⁻¹ * k⁻¹ = f * (k * f⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem hf hc
  · have hX₃F : X₃sub ≤ Fsub := le_sup_right.trans le_sup_left
    have hz₁Z : x₁SU 0 1 zero_one_rel ∈ ZX₁sub :=
      mem_x₁Sub.2 ⟨0, 1, rfl, mat_x₁SU 0 1 zero_one_rel⟩
    have hz₄Z : x₄SU 0 1 zero_one_rel ∈ ZX₄sub :=
      mem_x₄Sub.2 ⟨0, 1, rfl, mat_x₄SU 0 1 zero_one_rel⟩
    have hz₁Fs : x₁SU 0 1 zero_one_rel ∈ Fsub := mem_sup_left (mem_sup_left hz₁Z)
    have hz₄Fs : x₄SU 0 1 zero_one_rel ∈ Fsub := mem_sup_right hz₄Z
    have hX₃K : X₃sub ≤ ⁅Fsub, K₂sub⁆ := by
      intro x hx
      obtain ⟨c, hc⟩ := mem_X₃sub.1 hx
      have e : x = x₃SU c := ext_mat (by rw [hc, mat_x₃SU])
      rw [e, x₃SU_eq_comm_e₁e₂ c]
      exact commutator_mem_commutator (hX₃F (x₃SU_mem _)) e₁e₂_mem_K₂sub
    have hinvz₁ : mat (x₁SU 0 1 zero_one_rel)⁻¹ = x₁Mat 0 1 :=
      mat_inv_eq (by rw [mat_x₁SU]; decide +kernel)
    have hinvz₄ : mat (x₄SU 0 1 zero_one_rel)⁻¹ = x₄Mat 0 1 :=
      mat_inv_eq (by rw [mat_x₄SU]; decide +kernel)
    have hcomm1 : ⁅x₁SU 0 1 zero_one_rel, x₂SU 1⁆ = x₃SU 1 * x₄SU 0 1 zero_one_rel := by
      refine ext_mat ?_
      rw [commutatorElement_def]
      simp only [mat_mul, mat_x₁SU, mat_x₂SU, mat_x₃SU, mat_x₄SU, hinvz₁,
        mat_inv_of_x₂ (mat_x₂SU 1)]
      decide +kernel
    have hcomm2 : ⁅x₄SU 0 1 zero_one_rel, vSU⁆ = x₄SU 0 1 zero_one_rel * x₁SU 0 1 zero_one_rel := by
      refine ext_mat ?_
      rw [commutatorElement_def]
      simp only [mat_mul, vSU_inv, mat_vSU, mat_x₁SU, mat_x₄SU, hinvz₄]
      decide +kernel
    have hz₄K : x₄SU 0 1 zero_one_rel ∈ ⁅Fsub, K₂sub⁆ := by
      have e : x₄SU 0 1 zero_one_rel =
          (x₃SU 1)⁻¹ * ⁅x₁SU 0 1 zero_one_rel, x₂SU 1⁆ := by
        rw [hcomm1, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact mul_mem (inv_mem (hX₃K (x₃SU_mem 1)))
        (commutator_mem_commutator hz₁Fs (X₂sub_le_K₂sub (x₂SU_mem 1)))
    have hz₁K : x₁SU 0 1 zero_one_rel ∈ ⁅Fsub, K₂sub⁆ := by
      have e : x₁SU 0 1 zero_one_rel =
          (x₄SU 0 1 zero_one_rel)⁻¹ * ⁅x₄SU 0 1 zero_one_rel, vSU⁆ := by
        rw [hcomm2, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact mul_mem (inv_mem hz₄K) (commutator_mem_commutator hz₄Fs vSU_mem_K₂sub)
    have hZ₁ : ZX₁sub ≤ ⁅Fsub, K₂sub⁆ := by
      intro w hw
      obtain ⟨a, b, ha, hwm⟩ := mem_x₁Sub.1 hw
      subst ha
      rcases eq_zero_or_one_of_valid b (x₁_coord_rel hwm) with rfl | rfl
      · rw [show w = 1 from ext_mat (by rw [hwm, x₁Mat_zero, mat_one])]
        exact one_mem _
      · rw [show w = x₁SU 0 1 zero_one_rel from ext_mat (by rw [hwm, mat_x₁SU])]
        exact hz₁K
    have hZ₄ : ZX₄sub ≤ ⁅Fsub, K₂sub⁆ := by
      intro w hw
      obtain ⟨a, b, ha, hwm⟩ := mem_x₄Sub.1 hw
      subst ha
      rcases eq_zero_or_one_of_valid b (x₄_coord_rel hwm) with rfl | rfl
      · rw [show w = 1 from ext_mat (by rw [hwm, x₄Mat_zero, mat_one])]
        exact one_mem _
      · rw [show w = x₄SU 0 1 zero_one_rel from ext_mat (by rw [hwm, mat_x₄SU])]
        exact hz₄K
    exact sup_le (sup_le hZ₁ hX₃K) hZ₄

theorem eq_one_of_comm_K₂sub {y : SU52} (hy : y ∈ Fsub) (h : ∀ k ∈ K₂sub, k * y = y * k) :
    y = 1 := by
  have hZ : y ∈ ZX₄sub := mem_ZX₄sub_of_comm hy
    (h _ (X₂sub_le_K₂sub (x₂SU_mem 1))).symm
    (h _ (X₂sub_le_K₂sub (x₂SU_mem F4.ω))).symm
  obtain ⟨a, b, ha, hym⟩ := mem_x₄Sub.1 hZ
  subst ha
  rcases eq_zero_or_one_of_valid b (x₄_coord_rel hym) with rfl | rfl
  · exact ext_mat (by rw [hym, x₄Mat_zero, mat_one])
  · exfalso
    have hy' : y = x₄SU 0 1 zero_one_rel := ext_mat (by rw [hym, mat_x₄SU])
    have hv := h vSU vSU_mem_K₂sub
    rw [hy'] at hv
    have hm := congrArg mat hv
    simp only [mat_mul, mat_vSU, mat_x₄SU] at hm
    exact absurd hm (by decide +kernel)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
