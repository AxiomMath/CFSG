module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Bruhat
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.SylowCenters
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement Pointwise

@[expose] def patV : Fin 6 → Bool := ![false, false, false, false, false, true]

@[expose] def patY : Fin 6 → Bool := ![false, false, false, false, true, true]

@[expose] def patW : Fin 6 → Bool := ![false, false, false, true, true, true]

@[expose] def patD : Fin 6 → Bool := ![false, true, true, true, true, true]

@[expose] def patM : Fin 6 → Bool := ![true, false, true, true, true, true]

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem conj_conj_invol {w : X} (hw : w * w = 1) (t y : X) :
    w * t * w * y * (w * t * w)⁻¹ = w * (t * (w * y * w) * t⁻¹) * w := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  rw [mul_inv_rev, mul_inv_rev, hwi]
  simp only [mul_assoc]

theorem coe_coe_nmUnits (m : d.Γˣ) :
    (((d.nmUnits m : (d.Γ₀)ˣ) : d.Γ₀) : d.Γ) = (m : d.Γ) * d.σ m * d.σ (d.σ m) := rfl

theorem torus_eq_torus_iff {h h' : (d.Γ₀)ˣ × d.Γˣ} :
    d.torus h = d.torus h' ↔ ((h.1 : d.Γ₀) : d.Γ) = ((h'.1 : d.Γ₀) : d.Γ) ∧
      (h.2 : d.Γ) = (h'.2 : d.Γ) := by
  rw [d.torus_injective.eq_iff, Prod.ext_iff, Units.ext_iff, Units.ext_iff, Subtype.ext_iff]

theorem u_torus_eq (l : (d.Γ₀)ˣ) (m : d.Γˣ) :
    d.u * d.torus (l, m) * d.u = d.torus (l * d.nmUnits m, m⁻¹) := by
  obtain ⟨h', hh'⟩ := d.u_torus (l, m)
  have u₅ := conj_symm_of_involution d.u_mul_self d.u_x₂
  have u₄ := conj_symm_of_involution d.u_mul_self d.u_x₃
  have h2 : d.x₂ ((h'.1 : d.Γ₀) * 1) = d.x₂ ((l : d.Γ₀) * d.nm (m : d.Γ) * 1) := by
    rw [← d.torus_x₂, ← hh', conj_conj_invol d.u_mul_self, d.u_x₂, d.torus_x₅, u₅]
  have h3 : d.x₃ (((h'.1 : d.Γ₀) : d.Γ) * (h'.2 : d.Γ) * 1) =
      d.x₃ (((l : d.Γ₀) : d.Γ) * d.σ (m : d.Γ) * d.σ (d.σ (m : d.Γ)) * 1) := by
    rw [← d.torus_x₃, ← hh', conj_conj_invol d.u_mul_self, d.u_x₃, d.torus_x₄, u₄]
  have e1 : ((h'.1 : d.Γ₀) : d.Γ) = ((l : d.Γ₀) : d.Γ) * ((m : d.Γ) * d.σ m * d.σ (d.σ m)) := by
    have := congrArg Subtype.val (mul_right_cancel₀ one_ne_zero (d.x₂_injective h2))
    simpa [coe_fixedNorm] using this
  have e3 := mul_right_cancel₀ one_ne_zero (d.x₃_injective h3)
  rw [hh', torus_eq_torus_iff]
  have hl : ((l : d.Γ₀) : d.Γ) ≠ 0 := by simp
  have hm : (m : d.Γ) ≠ 0 := m.ne_zero
  have hσm : d.σ (m : d.Γ) ≠ 0 := (map_ne_zero d.σ).2 hm
  have hσσm : d.σ (d.σ (m : d.Γ)) ≠ 0 := (map_ne_zero d.σ).2 hσm
  refine ⟨?_, ?_⟩
  · rw [e1]
    simp [coe_coe_nmUnits]
  · rw [e1] at e3
    simp only [Units.val_inv_eq_inv_val]
    field_simp
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hl hσm) hσσm)
    linear_combination e3

theorem v_torus_eq (l : (d.Γ₀)ˣ) (m : d.Γˣ) :
    d.v * d.torus (l, m) * d.v = d.torus (l⁻¹, d.unitsIncl l * m) := by
  obtain ⟨h', hh'⟩ := d.v_torus (l, m)
  have v₃ := conj_symm_of_involution d.v_mul_self d.v_x₁
  have h1 : d.x₁ ((h'.2 : d.Γ) * 1) = d.x₁ (((l : d.Γ₀) : d.Γ) * (m : d.Γ) * 1) := by
    rw [← d.torus_x₁, ← hh', conj_conj_invol d.v_mul_self, d.v_x₁, d.torus_x₃, v₃]
  have h3 : d.x₃ (((h'.1 : d.Γ₀) : d.Γ) * (h'.2 : d.Γ) * 1) = d.x₃ ((m : d.Γ) * 1) := by
    rw [← d.torus_x₃, ← hh', conj_conj_invol d.v_mul_self, v₃, d.torus_x₁, d.v_x₁]
  have e1 := mul_right_cancel₀ one_ne_zero (d.x₁_injective h1)
  have e3 := mul_right_cancel₀ one_ne_zero (d.x₃_injective h3)
  rw [hh', torus_eq_torus_iff]
  have hl : ((l : d.Γ₀) : d.Γ) ≠ 0 := by simp
  have hm : (m : d.Γ) ≠ 0 := m.ne_zero
  rw [e1] at e3
  refine ⟨?_, ?_⟩
  · simp only [Units.val_inv_eq_inv_val, Subfield.coe_inv]
    field_simp
    apply mul_left_cancel₀ hm
    linear_combination e3
  · rw [e1]
    simp [coe_unitsIncl]

theorem nmUnits_unitsIncl (l : (d.Γ₀)ˣ) : d.nmUnits (d.unitsIncl l) = l ^ 3 := by
  refine Units.ext (Subtype.ext ?_)
  rw [coe_coe_nmUnits, coe_unitsIncl, apply_coe_fixedSubfield, apply_coe_fixedSubfield]
  simp [pow_succ]

theorem uv_torus_eq (l : (d.Γ₀)ˣ) (m : d.Γˣ) :
    d.u * d.v * d.torus (l, m) * (d.u * d.v)⁻¹ =
      d.torus (l ^ 2 * d.nmUnits m, (d.unitsIncl l)⁻¹ * m⁻¹) := by
  have e : d.u * d.v * d.torus (l, m) * (d.u * d.v)⁻¹ =
      d.u * (d.v * d.torus (l, m) * d.v) * d.u := by
    rw [mul_inv_rev, d.u_inv, d.v_inv]
    simp only [mul_assoc]
  rw [e, v_torus_eq, u_torus_eq, map_mul, nmUnits_unitsIncl, mul_inv]
  congr 2
  group

theorem w₀_torus_eq (h : (d.Γ₀)ˣ × d.Γˣ) : d.w₀ * d.torus h * d.w₀ = (d.torus h)⁻¹ := by
  have hw : d.w₀ = (d.u * d.v) ^ 3 := by
    rw [d.w₀_eq]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hinv : d.w₀⁻¹ = d.w₀ := inv_eq_of_mul_eq_one_right d.w₀_mul_self
  have step (k : ℕ) (t : X) : (d.u * d.v) ^ (k + 1) * t * ((d.u * d.v) ^ (k + 1))⁻¹ =
      (d.u * d.v) ^ k * (d.u * d.v * t * (d.u * d.v)⁻¹) * ((d.u * d.v) ^ k)⁻¹ := by
    rw [pow_succ]
    group
  obtain ⟨l, m⟩ := h
  rw [show d.w₀ * d.torus (l, m) * d.w₀ = (d.u * d.v) ^ 3 * d.torus (l, m) *
    ((d.u * d.v) ^ 3)⁻¹ by rw [← hw]; nth_rewrite 2 [← hinv]; rfl]
  rw [step, step, step, pow_zero, one_mul, inv_one, mul_one, uv_torus_eq, uv_torus_eq,
    uv_torus_eq, ← map_inv d.torus]
  congr 1
  have hl : ((l : d.Γ₀) : d.Γ) ≠ 0 := by simp
  have hm : (m : d.Γ) ≠ 0 := m.ne_zero
  have hσm : d.σ (m : d.Γ) ≠ 0 := (map_ne_zero d.σ).2 hm
  have hσσm : d.σ (d.σ (m : d.Γ)) ≠ 0 := (map_ne_zero d.σ).2 hσm
  have hσl : d.σ ((l : d.Γ₀) : d.Γ) = (l : d.Γ₀) := apply_coe_fixedSubfield _
  refine Prod.ext (Units.ext (Subtype.ext ?_)) (Units.ext ?_)
  · simp only [map_mul, map_inv, map_pow, nmUnits_unitsIncl, Prod.fst_inv]
    push_cast
    simp only [coe_coe_nmUnits]
    field_simp
  · simp only [map_mul, map_inv, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, Prod.snd_inv, nmUnits_unitsIncl]
    field_simp

theorem weylWord_zero : d.weylWord 0 = 1 := by
  simp [weylWord, weylList, word]

theorem weylWord_one : d.weylWord 1 = d.u := by
  simp [weylWord, weylList, word, gen]

theorem weylWord_two : d.weylWord 2 = d.v := by
  simp [weylWord, weylList, word, gen]

theorem u_ne_one : d.u ≠ 1 := by
  intro h
  have h2 := d.orderOf_u_mul_v
  rw [h, one_mul] at h2
  have h3 : orderOf d.v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, d.v_mul_self])
  rw [h2] at h3
  norm_num at h3

theorem v_ne_one : d.v ≠ 1 := by
  intro h
  have h2 := d.orderOf_u_mul_v
  rw [h, mul_one] at h2
  have h3 : orderOf d.u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, d.u_mul_self])
  rw [h2] at h3
  norm_num at h3

theorem w₀_inv : d.w₀⁻¹ = d.w₀ :=
  inv_eq_of_mul_eq_one_right d.w₀_mul_self

theorem w₀_mem_weyl : d.w₀ ∈ d.weyl :=
  d.weylWord_mem_weyl 11

theorem u_conj_x₃_eq_x₄ (a : d.Γ) : d.u * d.x₃ a * d.u⁻¹ = d.x₄ a := by
  rw [d.u_inv, d.u_x₃]

theorem u_conj_x₄_eq_x₃ (a : d.Γ) : d.u * d.x₄ a * d.u⁻¹ = d.x₃ a := by
  rw [← d.u_conj_x₃_eq_x₄ a, conj_conj_of_mul_self d.u_mul_self]

theorem w₀_conj_x₁ (a : d.Γ) : d.w₀ * d.x₁ a * d.w₀ = d.u * d.x₁ a * d.u := by
  have h := congrArg (fun g => g * d.x₁ a * g⁻¹) d.w₀_eq
  rw [d.w₀_inv] at h
  rw [h, conj_mul_conj, conj_mul_conj, conj_mul_conj, conj_mul_conj, conj_mul_conj,
    d.v_conj_x₁, d.u_conj_x₃_eq_x₄, d.v_conj_x₄, d.u_conj_x₄_eq_x₃, d.v_conj_x₃, d.u_inv]

theorem w₀_conj_x₂ (a : d.Γ₀) : d.w₀ * d.x₂ a * d.w₀ = d.v * d.x₂ a * d.v := by
  have e : d.w₀ = d.v * (d.u * (d.v * (d.u * (d.v * d.u)))) := by
    rw [d.w₀_eq, d.uvuvuv_eq]
  have h := congrArg (fun g => g * d.x₂ a * g⁻¹) e
  rw [d.w₀_inv] at h
  rw [h, conj_mul_conj, conj_mul_conj, conj_mul_conj, conj_mul_conj, conj_mul_conj,
    d.u_conj_x₂, d.v_conj_x₅, d.u_conj_x₆, d.v_conj_x₆, d.u_conj_x₅, d.v_inv]

theorem boxProd_subset_S (P : Fin 6 → Bool) : d.boxProd P ⊆ d.S := by
  rintro _ ⟨a, -, rfl⟩
  exact d.normal_form.mapsTo (Set.mem_univ a)

theorem wordAct_of_smul_rootGroup_le {k : Fin 12} {i : Fin 6} {T : Subgroup X}
    {P : Fin 6 → Bool} (hT : (T : Set X) ⊆ d.boxProd P)
    (h : MulAut.conj (d.weylWord k) • d.rootGroup i ≤ T) :
    (wordAct (weylList k) (false, i)).1 = false ∧
      P (wordAct (weylList k) (false, i)).2 = true := by
  rw [d.smul_rootGroup_weylWord] at h
  generalize wordAct (weylList k) (false, i) = r at h ⊢
  obtain ⟨ε, j⟩ := r
  cases ε
  · refine ⟨rfl, ?_⟩
    by_contra hP
    rw [Bool.not_eq_true] at hP
    apply d.rootGroup_ne_bot j
    rw [eq_bot_iff]
    intro g hg
    have h1 : g ∈ d.boxProd (fun i => decide (i = j)) := d.coe_rootGroup_subset_boxProd j hg
    have h2 : g ∈ d.boxProd P := hT (h hg)
    have h3 : g ∈ d.boxProd (fun i => decide (i = j) && P i) := by
      rw [← boxProd_inter]
      exact ⟨h1, h2⟩
    have hP' : (fun i => decide (i = j) && P i) = fun _ => false := by
      funext i
      by_cases hi : i = j
      · subst hi
        simp [hP]
      · simp [hi]
    rw [hP', boxProd_false] at h3
    exact h3
  · exfalso
    apply d.rootGroup_ne_bot j
    rw [eq_bot_iff]
    intro g hg
    have h1 : MulAut.conj d.w₀ • g ∈ T := h (smul_mem_pointwise_smul _ _ _ hg)
    have h2 : MulAut.conj d.w₀ • g ∈ d.conjB d.w₀ ⊓ d.S := by
      refine ⟨?_, d.boxProd_subset_S P (hT h1)⟩
      rw [conjB, d.w₀_inv]
      exact smul_mem_pointwise_smul _ _ _ (le_sup_left (a := d.S) (d.rootGroup_le_S j hg))
    rw [d.conjB_w₀_inf_S_eq_bot, mem_bot, MulAut.smul_def, MulAut.conj_apply,
      conj_eq_one_iff] at h2
    exact h2

@[expose] def Respects (P : Fin 6 → Bool) (k : Fin 12) : Prop :=
  ∀ i, P i = true → (wordAct (weylList k) (false, i)).1 = false ∧
    P (wordAct (weylList k) (false, i)).2 = true

instance (P : Fin 6 → Bool) (k : Fin 12) : Decidable (Respects P k) := by
  unfold Respects
  infer_instance

theorem respects_of_mem_normalizer {T : Subgroup X} {P : Fin 6 → Bool}
    (hT : (T : Set X) ⊆ d.boxProd P) (hP : ∀ i, P i = true → d.rootGroup i ≤ T) {k : Fin 12}
    (hk : d.weylWord k ∈ normalizer (T : Set X)) : Respects P k := by
  intro i hi
  refine d.wordAct_of_smul_rootGroup_le hT ?_
  rintro _ ⟨g, hg, rfl⟩
  exact (mem_normalizer_iff.1 hk g).1 (hP i hi hg)

theorem respects_patV {k : Fin 12} (h : Respects patV k) : k = 0 ∨ k = 1 := by
  revert k
  decide

theorem respects_patD {k : Fin 12} (h : Respects patD k) : k = 0 ∨ k = 1 := by
  revert k
  decide

theorem respects_patY {k : Fin 12} (h : Respects patY k) : k = 0 ∨ k = 2 := by
  revert k
  decide

theorem respects_patW {k : Fin 12} (h : Respects patW k) : k = 0 ∨ k = 2 := by
  revert k
  decide

theorem respects_patM {k : Fin 12} (h : Respects patM k) : k = 0 ∨ k = 2 := by
  revert k
  decide

theorem coe_V_subset_boxProd : (d.V : Set X) ⊆ d.boxProd patV := by
  rintro _ ⟨c, rfl⟩
  refine ⟨(0, 0, 0, 0, 0, c), ?_, ?_⟩
  · simp [box, coordSet, patV]
  · simp [sixProd, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, d.x₅_zero]

theorem coe_Y_subset_boxProd : (d.Y : Set X) ⊆ d.boxProd patY := by
  intro g hg
  obtain ⟨a₅, a₆, rfl⟩ := d.mem_Y_coords hg
  exact ⟨_, by simp [box, coordSet, patY], rfl⟩

theorem coe_W_subset_boxProd : (d.W : Set X) ⊆ d.boxProd patW := by
  intro g hg
  obtain ⟨a₄, a₅, a₆, rfl⟩ := d.mem_W_coords hg
  exact ⟨_, by simp [box, coordSet, patW], rfl⟩

theorem coe_D_subset_boxProd : (d.D : Set X) ⊆ d.boxProd patD := by
  intro g hg
  obtain ⟨a₂, a₃, a₄, a₅, a₆, rfl⟩ := d.mem_D_coords hg
  exact ⟨_, by simp [box, coordSet, patD], rfl⟩

theorem coe_M_subset_boxProd : (d.M : Set X) ⊆ d.boxProd patM := by
  intro g hg
  obtain ⟨a₁, a₃, a₄, a₅, a₆, rfl⟩ := d.mem_M_coords hg
  exact ⟨_, by simp [box, coordSet, patM], rfl⟩

theorem rootGroup_le_V {i : Fin 6} (h : patV i = true) : d.rootGroup i ≤ d.V := by
  fin_cases i <;> simp [patV] at h
  exact le_rfl

theorem rootGroup_le_Y {i : Fin 6} (h : patY i = true) : d.rootGroup i ≤ d.Y := by
  fin_cases i <;> simp [patY] at h
  · exact d.U₅_le_Y
  · exact d.V_le_Y

theorem rootGroup_le_W {i : Fin 6} (h : patW i = true) : d.rootGroup i ≤ d.W := by
  fin_cases i <;> simp [patW] at h
  · exact d.U₄_le_W
  · exact d.U₅_le_Y.trans d.Y_le_W
  · exact d.V_le_Y.trans d.Y_le_W

theorem rootGroup_le_D {i : Fin 6} (h : patD i = true) : d.rootGroup i ≤ d.D := by
  fin_cases i <;> simp [patD] at h
  · exact d.U₂_le_D
  · exact d.U₃_le_F.trans d.F_le_D
  · exact d.U₄_le_W.trans (d.W_le_F.trans d.F_le_D)
  · exact d.U₅_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D))
  · exact d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D))

theorem rootGroup_le_M {i : Fin 6} (h : patM i = true) : d.rootGroup i ≤ d.M := by
  fin_cases i <;> simp [patM] at h
  · exact d.U₁_le_M
  · exact d.U₃_le_F.trans d.F_le_M
  · exact d.U₄_le_W.trans (d.W_le_F.trans d.F_le_M)
  · exact d.U₅_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_M))
  · exact d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_M))

theorem B_le_normalizer_V : d.B ≤ normalizer (d.V : Set X) :=
  sup_le d.S_le_normalizer_V d.J_le_normalizer_V

theorem B_le_normalizer_Y : d.B ≤ normalizer (d.Y : Set X) :=
  sup_le d.S_le_normalizer_Y d.J_le_normalizer_Y

theorem B_le_normalizer_W : d.B ≤ normalizer (d.W : Set X) :=
  sup_le d.S_le_normalizer_W d.J_le_normalizer_W

theorem B_le_normalizer_D : d.B ≤ normalizer (d.D : Set X) :=
  sup_le d.S_le_normalizer_D d.J_le_normalizer_D

theorem B_le_normalizer_M : d.B ≤ normalizer (d.M : Set X) :=
  sup_le d.S_le_normalizer_M d.J_le_normalizer_M

theorem u_mem_normalizer_D : d.u ∈ normalizer (d.D : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype (show ∀ n ∈ d.U₂ ⊔ (d.U₃ ⊔ (d.U₄ ⊔ (d.U₅ ⊔ d.U₆))),
    d.u * n * d.u⁻¹ ∈ d.D from ?_)
  refine conj_mem_sup ?_ (conj_mem_sup ?_ (conj_mem_sup ?_ (conj_mem_sup ?_ ?_))) <;>
    rintro _ ⟨a, rfl⟩
  · rw [d.u_conj_x₂]
    exact d.F_le_D (d.x₅_mem_F a)
  · rw [d.u_conj_x₃_eq_x₄]
    exact d.F_le_D (d.x₄_mem_F a)
  · rw [d.u_conj_x₄_eq_x₃]
    exact d.F_le_D (d.x₃_mem_F a)
  · rw [d.u_conj_x₅]
    exact d.x₂_mem_D a
  · rw [d.u_conj_x₆]
    exact d.F_le_D (d.x₆_mem_F a)

theorem v_mem_normalizer_Y : d.v ∈ normalizer (d.Y : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype (show ∀ n ∈ d.U₅ ⊔ d.U₆, d.v * n * d.v⁻¹ ∈ d.Y from ?_)
  refine conj_mem_sup ?_ ?_ <;> rintro _ ⟨a, rfl⟩
  · rw [d.v_conj_x₅]
    exact d.x₆_mem_Y a
  · rw [d.v_conj_x₆]
    exact d.x₅_mem_Y a

theorem v_mem_normalizer_W_of_Y : d.v ∈ normalizer (d.W : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype (show ∀ n ∈ d.U₄ ⊔ d.Y, d.v * n * d.v⁻¹ ∈ d.W from ?_)
  refine conj_mem_sup ?_ fun n hn => d.Y_le_W ((mem_normalizer_iff.1 d.v_mem_normalizer_Y n).1 hn)
  rintro _ ⟨a, rfl⟩
  rw [d.v_conj_x₄]
  exact d.x₄_mem_W a

theorem v_mem_normalizer_M : d.v ∈ normalizer (d.M : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype (show ∀ n ∈ d.U₁ ⊔ (d.U₃ ⊔ d.W), d.v * n * d.v⁻¹ ∈ d.M from ?_)
  refine conj_mem_sup ?_ (conj_mem_sup ?_ fun n hn => d.F_le_M (d.W_le_F
    ((mem_normalizer_iff.1 d.v_mem_normalizer_W_of_Y n).1 hn))) <;> rintro _ ⟨a, rfl⟩
  · rw [d.v_conj_x₁]
    exact d.F_le_M (d.x₃_mem_F a)
  · rw [d.v_conj_x₃]
    exact d.x₁_mem_M a

theorem exists_bruhat_of_mem_normalizer {T : Subgroup X} {P : Fin 6 → Bool}
    (hB : d.B ≤ normalizer (T : Set X)) (hT : (T : Set X) ⊆ d.boxProd P)
    (hP : ∀ i, P i = true → d.rootGroup i ≤ T) {g : X} (hg : g ∈ normalizer (T : Set X)) :
    ∃ k, Respects P k ∧ ∃ x ∈ d.S, ∃ h ∈ d.J, ∃ y ∈ d.Uminus (d.weylWord k),
      g = x * h * d.weylWord k * y := by
  obtain ⟨x, hx, h, hh, w, hw, y, hy, rfl⟩ := d.exists_bruhat_normal_form g
  obtain ⟨k, rfl⟩ := d.exists_weylWord_eq hw
  refine ⟨k, d.respects_of_mem_normalizer hT hP ?_, x, hx, h, hh, y, hy, rfl⟩
  have hxh : x * h ∈ normalizer (T : Set X) :=
    hB (mul_mem (le_sup_left (a := d.S) hx) (le_sup_right (a := d.S) hh))
  have hy' : y ∈ normalizer (T : Set X) := hB (le_sup_left (a := d.S) (d.Uminus_le_S _ hy))
  have := mul_mem (mul_mem (inv_mem hxh) hg) (inv_mem hy')
  rwa [show (x * h)⁻¹ * (x * h * d.weylWord k * y) * y⁻¹ = d.weylWord k by group] at this

theorem normalizer_le_of_weylWord {T T' : Subgroup X} (hB : d.B ≤ normalizer (T : Set X))
    (hB' : d.B ≤ normalizer (T' : Set X))
    (h : ∀ k, d.weylWord k ∈ normalizer (T : Set X) → d.weylWord k ∈ normalizer (T' : Set X)) :
    normalizer (T : Set X) ≤ normalizer (T' : Set X) := by
  intro g hg
  obtain ⟨b₁, hb₁, w, hw, b₂, hb₂, rfl⟩ := d.bruhat g
  obtain ⟨k, rfl⟩ := d.exists_weylWord_eq hw
  have hk : d.weylWord k ∈ normalizer (T : Set X) := by
    have := mul_mem (mul_mem (inv_mem (hB hb₁)) hg) (inv_mem (hB hb₂))
    rwa [show b₁⁻¹ * (b₁ * d.weylWord k * b₂) * b₂⁻¹ = d.weylWord k by group] at this
  exact mul_mem (mul_mem (hB' hb₁) (h k hk)) (hB' hb₂)

theorem Uminus_u : d.Uminus d.u = d.U₁ := by
  rw [← d.weylWord_one]
  refine le_antisymm (iSup₂_le fun i hi => ?_) ?_
  · rw [rootGroup_le_conjS_iff, Bool.not_eq_true] at hi
    have hi0 : i = 0 := by
      revert i
      decide
    subst hi0
    exact le_rfl
  · refine le_iSup₂_of_le (f := fun i (_ : ¬ d.rootGroup i ≤ d.conjS (d.weylWord 1)) =>
      d.rootGroup i) 0 ?_ le_rfl
    rw [rootGroup_le_conjS_iff]
    decide

theorem Uminus_v : d.Uminus d.v = d.U₂ := by
  rw [← d.weylWord_two]
  refine le_antisymm (iSup₂_le fun i hi => ?_) ?_
  · rw [rootGroup_le_conjS_iff, Bool.not_eq_true] at hi
    have hi1 : i = 1 := by
      revert i
      decide
    subst hi1
    exact le_rfl
  · refine le_iSup₂_of_le (f := fun i (_ : ¬ d.rootGroup i ≤ d.conjS (d.weylWord 2)) =>
      d.rootGroup i) 1 ?_ le_rfl
    rw [rootGroup_le_conjS_iff]
    decide

theorem mul_mem_B_of_Uminus {x h y : X} (hx : x ∈ d.S) (hh : h ∈ d.J) (hy : y ∈ d.S) :
    x * h * 1 * y ∈ d.B := by
  rw [mul_one]
  exact mul_mem (mul_mem (le_sup_left (a := d.S) hx) (le_sup_right (a := d.S) hh))
    (le_sup_left (a := d.S) hy)

theorem normalizer_V_cases {g : X} (hg : g ∈ normalizer (d.V : Set X)) :
    g ∈ d.B ∨ ∃ x ∈ d.S, ∃ h ∈ d.J, ∃ y ∈ d.U₁, g = x * h * d.u * y := by
  obtain ⟨k, hk, x, hx, h, hh, y, hy, rfl⟩ := d.exists_bruhat_of_mem_normalizer
    d.B_le_normalizer_V d.coe_V_subset_boxProd (fun _ hi => d.rootGroup_le_V hi) hg
  rcases respects_patV hk with rfl | rfl
  · rw [weylWord_zero]
    exact Or.inl (d.mul_mem_B_of_Uminus hx hh (d.Uminus_le_S _ hy))
  · rw [weylWord_one] at hy ⊢
    rw [Uminus_u] at hy
    exact Or.inr ⟨x, hx, h, hh, y, hy, rfl⟩

theorem normalizer_Y_cases {g : X} (hg : g ∈ normalizer (d.Y : Set X)) :
    g ∈ d.B ∨ ∃ x ∈ d.S, ∃ h ∈ d.J, ∃ y ∈ d.U₂, g = x * h * d.v * y := by
  obtain ⟨k, hk, x, hx, h, hh, y, hy, rfl⟩ := d.exists_bruhat_of_mem_normalizer
    d.B_le_normalizer_Y d.coe_Y_subset_boxProd (fun _ hi => d.rootGroup_le_Y hi) hg
  rcases respects_patY hk with rfl | rfl
  · rw [weylWord_zero]
    exact Or.inl (d.mul_mem_B_of_Uminus hx hh (d.Uminus_le_S _ hy))
  · rw [weylWord_two] at hy ⊢
    rw [Uminus_v] at hy
    exact Or.inr ⟨x, hx, h, hh, y, hy, rfl⟩

theorem normalizer_V_eq_normalizer_D :
    normalizer (d.V : Set X) = normalizer (d.D : Set X) := by
  have key : ∀ {P : Fin 6 → Bool}, (∀ {k}, Respects P k → k = 0 ∨ k = 1) →
      ∀ {T T' : Subgroup X}, d.B ≤ normalizer (T : Set X) → d.B ≤ normalizer (T' : Set X) →
      (T : Set X) ⊆ d.boxProd P → (∀ i, P i = true → d.rootGroup i ≤ T) →
      d.u ∈ normalizer (T' : Set X) → normalizer (T : Set X) ≤ normalizer (T' : Set X) := by
    intro P hP T T' hB hB' hT hPT hu
    refine d.normalizer_le_of_weylWord hB hB' fun k hk => ?_
    rcases hP (d.respects_of_mem_normalizer hT hPT hk) with rfl | rfl
    · rw [weylWord_zero]
      exact one_mem _
    · rwa [weylWord_one]
  exact le_antisymm
    (key respects_patV d.B_le_normalizer_V d.B_le_normalizer_D d.coe_V_subset_boxProd
      (fun _ hi => d.rootGroup_le_V hi) d.u_mem_normalizer_D)
    (key respects_patD d.B_le_normalizer_D d.B_le_normalizer_V d.coe_D_subset_boxProd
      (fun _ hi => d.rootGroup_le_D hi) d.u_mem_normalizer_V)

theorem normalizer_Y_eq_normalizer_W_and_M :
    normalizer (d.Y : Set X) = normalizer (d.W : Set X) ∧
      normalizer (d.Y : Set X) = normalizer (d.M : Set X) := by
  have key : ∀ {P : Fin 6 → Bool}, (∀ {k}, Respects P k → k = 0 ∨ k = 2) →
      ∀ {T T' : Subgroup X}, d.B ≤ normalizer (T : Set X) → d.B ≤ normalizer (T' : Set X) →
      (T : Set X) ⊆ d.boxProd P → (∀ i, P i = true → d.rootGroup i ≤ T) →
      d.v ∈ normalizer (T' : Set X) → normalizer (T : Set X) ≤ normalizer (T' : Set X) := by
    intro P hP T T' hB hB' hT hPT hv
    refine d.normalizer_le_of_weylWord hB hB' fun k hk => ?_
    rcases hP (d.respects_of_mem_normalizer hT hPT hk) with rfl | rfl
    · rw [weylWord_zero]
      exact one_mem _
    · rwa [weylWord_two]
  refine ⟨le_antisymm (key respects_patY d.B_le_normalizer_Y d.B_le_normalizer_W
      d.coe_Y_subset_boxProd (fun _ hi => d.rootGroup_le_Y hi) d.v_mem_normalizer_W_of_Y)
    (key respects_patW d.B_le_normalizer_W d.B_le_normalizer_Y d.coe_W_subset_boxProd
      (fun _ hi => d.rootGroup_le_W hi) d.v_mem_normalizer_Y),
    le_antisymm (key respects_patY d.B_le_normalizer_Y d.B_le_normalizer_M
      d.coe_Y_subset_boxProd (fun _ hi => d.rootGroup_le_Y hi) d.v_mem_normalizer_M)
    (key respects_patM d.B_le_normalizer_M d.B_le_normalizer_Y d.coe_M_subset_boxProd
      (fun _ hi => d.rootGroup_le_M hi) d.v_mem_normalizer_Y)⟩

@[expose] def leviShort : Subgroup X := closure ((d.U₁ : Set X) ∪ {d.u})

theorem U₁_le_leviShort : d.U₁ ≤ d.leviShort := fun _ hg => subset_closure (Or.inl hg)

theorem u_mem_leviShort : d.u ∈ d.leviShort := subset_closure (Or.inr rfl)

theorem x₁_mem_leviShort (a : d.Γ) : d.x₁ a ∈ d.leviShort :=
  d.U₁_le_leviShort (d.x₁_mem_U₁ a)

theorem u_mem_centralizer_V : d.u ∈ centralizer (d.V : Set X) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  calc d.x₆ b * d.u = d.u * d.x₆ b * d.u * d.u := by rw [d.u_x₆]
    _ = d.u * d.x₆ b := by rw [mul_assoc _ d.u, d.u_mul_self, mul_one]

theorem leviShort_le_centralizer_V : d.leviShort ≤ centralizer (d.V : Set X) := by
  rw [leviShort, closure_le]
  rintro g (⟨a, rfl⟩ | rfl)
  · rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    exact (d.commute₁₆ a b).symm.eq
  · exact d.u_mem_centralizer_V

theorem leviShort_le_normalizer_V : d.leviShort ≤ normalizer (d.V : Set X) :=
  d.leviShort_le_centralizer_V.trans (centralizer_le_normalizer _)

theorem w₀_conj_mem_leviShort {g : X} (hg : g ∈ d.leviShort) :
    d.w₀ * g * d.w₀ ∈ d.leviShort := by
  have h : d.leviShort ≤ d.leviShort.comap (MulAut.conj d.w₀).toMonoidHom := by
    rw [leviShort, closure_le]
    rintro g (⟨a, rfl⟩ | rfl) <;>
      simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        d.w₀_inv]
    · rw [d.w₀_conj_x₁]
      exact mul_mem (mul_mem d.u_mem_leviShort (d.x₁_mem_leviShort a)) d.u_mem_leviShort
    · have e : d.w₀ * d.u * d.w₀ = d.u := by
        rw [show d.w₀ * d.u = d.u * d.w₀ from (d.gen_mul_w₀ false).symm, mul_assoc,
          d.w₀_mul_self, mul_one]
      rw [e]
      exact d.u_mem_leviShort
  simpa [d.w₀_inv] using h hg

theorem exists_x₁_u_of_mem_cell {x h y : X} (hx : x ∈ d.S) (hh : h ∈ d.J) (hy : y ∈ d.U₁) :
    ∃ a, ∃ b ∈ d.B, x * h * d.u * y = d.x₁ a * d.u * b := by
  obtain ⟨a, m, hm, rfl⟩ := d.mem_S_iff.1 hx
  refine ⟨a, (d.u * m * d.u) * (d.u * h * d.u) * y, ?_, ?_⟩
  · refine mul_mem (mul_mem (le_sup_left (a := d.S) (d.D_le_S ?_))
      (le_sup_right (a := d.S) ?_)) (le_sup_left (a := d.S) (d.U₁_le_S hy))
    · have := (mem_normalizer_iff.1 d.u_mem_normalizer_D m).1 hm
      rwa [d.u_inv] at this
    · have := d.conj_mem_J (d.gen_mem_weyl false) hh
      rwa [show d.gen false = d.u from rfl, d.u_inv] at this
  · have uu : d.u * d.u = 1 := d.u_mul_self
    calc d.x₁ a * m * h * d.u * y = d.x₁ a * (d.u * d.u) * m * (d.u * d.u) * h * d.u * y := by
          rw [uu]
          group
      _ = d.x₁ a * d.u * (d.u * m * d.u * (d.u * h * d.u) * y) := by group

theorem eq_one_of_conj_w₀_mem_normalizer_V {n : X} (hn : n ∈ d.D)
    (h : d.w₀ * n * d.w₀ ∈ normalizer (d.V : Set X)) : n = 1 := by
  rcases d.normalizer_V_cases h with hB | ⟨x, hx, t, ht, y, hy, he⟩
  · have h1 : n ∈ d.conjB d.w₀ ⊓ d.S := by
      refine Subgroup.mem_inf.2 ⟨mem_conj_inv_smul.2 ?_, d.D_le_S hn⟩
      rw [d.w₀_inv]
      exact hB
    rw [d.conjB_w₀_inf_S_eq_bot] at h1
    exact h1
  · exfalso
    obtain ⟨a, b, hb, he'⟩ := d.exists_x₁_u_of_mem_cell hx ht hy
    rw [he'] at he
    have hun : d.u * n * d.u ∈ d.D := by
      have := (mem_normalizer_iff.1 d.u_mem_normalizer_D n).1 hn
      rwa [d.u_inv] at this
    have hw₀u : d.u * d.w₀ = d.w₀ * d.u := d.gen_mul_w₀ false
    have hx₁ : d.w₀ * d.x₁ a * d.w₀ = d.u * d.x₁ a * d.u := d.w₀_conj_x₁ a
    have hnw : n * d.w₀ = d.w₀ * (d.x₁ a * d.u * b) := by
      rw [← he]
      calc n * d.w₀ = (d.w₀ * d.w₀) * n * d.w₀ := by rw [d.w₀_mul_self, one_mul]
        _ = d.w₀ * (d.w₀ * n * d.w₀) := by group
    have huw : d.u * d.w₀⁻¹ * d.u = d.w₀ := by
      rw [d.w₀_inv, hw₀u, mul_assoc, d.u_mul_self, mul_one]
    have hux : d.u * d.w₀ * d.x₁ a * d.u = d.x₁ a * d.w₀ := by
      calc d.u * d.w₀ * d.x₁ a * d.u = d.u * (d.w₀ * d.x₁ a * d.w₀) * (d.w₀⁻¹ * d.u) := by
            group
        _ = d.u * d.u * d.x₁ a * (d.u * d.w₀⁻¹ * d.u) := by rw [hx₁]; group
        _ = d.x₁ a * d.w₀ := by rw [d.u_mul_self, one_mul, huw]
    have key : (d.x₁ a)⁻¹ * (d.u * n * d.u) * (d.u * d.w₀) * b⁻¹ = d.w₀ := by
      calc (d.x₁ a)⁻¹ * (d.u * n * d.u) * (d.u * d.w₀) * b⁻¹
          = (d.x₁ a)⁻¹ * d.u * n * (d.u * d.u) * d.w₀ * b⁻¹ := by group
        _ = (d.x₁ a)⁻¹ * d.u * (n * d.w₀) * b⁻¹ := by rw [d.u_mul_self]; group
        _ = (d.x₁ a)⁻¹ * (d.u * d.w₀ * d.x₁ a * d.u) * (b * b⁻¹) := by rw [hnw]; group
        _ = d.w₀ := by rw [hux, mul_inv_cancel, mul_one]; group
    have h1 := d.bruhat_disjoint (d.u * d.w₀) (mul_mem (d.gen_mem_weyl false) d.w₀_mem_weyl)
      d.w₀ d.w₀_mem_weyl ((d.x₁ a)⁻¹ * (d.u * n * d.u))
      (mul_mem (le_sup_left (a := d.S) (inv_mem (d.U₁_le_S (d.x₁_mem_U₁ a))))
        (le_sup_left (a := d.S) (d.D_le_S hun))) b⁻¹ (inv_mem hb) key
    exact d.u_ne_one (by simpa using congrArg (· * d.w₀⁻¹) h1)

theorem exists_eq_mul_of_mem_leviShort_of_mem_B {g : X} (hg : g ∈ d.leviShort)
    (hB : g ∈ d.B) : ∃ x ∈ d.U₁, ∃ h ∈ d.J₆, g = x * h := by
  obtain ⟨x, hx, h, hh, rfl⟩ := d.mem_B_iff.1 hB
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hx
  have h1 : d.w₀ * (d.x₁ a * n * h) * d.w₀ ∈ normalizer (d.V : Set X) :=
    d.leviShort_le_normalizer_V (d.w₀_conj_mem_leviShort hg)
  have hx₁ : d.w₀ * d.x₁ a * d.w₀ ∈ normalizer (d.V : Set X) := by
    rw [d.w₀_conj_x₁]
    exact d.leviShort_le_normalizer_V
      (mul_mem (mul_mem d.u_mem_leviShort (d.x₁_mem_leviShort a)) d.u_mem_leviShort)
  have hh' : d.w₀ * h * d.w₀ ∈ normalizer (d.V : Set X) := by
    have := d.conj_mem_J d.w₀_mem_weyl hh
    rw [d.w₀_inv] at this
    exact d.J_le_normalizer_V this
  have h2 := mul_mem (mul_mem (inv_mem hx₁) h1) (inv_mem hh')
  rw [show (d.w₀ * d.x₁ a * d.w₀)⁻¹ * (d.w₀ * (d.x₁ a * n * h) * d.w₀) * (d.w₀ * h * d.w₀)⁻¹ =
    d.w₀⁻¹ * n * d.w₀⁻¹ by group, d.w₀_inv] at h2
  obtain rfl := d.eq_one_of_conj_w₀_mem_normalizer_V hn h2
  refine ⟨d.x₁ a, d.x₁_mem_U₁ a, h, ⟨hh, ?_⟩, by rw [mul_one]⟩
  have hc := mul_mem (inv_mem (d.leviShort_le_centralizer_V (d.x₁_mem_leviShort a)))
    (d.leviShort_le_centralizer_V hg)
  rwa [mul_one, inv_mul_cancel_left] at hc

theorem u_conj_eq_inv_of_mem_J₆ {t : X} (ht : t ∈ d.J₆) : d.u * t * d.u = t⁻¹ := by
  obtain ⟨⟨l, m⟩, rfl, hlm⟩ := d.mem_J₆.1 ht
  rw [u_torus_eq, ← map_inv]
  congr 1
  refine Prod.ext (Units.ext ?_) rfl
  simp only [Units.val_mul, coe_nmUnits, Prod.fst_inv, Units.val_inv_eq_inv_val]
  dsimp only at hlm
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hlm]
  ring

theorem u_x₁_u_not_mem_B {a : d.Γ} (ha : a ≠ 0) : d.u * d.x₁ a * d.u ∉ d.B := by
  intro hB
  have h1 : d.x₁ a ∈ d.Uminus (d.weylWord 1) ⊓ d.conjB (d.weylWord 1) := by
    refine Subgroup.mem_inf.2 ⟨?_, mem_conj_inv_smul.2 ?_⟩
    · rw [weylWord_one, Uminus_u]
      exact d.x₁_mem_U₁ a
    · rw [weylWord_one, d.u_inv]
      exact hB
  rw [d.Uminus_inf_conjB, mem_bot] at h1
  exact ha (d.x₁_injective (h1.trans d.x₁_zero.symm))

theorem exists_mul_self_eq_of_mem_J₆ {t : X} (ht : t ∈ d.J₆) : ∃ s ∈ d.J₆, s * s = t := by
  rw [d.J₆_eq_range_hBCD] at ht ⊢
  obtain ⟨γ, rfl⟩ := ht
  obtain ⟨β, rfl⟩ := d.sq_surjective_units γ
  exact ⟨d.hBCD β, ⟨β, rfl⟩, by rw [← map_mul, sq]⟩

theorem J₆_le_leviShort : d.J₆ ≤ d.leviShort := by
  have hg : d.u * d.x₁ 1 * d.u ∈ d.leviShort :=
    mul_mem (mul_mem d.u_mem_leviShort (d.x₁_mem_leviShort 1)) d.u_mem_leviShort
  rcases d.normalizer_V_cases (d.leviShort_le_normalizer_V hg) with hB | ⟨x, hx, h, hh, y, hy, he⟩
  · exact absurd hB (d.u_x₁_u_not_mem_B one_ne_zero)
  have hyK : y ∈ d.leviShort := d.U₁_le_leviShort hy
  have hxh : x * h ∈ d.leviShort := by
    have := mul_mem (mul_mem hg (inv_mem hyK)) d.u_mem_leviShort
    rwa [he, show x * h * d.u * y * y⁻¹ * d.u = x * h * (d.u * d.u) by group, d.u_mul_self,
      mul_one] at this
  obtain ⟨x', hx', h', hh', hxh'⟩ := d.exists_eq_mul_of_mem_leviShort_of_mem_B hxh
    (mul_mem (le_sup_left (a := d.S) hx) (le_sup_right (a := d.S) hh))
  have hh'K : h' ∈ d.leviShort := by
    have := mul_mem (inv_mem (d.U₁_le_leviShort hx')) hxh
    rwa [hxh', inv_mul_cancel_left] at this
  have hsq : ∀ t ∈ d.J₆, t * t ∈ d.leviShort := by
    intro t ht
    have hut : d.u * t * d.u = t⁻¹ := d.u_conj_eq_inv_of_mem_J₆ ht
    have htJ : t ∈ d.J := ht.1
    have hcomm : h' * t⁻¹ = t⁻¹ * h' := by
      obtain ⟨p, rfl⟩ := d.mem_J.1 hh'.1
      obtain ⟨r, rfl⟩ := d.mem_J.1 htJ
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm]
    have hconj : t⁻¹ * (d.u * d.x₁ 1 * d.u) * t ∈ d.leviShort := by
      have e : t⁻¹ * (d.u * d.x₁ 1 * d.u) * t = d.u * (t * d.x₁ 1 * t⁻¹) * d.u := by
        calc t⁻¹ * (d.u * d.x₁ 1 * d.u) * t = (d.u * t * d.u) * (d.u * d.x₁ 1 * d.u) * t := by
              rw [hut]
          _ = d.u * t * (d.u * d.u) * d.x₁ 1 * d.u * t := by group
          _ = d.u * (t * d.x₁ 1 * t⁻¹) * (t * d.u * t) := by rw [d.u_mul_self]; group
          _ = d.u * (t * d.x₁ 1 * t⁻¹) * d.u := by
            congr 1
            calc t * d.u * t = d.u * (d.u * t * d.u) * t := by
                  rw [← mul_assoc, ← mul_assoc, d.u_mul_self, one_mul]
              _ = d.u := by rw [hut, mul_assoc, inv_mul_cancel, mul_one]
      rw [e]
      obtain ⟨p, rfl⟩ := d.mem_J.1 htJ
      rw [d.torus_x₁]
      exact mul_mem (mul_mem d.u_mem_leviShort (d.x₁_mem_leviShort _)) d.u_mem_leviShort
    have key : (t⁻¹ * x' * t)⁻¹ * (t⁻¹ * (d.u * d.x₁ 1 * d.u) * t) * (t⁻¹ * y * t)⁻¹ * d.u =
        h' * (t⁻¹ * t⁻¹) := by
      rw [he, hxh']
      calc (t⁻¹ * x' * t)⁻¹ * (t⁻¹ * (x' * h' * d.u * y) * t) * (t⁻¹ * y * t)⁻¹ * d.u
          = t⁻¹ * h' * (d.u * t * d.u) := by group
        _ = h' * (t⁻¹ * t⁻¹) := by rw [hut, ← hcomm, mul_assoc]
    have hx'K : t⁻¹ * x' * t ∈ d.leviShort := by
      obtain ⟨p, rfl⟩ := d.mem_J.1 htJ
      obtain ⟨c, rfl⟩ := hx'
      rw [← map_inv, show d.torus p⁻¹ * d.x₁ c * d.torus p =
        d.torus p⁻¹ * d.x₁ c * (d.torus p⁻¹)⁻¹ by rw [map_inv, inv_inv], d.torus_x₁]
      exact d.x₁_mem_leviShort _
    have hyK' : t⁻¹ * y * t ∈ d.leviShort := by
      obtain ⟨p, rfl⟩ := d.mem_J.1 htJ
      obtain ⟨c, rfl⟩ := hy
      rw [← map_inv, show d.torus p⁻¹ * d.x₁ c * d.torus p =
        d.torus p⁻¹ * d.x₁ c * (d.torus p⁻¹)⁻¹ by rw [map_inv, inv_inv], d.torus_x₁]
      exact d.x₁_mem_leviShort _
    have h3 : h' * (t⁻¹ * t⁻¹) ∈ d.leviShort := by
      rw [← key]
      exact mul_mem (mul_mem (mul_mem (inv_mem hx'K) hconj) (inv_mem hyK')) d.u_mem_leviShort
    have h4 := mul_mem (inv_mem hh'K) h3
    rw [inv_mul_cancel_left, ← mul_inv_rev] at h4
    exact inv_mem_iff.1 h4
  intro t ht
  obtain ⟨s, hs, rfl⟩ := d.exists_mul_self_eq_of_mem_J₆ ht
  exact hsq s hs

theorem u_mem_weyl : d.u ∈ d.weyl :=
  d.gen_mem_weyl false

theorem v_mem_weyl : d.v ∈ d.weyl :=
  d.gen_mem_weyl true

theorem mem_leviShort_iff {g : X} : g ∈ d.leviShort ↔
    (∃ x ∈ d.U₁, ∃ h ∈ d.J₆, g = x * h) ∨
      ∃ x ∈ d.U₁, ∃ h ∈ d.J₆, ∃ y ∈ d.U₁, g = x * h * d.u * y := by
  constructor
  · intro hg
    rcases d.normalizer_V_cases (d.leviShort_le_normalizer_V hg) with
      hB | ⟨x, hx, h, hh, y, hy, rfl⟩
    · exact Or.inl (d.exists_eq_mul_of_mem_leviShort_of_mem_B hg hB)
    · have hxh : x * h ∈ d.leviShort := by
        have := mul_mem (mul_mem hg (inv_mem (d.U₁_le_leviShort hy))) d.u_mem_leviShort
        rwa [show x * h * d.u * y * y⁻¹ * d.u = x * h * (d.u * d.u) by group, d.u_mul_self,
          mul_one] at this
      obtain ⟨x', hx', h', hh', e⟩ := d.exists_eq_mul_of_mem_leviShort_of_mem_B hxh
        (mul_mem (le_sup_left (a := d.S) hx) (le_sup_right (a := d.S) hh))
      exact Or.inr ⟨x', hx', h', hh', y, hy, by rw [e]⟩
  · rintro (⟨x, hx, h, hh, rfl⟩ | ⟨x, hx, h, hh, y, hy, rfl⟩)
    · exact mul_mem (d.U₁_le_leviShort hx) (d.J₆_le_leviShort hh)
    · exact mul_mem (mul_mem (mul_mem (d.U₁_le_leviShort hx) (d.J₆_le_leviShort hh))
        d.u_mem_leviShort) (d.U₁_le_leviShort hy)

theorem hBCD_injective : Function.Injective d.hBCD := by
  refine d.torus_injective.comp fun a b h => ?_
  have h2 : a ^ 2 = b ^ 2 := congrArg Prod.snd h
  have : (a * b⁻¹) ^ 2 = 1 := by rw [mul_pow, h2, ← mul_pow, mul_inv_cancel, one_pow]
  exact mul_inv_eq_one.1 (d.units_eq_one_of_sq this)

theorem card_J₆ : Nat.card d.J₆ = q ^ 3 - 1 := by
  rw [d.J₆_eq_range_hBCD, ← Nat.card_congr (MonoidHom.ofInjective d.hBCD_injective).toEquiv,
    d.card_units_Γ]

theorem eq_of_mul_eq_mul_of_S_J {x x' h h' : X} (hx : x ∈ d.S) (hx' : x' ∈ d.S) (hh : h ∈ d.J)
    (hh' : h' ∈ d.J) (e : x * h = x' * h') : x = x' ∧ h = h' := by
  have h1 : x'⁻¹ * x ∈ d.S ⊓ d.J := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx') hx, ?_⟩
    rw [show x'⁻¹ * x = h' * h⁻¹ by rw [eq_mul_inv_iff_mul_eq, mul_assoc, e, inv_mul_cancel_left]]
    exact mul_mem hh' (inv_mem hh)
  rw [d.S_inf_J_eq_bot, mem_bot, inv_mul_eq_one] at h1
  subst h1
  exact ⟨rfl, mul_left_cancel e⟩

theorem mul_ne_mul_weyl {x x' h h' w y' : X} (hx : x ∈ d.S) (hx' : x' ∈ d.S) (hh : h ∈ d.J)
    (hh' : h' ∈ d.J) (hw : w ∈ d.weyl) (hw1 : w ≠ 1) (hy' : y' ∈ d.S) :
    x * h ≠ x' * h' * w * y' := by
  intro e
  have hb : (x * h)⁻¹ * (x' * h') ∈ d.B := mul_mem (inv_mem (mul_mem (le_sup_left (a := d.S) hx)
    (le_sup_right (a := d.S) hh))) (mul_mem (le_sup_left (a := d.S) hx')
    (le_sup_right (a := d.S) hh'))
  refine hw1 (d.bruhat_disjoint w hw 1 (one_mem _) _ hb y' (le_sup_left (a := d.S) hy') ?_)
  rw [show (x * h)⁻¹ * (x' * h') * w * y' = (x * h)⁻¹ * (x' * h' * w * y') by group, ← e,
    inv_mul_cancel]

theorem card_leviShort : Nat.card d.leviShort = q ^ 3 * (q ^ 6 - 1) := by
  have := d.finite
  let f₁ : d.U₁ × d.J₆ → X := fun p => (p.1 : X) * p.2
  let f₂ : d.U₁ × d.J₆ × d.U₁ → X := fun p => (p.1 : X) * p.2.1 * d.u * p.2.2
  have hK : (d.leviShort : Set X) = Set.range f₁ ∪ Set.range f₂ := by
    ext g
    simp only [SetLike.mem_coe, mem_leviShort_iff, Set.mem_union, Set.mem_range, Prod.exists,
      Subtype.exists, f₁, f₂]
    constructor
    · rintro (⟨x, hx, h, hh, rfl⟩ | ⟨x, hx, h, hh, y, hy, rfl⟩)
      · exact Or.inl ⟨x, hx, h, hh, rfl⟩
      · exact Or.inr ⟨x, hx, h, hh, y, hy, rfl⟩
    · rintro (⟨x, hx, h, hh, rfl⟩ | ⟨x, hx, h, hh, y, hy, rfl⟩)
      · exact Or.inl ⟨x, hx, h, hh, rfl⟩
      · exact Or.inr ⟨x, hx, h, hh, y, hy, rfl⟩
  have hU : ∀ y ∈ d.U₁, y ∈ d.Uminus d.u := fun y hy => by rwa [Uminus_u]
  have h₁ : Function.Injective f₁ := fun p p' e => by
    obtain ⟨e1, e2⟩ := d.eq_of_mul_eq_mul_of_S_J (d.U₁_le_S p.1.2) (d.U₁_le_S p'.1.2)
      p.2.2.1 p'.2.2.1 e
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  have h₂ : Function.Injective f₂ := fun p p' e => by
    obtain ⟨e1, e2, -, e4⟩ := d.bruhat_normal_form_unique (d.U₁_le_S p.1.2) p.2.1.2.1
      d.u_mem_weyl (hU _ p.2.2.2) (d.U₁_le_S p'.1.2) p'.2.1.2.1 d.u_mem_weyl
      (hU _ p'.2.2.2) e
    exact Prod.ext (Subtype.ext e1) (Prod.ext (Subtype.ext e2) (Subtype.ext e4))
  have hdisj : Disjoint (Set.range f₁) (Set.range f₂) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨p', e⟩
    exact d.mul_ne_mul_weyl (d.U₁_le_S p.1.2) (d.U₁_le_S p'.1.2) p.2.2.1 p'.2.1.2.1
      d.u_mem_weyl d.u_ne_one (d.U₁_le_S p'.2.2.2) e.symm
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hK, Set.ncard_union_eq hdisj (Set.toFinite _)
    (Set.toFinite _), ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_range_of_injective h₁, Nat.card_range_of_injective h₂, Nat.card_prod,
    Nat.card_prod, Nat.card_prod, d.card_U₁, d.card_J₆]
  have hq := d.two_le_q
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h3, h6]
  ring

@[expose] def leviLong : Subgroup X := closure ((d.U₂ : Set X) ∪ {d.v})

theorem U₂_le_leviLong : d.U₂ ≤ d.leviLong := fun _ hg => subset_closure (Or.inl hg)

theorem v_mem_leviLong : d.v ∈ d.leviLong := subset_closure (Or.inr rfl)

theorem x₂_mem_leviLong (a : d.Γ₀) : d.x₂ a ∈ d.leviLong :=
  d.U₂_le_leviLong (d.x₂_mem_U₂ a)

theorem v_mem_centralizer_U₄ : d.v ∈ centralizer (d.U₄ : Set X) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  calc d.x₄ b * d.v = d.v * d.x₄ b * d.v * d.v := by rw [d.v_x₄]
    _ = d.v * d.x₄ b := by rw [mul_assoc _ d.v, d.v_mul_self, mul_one]

theorem leviLong_le_centralizer_U₄ : d.leviLong ≤ centralizer (d.U₄ : Set X) := by
  rw [leviLong, closure_le]
  rintro g (⟨a, rfl⟩ | rfl)
  · rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    exact (d.commute₂₄ a b).symm.eq
  · exact d.v_mem_centralizer_U₄

theorem leviLong_le_normalizer_Y : d.leviLong ≤ normalizer (d.Y : Set X) := by
  rw [leviLong, closure_le]
  rintro g (hg | rfl)
  · exact d.S_le_normalizer_Y (d.U₂_le_S hg)
  · exact d.v_mem_normalizer_Y

theorem w₀_conj_mem_leviLong {g : X} (hg : g ∈ d.leviLong) :
    d.w₀ * g * d.w₀ ∈ d.leviLong := by
  have h : d.leviLong ≤ d.leviLong.comap (MulAut.conj d.w₀).toMonoidHom := by
    rw [leviLong, closure_le]
    rintro g (⟨a, rfl⟩ | rfl) <;>
      simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        d.w₀_inv]
    · rw [d.w₀_conj_x₂]
      exact mul_mem (mul_mem d.v_mem_leviLong (d.x₂_mem_leviLong a)) d.v_mem_leviLong
    · have e : d.w₀ * d.v * d.w₀ = d.v := by
        rw [show d.w₀ * d.v = d.v * d.w₀ from (d.gen_mul_w₀ true).symm, mul_assoc,
          d.w₀_mul_self, mul_one]
      rw [e]
      exact d.v_mem_leviLong
  simpa [d.w₀_inv] using h hg

theorem S_eq_U₂_sup_M : d.S = d.U₂ ⊔ d.M := by
  rw [d.S_eq_sup, D, M, sup_left_comm]

theorem mem_S_iff_x₂ {g : X} : g ∈ d.S ↔ ∃ a, ∃ n ∈ d.M, d.x₂ a * n = g := by
  rw [d.S_eq_U₂_sup_M]
  exact mem_rangeSubgroup_sup_iff d.x₂_add (d.U₂_le_S.trans d.S_le_normalizer_M)

theorem exists_x₂_v_of_mem_cell {x h y : X} (hx : x ∈ d.S) (hh : h ∈ d.J) (hy : y ∈ d.U₂) :
    ∃ a, ∃ b ∈ d.B, x * h * d.v * y = d.x₂ a * d.v * b := by
  obtain ⟨a, m, hm, rfl⟩ := d.mem_S_iff_x₂.1 hx
  refine ⟨a, (d.v * m * d.v) * (d.v * h * d.v) * y, ?_, ?_⟩
  · refine mul_mem (mul_mem (le_sup_left (a := d.S) (d.M_le_S ?_))
      (le_sup_right (a := d.S) ?_)) (le_sup_left (a := d.S) (d.U₂_le_S hy))
    · have := (mem_normalizer_iff.1 d.v_mem_normalizer_M m).1 hm
      rwa [d.v_inv] at this
    · have := d.conj_mem_J d.v_mem_weyl hh
      rwa [d.v_inv] at this
  · have vv : d.v * d.v = 1 := d.v_mul_self
    calc d.x₂ a * m * h * d.v * y = d.x₂ a * (d.v * d.v) * m * (d.v * d.v) * h * d.v * y := by
          rw [vv]
          group
      _ = d.x₂ a * d.v * (d.v * m * d.v * (d.v * h * d.v) * y) := by group

theorem eq_one_of_conj_w₀_mem_normalizer_Y {n : X} (hn : n ∈ d.M)
    (h : d.w₀ * n * d.w₀ ∈ normalizer (d.Y : Set X)) : n = 1 := by
  rcases d.normalizer_Y_cases h with hB | ⟨x, hx, t, ht, y, hy, he⟩
  · have h1 : n ∈ d.conjB d.w₀ ⊓ d.S := by
      refine Subgroup.mem_inf.2 ⟨mem_conj_inv_smul.2 ?_, d.M_le_S hn⟩
      rw [d.w₀_inv]
      exact hB
    rw [d.conjB_w₀_inf_S_eq_bot] at h1
    exact h1
  · exfalso
    obtain ⟨a, b, hb, he'⟩ := d.exists_x₂_v_of_mem_cell hx ht hy
    rw [he'] at he
    have hvn : d.v * n * d.v ∈ d.M := by
      have := (mem_normalizer_iff.1 d.v_mem_normalizer_M n).1 hn
      rwa [d.v_inv] at this
    have hw₀v : d.v * d.w₀ = d.w₀ * d.v := d.gen_mul_w₀ true
    have hx₂ : d.w₀ * d.x₂ a * d.w₀ = d.v * d.x₂ a * d.v := d.w₀_conj_x₂ a
    have hnw : n * d.w₀ = d.w₀ * (d.x₂ a * d.v * b) := by
      rw [← he]
      calc n * d.w₀ = (d.w₀ * d.w₀) * n * d.w₀ := by rw [d.w₀_mul_self, one_mul]
        _ = d.w₀ * (d.w₀ * n * d.w₀) := by group
    have hvw : d.v * d.w₀⁻¹ * d.v = d.w₀ := by
      rw [d.w₀_inv, hw₀v, mul_assoc, d.v_mul_self, mul_one]
    have hvx : d.v * d.w₀ * d.x₂ a * d.v = d.x₂ a * d.w₀ := by
      calc d.v * d.w₀ * d.x₂ a * d.v = d.v * (d.w₀ * d.x₂ a * d.w₀) * (d.w₀⁻¹ * d.v) := by
            group
        _ = d.v * d.v * d.x₂ a * (d.v * d.w₀⁻¹ * d.v) := by rw [hx₂]; group
        _ = d.x₂ a * d.w₀ := by rw [d.v_mul_self, one_mul, hvw]
    have key : (d.x₂ a)⁻¹ * (d.v * n * d.v) * (d.v * d.w₀) * b⁻¹ = d.w₀ := by
      calc (d.x₂ a)⁻¹ * (d.v * n * d.v) * (d.v * d.w₀) * b⁻¹
          = (d.x₂ a)⁻¹ * d.v * n * (d.v * d.v) * d.w₀ * b⁻¹ := by group
        _ = (d.x₂ a)⁻¹ * d.v * (n * d.w₀) * b⁻¹ := by rw [d.v_mul_self]; group
        _ = (d.x₂ a)⁻¹ * (d.v * d.w₀ * d.x₂ a * d.v) * (b * b⁻¹) := by rw [hnw]; group
        _ = d.w₀ := by rw [hvx, mul_inv_cancel, mul_one]; group
    have h1 := d.bruhat_disjoint (d.v * d.w₀) (mul_mem d.v_mem_weyl d.w₀_mem_weyl)
      d.w₀ d.w₀_mem_weyl ((d.x₂ a)⁻¹ * (d.v * n * d.v))
      (mul_mem (le_sup_left (a := d.S) (inv_mem (d.U₂_le_S (d.x₂_mem_U₂ a))))
        (le_sup_left (a := d.S) (d.M_le_S hvn))) b⁻¹ (inv_mem hb) key
    exact d.v_ne_one (by simpa using congrArg (· * d.w₀⁻¹) h1)

theorem exists_eq_mul_of_mem_leviLong_of_mem_B {g : X} (hg : g ∈ d.leviLong)
    (hB : g ∈ d.B) : ∃ x ∈ d.U₂, ∃ h ∈ d.J₄, g = x * h := by
  obtain ⟨x, hx, h, hh, rfl⟩ := d.mem_B_iff.1 hB
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff_x₂.1 hx
  have h1 : d.w₀ * (d.x₂ a * n * h) * d.w₀ ∈ normalizer (d.Y : Set X) :=
    d.leviLong_le_normalizer_Y (d.w₀_conj_mem_leviLong hg)
  have hx₂ : d.w₀ * d.x₂ a * d.w₀ ∈ normalizer (d.Y : Set X) := by
    rw [d.w₀_conj_x₂]
    exact d.leviLong_le_normalizer_Y
      (mul_mem (mul_mem d.v_mem_leviLong (d.x₂_mem_leviLong a)) d.v_mem_leviLong)
  have hh' : d.w₀ * h * d.w₀ ∈ normalizer (d.Y : Set X) := by
    have := d.conj_mem_J d.w₀_mem_weyl hh
    rw [d.w₀_inv] at this
    exact d.J_le_normalizer_Y this
  have h2 := mul_mem (mul_mem (inv_mem hx₂) h1) (inv_mem hh')
  rw [show (d.w₀ * d.x₂ a * d.w₀)⁻¹ * (d.w₀ * (d.x₂ a * n * h) * d.w₀) * (d.w₀ * h * d.w₀)⁻¹ =
    d.w₀⁻¹ * n * d.w₀⁻¹ by group, d.w₀_inv] at h2
  obtain rfl := d.eq_one_of_conj_w₀_mem_normalizer_Y hn h2
  refine ⟨d.x₂ a, d.x₂_mem_U₂ a, h, ⟨hh, ?_⟩, by rw [mul_one]⟩
  have hc := mul_mem (inv_mem (d.leviLong_le_centralizer_U₄ (d.x₂_mem_leviLong a)))
    (d.leviLong_le_centralizer_U₄ hg)
  rwa [mul_one, inv_mul_cancel_left] at hc

theorem v_conj_eq_inv_of_mem_J₄ {t : X} (ht : t ∈ d.J₄) : d.v * t * d.v = t⁻¹ := by
  rw [d.J₄_eq_range_hA] at ht
  obtain ⟨β, rfl⟩ := ht
  rw [hA_apply, v_torus_eq, ← map_inv]
  congr 1
  refine Prod.ext rfl (Units.ext ?_)
  simp [coe_unitsIncl, sq]

theorem v_x₂_v_not_mem_B {a : d.Γ₀} (ha : a ≠ 0) : d.v * d.x₂ a * d.v ∉ d.B := by
  intro hB
  have h1 : d.x₂ a ∈ d.Uminus (d.weylWord 2) ⊓ d.conjB (d.weylWord 2) := by
    refine Subgroup.mem_inf.2 ⟨?_, mem_conj_inv_smul.2 ?_⟩
    · rw [weylWord_two, Uminus_v]
      exact d.x₂_mem_U₂ a
    · rw [weylWord_two, d.v_inv]
      exact hB
  rw [d.Uminus_inf_conjB, mem_bot] at h1
  exact ha (d.x₂_injective (h1.trans d.x₂_zero.symm))

theorem sq_surjective_units₀ (l : (d.Γ₀)ˣ) : ∃ b : (d.Γ₀)ˣ, b ^ 2 = l := by
  have hinj : Function.Injective (powMonoidHom 2 : (d.Γ₀)ˣ →* (d.Γ₀)ˣ) :=
    (injective_iff_map_eq_one _).2 fun _ hb => d.units₀_eq_one_of_sq hb
  exact Finite.injective_iff_surjective.1 hinj l

theorem exists_mul_self_eq_of_mem_J₄ {t : X} (ht : t ∈ d.J₄) : ∃ s ∈ d.J₄, s * s = t := by
  rw [d.J₄_eq_range_hA] at ht ⊢
  obtain ⟨γ, rfl⟩ := ht
  obtain ⟨β, rfl⟩ := d.sq_surjective_units₀ γ
  exact ⟨d.hA β, ⟨β, rfl⟩, by rw [← map_mul, sq]⟩

theorem J₄_le_leviLong : d.J₄ ≤ d.leviLong := by
  have hg : d.v * d.x₂ 1 * d.v ∈ d.leviLong :=
    mul_mem (mul_mem d.v_mem_leviLong (d.x₂_mem_leviLong 1)) d.v_mem_leviLong
  rcases d.normalizer_Y_cases (d.leviLong_le_normalizer_Y hg) with hB | ⟨x, hx, h, hh, y, hy, he⟩
  · exact absurd hB (d.v_x₂_v_not_mem_B one_ne_zero)
  have hyK : y ∈ d.leviLong := d.U₂_le_leviLong hy
  have hxh : x * h ∈ d.leviLong := by
    have := mul_mem (mul_mem hg (inv_mem hyK)) d.v_mem_leviLong
    rwa [he, show x * h * d.v * y * y⁻¹ * d.v = x * h * (d.v * d.v) by group, d.v_mul_self,
      mul_one] at this
  obtain ⟨x', hx', h', hh', hxh'⟩ := d.exists_eq_mul_of_mem_leviLong_of_mem_B hxh
    (mul_mem (le_sup_left (a := d.S) hx) (le_sup_right (a := d.S) hh))
  have hh'K : h' ∈ d.leviLong := by
    have := mul_mem (inv_mem (d.U₂_le_leviLong hx')) hxh
    rwa [hxh', inv_mul_cancel_left] at this
  have hsq : ∀ t ∈ d.J₄, t * t ∈ d.leviLong := by
    intro t ht
    have hvt : d.v * t * d.v = t⁻¹ := d.v_conj_eq_inv_of_mem_J₄ ht
    have htJ : t ∈ d.J := ht.1
    have hcomm : h' * t⁻¹ = t⁻¹ * h' := by
      obtain ⟨p, rfl⟩ := d.mem_J.1 hh'.1
      obtain ⟨r, rfl⟩ := d.mem_J.1 htJ
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm]
    have hconj : t⁻¹ * (d.v * d.x₂ 1 * d.v) * t ∈ d.leviLong := by
      have e : t⁻¹ * (d.v * d.x₂ 1 * d.v) * t = d.v * (t * d.x₂ 1 * t⁻¹) * d.v := by
        calc t⁻¹ * (d.v * d.x₂ 1 * d.v) * t = (d.v * t * d.v) * (d.v * d.x₂ 1 * d.v) * t := by
              rw [hvt]
          _ = d.v * t * (d.v * d.v) * d.x₂ 1 * d.v * t := by group
          _ = d.v * (t * d.x₂ 1 * t⁻¹) * (t * d.v * t) := by rw [d.v_mul_self]; group
          _ = d.v * (t * d.x₂ 1 * t⁻¹) * d.v := by
            congr 1
            calc t * d.v * t = d.v * (d.v * t * d.v) * t := by
                  rw [← mul_assoc, ← mul_assoc, d.v_mul_self, one_mul]
              _ = d.v := by rw [hvt, mul_assoc, inv_mul_cancel, mul_one]
      rw [e]
      obtain ⟨p, rfl⟩ := d.mem_J.1 htJ
      rw [d.torus_x₂]
      exact mul_mem (mul_mem d.v_mem_leviLong (d.x₂_mem_leviLong _)) d.v_mem_leviLong
    have key : (t⁻¹ * x' * t)⁻¹ * (t⁻¹ * (d.v * d.x₂ 1 * d.v) * t) * (t⁻¹ * y * t)⁻¹ * d.v =
        h' * (t⁻¹ * t⁻¹) := by
      rw [he, hxh']
      calc (t⁻¹ * x' * t)⁻¹ * (t⁻¹ * (x' * h' * d.v * y) * t) * (t⁻¹ * y * t)⁻¹ * d.v
          = t⁻¹ * h' * (d.v * t * d.v) := by group
        _ = h' * (t⁻¹ * t⁻¹) := by rw [hvt, ← hcomm, mul_assoc]
    have hx'K : t⁻¹ * x' * t ∈ d.leviLong := by
      obtain ⟨p, rfl⟩ := d.mem_J.1 htJ
      obtain ⟨c, rfl⟩ := hx'
      rw [← map_inv, show d.torus p⁻¹ * d.x₂ c * d.torus p =
        d.torus p⁻¹ * d.x₂ c * (d.torus p⁻¹)⁻¹ by rw [map_inv, inv_inv], d.torus_x₂]
      exact d.x₂_mem_leviLong _
    have hyK' : t⁻¹ * y * t ∈ d.leviLong := by
      obtain ⟨p, rfl⟩ := d.mem_J.1 htJ
      obtain ⟨c, rfl⟩ := hy
      rw [← map_inv, show d.torus p⁻¹ * d.x₂ c * d.torus p =
        d.torus p⁻¹ * d.x₂ c * (d.torus p⁻¹)⁻¹ by rw [map_inv, inv_inv], d.torus_x₂]
      exact d.x₂_mem_leviLong _
    have h3 : h' * (t⁻¹ * t⁻¹) ∈ d.leviLong := by
      rw [← key]
      exact mul_mem (mul_mem (mul_mem (inv_mem hx'K) hconj) (inv_mem hyK')) d.v_mem_leviLong
    have h4 := mul_mem (inv_mem hh'K) h3
    rw [inv_mul_cancel_left, ← mul_inv_rev] at h4
    exact inv_mem_iff.1 h4
  intro t ht
  obtain ⟨s, hs, rfl⟩ := d.exists_mul_self_eq_of_mem_J₄ ht
  exact hsq s hs

theorem mem_leviLong_iff {g : X} : g ∈ d.leviLong ↔
    (∃ x ∈ d.U₂, ∃ h ∈ d.J₄, g = x * h) ∨
      ∃ x ∈ d.U₂, ∃ h ∈ d.J₄, ∃ y ∈ d.U₂, g = x * h * d.v * y := by
  constructor
  · intro hg
    rcases d.normalizer_Y_cases (d.leviLong_le_normalizer_Y hg) with
      hB | ⟨x, hx, h, hh, y, hy, rfl⟩
    · exact Or.inl (d.exists_eq_mul_of_mem_leviLong_of_mem_B hg hB)
    · have hxh : x * h ∈ d.leviLong := by
        have := mul_mem (mul_mem hg (inv_mem (d.U₂_le_leviLong hy))) d.v_mem_leviLong
        rwa [show x * h * d.v * y * y⁻¹ * d.v = x * h * (d.v * d.v) by group, d.v_mul_self,
          mul_one] at this
      obtain ⟨x', hx', h', hh', e⟩ := d.exists_eq_mul_of_mem_leviLong_of_mem_B hxh
        (mul_mem (le_sup_left (a := d.S) hx) (le_sup_right (a := d.S) hh))
      exact Or.inr ⟨x', hx', h', hh', y, hy, by rw [e]⟩
  · rintro (⟨x, hx, h, hh, rfl⟩ | ⟨x, hx, h, hh, y, hy, rfl⟩)
    · exact mul_mem (d.U₂_le_leviLong hx) (d.J₄_le_leviLong hh)
    · exact mul_mem (mul_mem (mul_mem (d.U₂_le_leviLong hx) (d.J₄_le_leviLong hh))
        d.v_mem_leviLong) (d.U₂_le_leviLong hy)

theorem hA_injective : Function.Injective d.hA := by
  refine d.torus_injective.comp fun a b h => ?_
  have h2 : a ^ 2 = b ^ 2 := congrArg Prod.fst h
  have : (a * b⁻¹) ^ 2 = 1 := by rw [mul_pow, h2, ← mul_pow, mul_inv_cancel, one_pow]
  exact mul_inv_eq_one.1 (d.units₀_eq_one_of_sq this)

theorem card_J₄ : Nat.card d.J₄ = q - 1 := by
  rw [d.J₄_eq_range_hA, ← Nat.card_congr (MonoidHom.ofInjective d.hA_injective).toEquiv,
    d.card_units_Γ₀]

theorem card_leviLong : Nat.card d.leviLong = q * (q ^ 2 - 1) := by
  have := d.finite
  let f₁ : d.U₂ × d.J₄ → X := fun p => (p.1 : X) * p.2
  let f₂ : d.U₂ × d.J₄ × d.U₂ → X := fun p => (p.1 : X) * p.2.1 * d.v * p.2.2
  have hK : (d.leviLong : Set X) = Set.range f₁ ∪ Set.range f₂ := by
    ext g
    simp only [SetLike.mem_coe, mem_leviLong_iff, Set.mem_union, Set.mem_range, Prod.exists,
      Subtype.exists, f₁, f₂]
    constructor
    · rintro (⟨x, hx, h, hh, rfl⟩ | ⟨x, hx, h, hh, y, hy, rfl⟩)
      · exact Or.inl ⟨x, hx, h, hh, rfl⟩
      · exact Or.inr ⟨x, hx, h, hh, y, hy, rfl⟩
    · rintro (⟨x, hx, h, hh, rfl⟩ | ⟨x, hx, h, hh, y, hy, rfl⟩)
      · exact Or.inl ⟨x, hx, h, hh, rfl⟩
      · exact Or.inr ⟨x, hx, h, hh, y, hy, rfl⟩
  have hU : ∀ y ∈ d.U₂, y ∈ d.Uminus d.v := fun y hy => by rwa [Uminus_v]
  have h₁ : Function.Injective f₁ := fun p p' e => by
    obtain ⟨e1, e2⟩ := d.eq_of_mul_eq_mul_of_S_J (d.U₂_le_S p.1.2) (d.U₂_le_S p'.1.2)
      p.2.2.1 p'.2.2.1 e
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  have h₂ : Function.Injective f₂ := fun p p' e => by
    obtain ⟨e1, e2, -, e4⟩ := d.bruhat_normal_form_unique (d.U₂_le_S p.1.2) p.2.1.2.1
      d.v_mem_weyl (hU _ p.2.2.2) (d.U₂_le_S p'.1.2) p'.2.1.2.1 d.v_mem_weyl
      (hU _ p'.2.2.2) e
    exact Prod.ext (Subtype.ext e1) (Prod.ext (Subtype.ext e2) (Subtype.ext e4))
  have hdisj : Disjoint (Set.range f₁) (Set.range f₂) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨p', e⟩
    exact d.mul_ne_mul_weyl (d.U₂_le_S p.1.2) (d.U₂_le_S p'.1.2) p.2.2.1 p'.2.1.2.1
      d.v_mem_weyl d.v_ne_one (d.U₂_le_S p'.2.2.2) e.symm
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hK, Set.ncard_union_eq hdisj (Set.toFinite _)
    (Set.toFinite _), ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_range_of_injective h₁, Nat.card_range_of_injective h₂, Nat.card_prod,
    Nat.card_prod, Nat.card_prod, d.card_U₂, d.card_J₄]
  have hq := d.two_le_q
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h2, (by omega : 1 ≤ q)]
  ring

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
