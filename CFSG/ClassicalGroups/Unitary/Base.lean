module

public import CFSG.ClassicalGroups.Unitary.Hyperbolic
public import CFSG.ClassicalGroups.Unitary.Elements

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem det_eq_of_basis {A : Matrix (Fin 2) (Fin 2) K} {a b : Fin 2 → K} {α β γ δ : K}
    (hAa : A *ᵥ a = α • a + γ • b) (hAb : A *ᵥ b = β • a + δ • b)
    (hP : a 0 * b 1 - b 0 * a 1 ≠ 0) : A.det = α * δ - β * γ := by
  have h1 := congrFun hAa 0
  have h2 := congrFun hAa 1
  have h3 := congrFun hAb 0
  have h4 := congrFun hAb 1
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at h1 h2 h3 h4
  have hAP : A * !![a 0, b 0; a 1, b 1] = !![a 0, b 0; a 1, b 1] * !![α, β; γ, δ] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination h1
    · linear_combination h3
    · linear_combination h2
    · linear_combination h4
  have := congrArg Matrix.det hAP
  rw [det_mul, det_mul, det_fin_two_of, det_fin_two_of] at this
  exact mul_right_cancel₀ hP (by linear_combination this)

theorem mem_T_two_of_basis (hσ : IsUnitaryInvolution σ) {a b : Fin 2 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1)
    (hexp : ∀ v, v = herm σ b v • a + herm σ a v • b) (hP : a 0 * b 1 - b 0 * a 1 ≠ 0)
    (A : SUid σ 2) : A ∈ T σ 2 := by
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ.invol, hab, map_one]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at hab
    exact zero_ne_one hab
  have hsmul : ∀ (g : SUid σ 2) (v : Fin 2 → K),
      g • v = herm σ b v • (g • a) + herm σ a v • (g • b) := by
    intro g v
    conv_lhs => rw [hexp v]
    rw [smul_add, smul_comm, smul_comm g (herm σ a v)]
  have key : ∀ A : SUid σ 2, herm σ a (A • a) ≠ 0 → A ∈ T σ 2 := by
    intro A hγ
    set α := herm σ b (A • a) with hα
    set γ := herm σ a (A • a) with hγdef
    set β := herm σ b (A • b) with hβ
    set δ := herm σ a (A • b) with hδ
    have hAa : A • a = α • a + γ • b := hexp _
    have hAb : A • b = β • a + δ • b := hexp _
    have e1 : σ α * γ + σ γ * α = 0 := by
      have := herm_smul_smul σ A a a
      rw [hAa, ha] at this
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab,
        hba] at this
      linear_combination this
    have e2 : σ β * δ + σ δ * β = 0 := by
      have := herm_smul_smul σ A b b
      rw [hAb, hb] at this
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab,
        hba] at this
      linear_combination this
    have e3 : σ α * δ + σ γ * β = 1 := by
      have := herm_smul_smul σ A a b
      rw [hAa, hAb, hab] at this
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab,
        hba] at this
      linear_combination this
    have e3' : α * σ δ + γ * σ β = 1 := by
      have := congrArg σ e3
      simp only [map_add, map_mul, hσ.invol, map_one] at this
      linear_combination this
    have e4 : α * δ - β * γ = 1 := by
      have hdet := ((mem_SUid_iff σ).mp A.2).1
      rw [det_eq_of_basis (a := a) (b := b) hAa hAb hP] at hdet
      exact hdet
    have hσγ : σ γ = -γ := by linear_combination (-σ γ) * e4 + δ * e1 - γ * e3
    have hσα : σ α = α := by linear_combination (-σ α) * e4 + α * e3 - β * e1
    have hσδ : σ δ = δ := by linear_combination (-σ δ) * e4 + δ * e3' - γ * e2
    have hσβ : σ β = -β := by linear_combination (-σ β) * e4 + α * e2 - β * e3'
    have hγE : γ + σ γ = 0 := by rw [hσγ]; ring
    have hx : (α - 1) / γ + σ ((α - 1) / γ) = 0 := by
      rw [map_div₀, map_sub, map_one, hσα, hσγ, div_neg]; ring
    have hy : (δ - 1) / γ + σ ((δ - 1) / γ) = 0 := by
      rw [map_div₀, map_sub, map_one, hσδ, hσγ, div_neg]; ring
    set t := tv hσ.invol ha hx * tv hσ.invol hb hγE * tv hσ.invol ha hy with ht
    have hta : t • a = A • a := by
      rw [ht, mul_smul, mul_smul, tv_smul, tv_smul, tv_smul, hAa]
      simp only [herm_add_right, herm_smul_right, ha, hab, hba, mul_zero, zero_smul,
        add_zero, mul_one]
      match_scalars
      all_goals field_simp
      all_goals ring
    have htb : t • b = A • b := by
      rw [ht, mul_smul, mul_smul, tv_smul, tv_smul, tv_smul, hAb]
      simp only [herm_add_right, herm_smul_right, ha, hb, hab, hba, mul_zero,
        add_zero, mul_one, zero_add]
      match_scalars
      all_goals field_simp
      all_goals first | linear_combination e4 | ring
    have hA : A = t := by
      apply ext_smul
      intro v
      rw [hsmul A v, hsmul t v, hta, htb]
    rw [hA, ht]
    exact (T σ 2).mul_mem ((T σ 2).mul_mem (tv_mem_T _ _ _) (tv_mem_T _ _ _)) (tv_mem_T _ _ _)
  by_cases hγ : herm σ a (A • a) = 0
  · obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
    have hα : herm σ b (A • a) ≠ 0 := by
      intro hα
      have h0 : A • a = 0 := by rw [hexp (A • a), hα, hγ, zero_smul, zero_smul, add_zero]
      exact ha0 ((smul_eq_zero_iff_eq A).mp h0)
    have hB : herm σ a ((tv hσ.invol hb hτ * A) • a) ≠ 0 := by
      rw [mul_smul, tv_smul, herm_add_right, herm_smul_right, hγ, hab, zero_add, mul_one]
      exact mul_ne_zero hτ0 hα
    have hA : A = (tv hσ.invol hb hτ)⁻¹ * (tv hσ.invol hb hτ * A) := by group
    rw [hA]
    exact (T σ 2).mul_mem ((T σ 2).inv_mem (tv_mem_T _ _ _)) (key _ hB)
  · exact key A hγ

namespace WittData

variable (W : WittData σ)

theorem eq_hyp_expansion (hσ : ∀ c, σ (σ c) = c) (v : Fin 2 → K) :
    v = herm σ (W.hypB 0) v • W.hypA 0 + herm σ (W.hypA 0) v • W.hypB 0 := by
  set d := v - (herm σ (W.hypB 0) v • W.hypA 0 + herm σ (W.hypA 0) v • W.hypB 0) with hd
  have h1 : herm σ (W.hypA 0) d = 0 := by
    rw [hd]
    simp only [herm_sub_right, herm_add_right, herm_smul_right, W.herm_hypA_hypA,
      W.herm_hypA_hypB]
    ring
  have h2 : herm σ (W.hypB 0) d = 0 := by
    rw [hd]
    simp only [herm_sub_right, herm_add_right, herm_smul_right, W.herm_hypB_hypB,
      W.herm_hypB_hypA hσ]
    ring
  obtain ⟨d0, d1⟩ := W.coord_eq_zero_of_perp h1 h2
  have : d = 0 := by
    funext i
    fin_cases i
    · exact d0
    · exact d1
  rw [hd, sub_eq_zero] at this
  exact this

end WittData

theorem T_two_eq_top (hσ : IsUnitaryInvolution σ) : T σ 2 = ⊤ := by
  obtain ⟨W⟩ := hσ.nonempty_wittData
  rw [eq_top_iff]
  intro A _
  refine mem_T_two_of_basis hσ W.herm_hypA_hypA W.herm_hypB_hypB W.herm_hypA_hypB
    (W.eq_hyp_expansion hσ.invol) ?_ A
  simp only [WittData.hypA_zero, WittData.hypA_one, WittData.hypB_zero, WittData.hypB_one]
  have h : (1 : K) * ((1 - W.ω)⁻¹ * (W.u * W.ω)) - (1 - W.ω)⁻¹ * W.u = -W.u := by
    field_simp [W.one_sub_ω_ne_zero]
    ring
  rw [h]
  exact neg_ne_zero.mpr W.u_ne_zero

end CFSG.ClassicalGroups.Unitary
