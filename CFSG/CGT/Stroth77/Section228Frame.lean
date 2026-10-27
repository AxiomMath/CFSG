module

public import CFSG.CGT.Stroth77.Sections34AssemblyAux
public import CFSG.CGT.Stroth77.Section43Fus
public import CFSG.CGT.Stroth77.Section42

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

open CFSG.CGT.Stroth77

theorem rho_c_gen (τ : StrothTypeIndex) :
    τ.action.φρ (Torus.c (k := τ.k)) = Torus.c (k := τ.k) := by
  cases τ
  all_goals
    dsimp only [StrothTypeIndex.action, Torus.c, Type100.action, Type101.action, Type110.action,
      Type111.action, Type120.action, Type121.action, Type130.action, Type131.action,
      Type200.action, Type201.action, Type210.action, Type211.action, Type220.action,
      Type221.action, Type230.action, Type231.action, Type300.action, Type310.action,
      Type320.action, Type330.action, Type321.action, Type331.action, Type120.actionPaper,
      Type121.actionPaper, Type130.actionPaper, Type131.actionPaper, Type220.actionPaper,
      Type221.actionPaper, Type230.actionPaper, Type231.actionPaper, Type320.actionPaper,
      Type330.actionPaper, SigmaFourAction.ofMatEq, SigmaFourAction.φρ]
    rw [matAct_gen_eq]
    simp [Type100.ρM, Type101.ρM, Type110.ρM, Type111.ρM, Type120.ρM, Type121.ρM, Type130.ρM,
      Type131.ρM, Type200.ρM, Type201.ρM, Type210.ρM, Type211.ρM, Type220.ρM, Type221.ρM,
      Type230.ρM, Type231.ρM, Type300.ρM, Type310.ρM, Type320.ρM, Type330.ρM, Type321.ρM,
      Type331.ρM, ofCols, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem one_le_m (h : F.IsD D dD) : 1 ≤ τ.m := by
  have htri : τ.m + 1 = τ.n ∨ τ.m + 2 = τ.n ∨ τ.m = τ.n := by
    cases τ <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
  have hk := h.five_le_k_sum
  rw [τ.k_eq] at hk
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hk
  omega

theorem c_pow_eq_w (h : F.IsD D dD) :
    (dD.c : G) ^ 2 ^ (τ.m - 1) = (F.dA.c : G) := by
  have hm : 1 ≤ τ.m := h.one_le_m
  set z : G := (dD.c : G) ^ 2 ^ (τ.m - 1) with hz
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hcord : orderOf (dD.c : G) = 2 ^ τ.m := by
    rw [Stroth42.orderOf_c_coe, show τ.k 0 = τ.m from rfl]
  have hz2 : z * z = 1 := by
    rw [hz, ← pow_add, show 2 ^ (τ.m - 1) + 2 ^ (τ.m - 1) = 2 ^ τ.m by
      rw [← two_mul, show 2 * 2 ^ (τ.m - 1) = 2 ^ ((τ.m - 1) + 1) by rw [pow_succ'],
        Nat.sub_add_cancel hm]]
    rw [← hcord, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rw [hz]
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) ?_
    rw [hcord]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hrhoc : τ.action.φρ (Torus.c (k := τ.k)) = Torus.c := rho_c_gen τ
  have hrhov : τ.action.φρ ((2 ^ (τ.m - 1) : ℕ) • Torus.c (k := τ.k)) =
      (2 ^ (τ.m - 1) : ℕ) • Torus.c := by
    rw [map_nsmul, hrhoc]
  have hz_eq : z = dD.ofTorus ((2 ^ (τ.m - 1) : ℕ) • Torus.c (k := τ.k)) := by
    rw [hz, show (dD.c : G) = dD.ofTorus (Torus.c (k := τ.k)) from rfl, ← dD.ofTorus_nsmul]
  have hzρ : dD.ρ⁻¹ * z * dD.ρ = z := by
    rw [hz_eq, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, hrhov]
  have hzΩ : z ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hzD hz2
  have hzA : z ∈ F.A := omegaIn_le 1 F.A (h.omegaIn_one_eq ▸ hzΩ)
  obtain ⟨γ, hγ⟩ := F.dA.exists_ofTorus hzA
  have hγ2 : γ + γ = 0 := by
    rw [hγ, ← F.dA.ofTorus_add] at hz2
    exact F.dA.ofTorus_eq_one_iff.mp hz2
  have hγ1 : γ ≠ 0 := by
    intro h0
    apply hz1
    rw [hγ, h0, F.dA.ofTorus_zero]
  have hγρ : (StrothTypeIndex.t100 1).action.φρ γ = γ := by
    have h1 : F.dA.ρ⁻¹ * z * F.dA.ρ = z := by
      rw [← h.ρ_eq]; exact hzρ
    rw [hγ] at h1
    have h2 := F.dA.conj_ofTorus F.dA.ρ_mem F.dA.ρ_conj γ
    rw [h2] at h1
    exact F.dA.ofTorus_inj h1
  have hγc := Stroth43Fus.t100_one_rho_fixed γ hγ2 hγ1 hγρ
  rw [hγ, hγc]
  rfl

theorem isConj_w_xy_sq_of_isConj_uv_xyuv (h : F.IsD D dD)
    (hu : IsConj dD.u (F.dA.toConfig.w * dD.u))
    (huv : IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv)) :
    IsConj F.dA.toConfig.w ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) := by
  obtain ⟨hfusE, huw, hwu, -, -, -⟩ := Stroth76.frame_fusion F
  have huv1 : F.dA.uv ≠ 1 := fun h1 =>
    F.uv_not_mem_centralizer_A (by rw [h1]; exact Subgroup.one_mem _)
  have huvsq : IsConj F.dA.uv ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) :=
    hfusE F.dA.uv (Subgroup.subset_closure (by simp)) huv1
  have hu' : IsConj F.dA.toConfig.u (F.dA.toConfig.w * F.dA.toConfig.u) := by
    simpa [h.u_eq] using hu
  exact huw.symm.trans (hu'.trans (hwu.trans (huv.symm.trans huvsq)))

theorem stroth_2_28_frame_of_inputs (h : F.IsD D dD)
    (hnotall : ∃ x : G, x ∈ omegaIn 1 D ∧ orderOf x = 2 ∧
      ∃ y : G, y ∈ omegaIn 1 D ∧ orderOf y = 2 ∧ ∀ g : G, y ≠ g * x * g⁻¹)
    (hu : ¬ ((∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨ (∃ m, τ = .t100 m) ∨
        (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n) →
      IsConj dD.u (F.dA.toConfig.w * dD.u))
    (huv : ¬ ((∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨ (∃ m, τ = .t100 m) ∨
        (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n) →
      IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv)) :
    (∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨ (∃ m, τ = .t100 m) ∨
      (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n := by
  by_contra hfive
  have hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hnotall
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, fun hc => by
      obtain ⟨g, hg⟩ := isConj_iff.mp hc
      exact hxy g hg.symm⟩
  exact F.not_isConj_w_xy_sq hnc
    (h.isConj_w_xy_sq_of_isConj_uv_xyuv (hu hfive) (huv hfive))

end StrothFrame.IsD

end CFSG.CGT.Stroth77
