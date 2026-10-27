module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.UnLinAlg
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFinal

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

open CFSG.LieType.Steinberg CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.SP

variable {k : Type*} [Field k]

theorem sl2_closure_eq_top :
    Subgroup.closure (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
      Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) = ⊤ :=
  CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := k)

theorem tau_rho_eq {G : Type*} [Group G] (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* G)
    (τ : G ≃* G) (ε : k ≃+* k) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (N : Matrix.SpecialLinearGroup (Fin 2) k) : τ (ρ N) = ρ (tauHat ε κ N) := by
  have key : (τ : G →* G).comp ρ = ρ.comp (tauHat ε κ) := by
    refine MonoidHom.eq_of_eqOn_dense sl2_closure_eq_top ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show τ (ρ (sl2Upper c)) = ρ (tauHat ε κ (sl2Upper c))
      rw [hu, tauHat_upper]
    · show τ (ρ (sl2Lower c)) = ρ (tauHat ε κ (sl2Lower c))
      rw [hl, tauHat_lower]
  exact congrArg (fun f : Matrix.SpecialLinearGroup (Fin 2) k →* G => f N) key

theorem theta_rho_fixed {G : Type*} [Group G] (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* G)
    (τ : G ≃* G) (ε : k ≃+* k) (κ : kˣ)
    (hτρ : ∀ N, τ (ρ N) = ρ (tauHat ε κ N)) (t : k) {N : Matrix.SpecialLinearGroup (Fin 2) k}
    (hN : tauHat ε κ (sl2Lower t * N * (sl2Lower t)⁻¹) = sl2Lower t * N * (sl2Lower t)⁻¹) :
    (τ.trans (MulAut.conj ((ρ (sl2Lower t))⁻¹ * τ (ρ (sl2Lower t))))) (ρ N) = ρ N := by
  rw [un_theta_apply]
  have e : ρ (sl2Lower t) * ρ N * (ρ (sl2Lower t))⁻¹ = ρ (sl2Lower t * N * (sl2Lower t)⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e, hτρ, hN]
  simp only [map_mul, map_inv]
  group

theorem diag_upper_conj (u : kˣ) (a : k) :
    unSL2Diag u * sl2Upper a * (unSL2Diag u)⁻¹ = sl2Upper ((u : k) ^ 2 * a) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  have hu : (u : k) ≠ 0 := u.ne_zero
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unSL2Diag, sl2U_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem sl2_eq_diag_mul_upper {X : Matrix.SpecialLinearGroup (Fin 2) k} {a β : k} (ha : a ≠ 0)
    (hX : (X : Matrix (Fin 2) (Fin 2) k) = !![a, β; 0, a⁻¹]) :
    X = unSL2Diag (Units.mk0 a ha) * sl2Upper (β * a⁻¹) := by
  apply Subtype.ext
  rw [hX]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unSL2Diag, sl2U_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem upper_mul_comm (a b : k) : sl2Upper a * sl2Upper b = sl2Upper b * sl2Upper a := by
  rw [← un_sl2Upper_add, ← un_sl2Upper_add, add_comm]

theorem sl2Upper_zero' : (sl2Upper (0 : k)) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2U_coe]

theorem torus_upper_fixed {G : Type*} [Group G] (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* G)
    (hρinj : Function.Injective ρ) (u : kˣ) (s a : k) (hu2 : (u : k) ^ 2 ≠ 1)
    (h : (ρ (unSL2Diag u) * ρ (sl2Upper s)) * ρ (sl2Upper a) *
      (ρ (unSL2Diag u) * ρ (sl2Upper s))⁻¹ = ρ (sl2Upper a)) : ρ (sl2Upper a) = 1 := by
  have h1 : sl2Upper s * sl2Upper a * (sl2Upper s)⁻¹ = sl2Upper a := by
    rw [upper_mul_comm s a, mul_inv_cancel_right]
  have e : (unSL2Diag u * sl2Upper s) * sl2Upper a * (unSL2Diag u * sl2Upper s)⁻¹ =
      sl2Upper ((u : k) ^ 2 * a) := by
    calc (unSL2Diag u * sl2Upper s) * sl2Upper a * (unSL2Diag u * sl2Upper s)⁻¹
        = unSL2Diag u * (sl2Upper s * sl2Upper a * (sl2Upper s)⁻¹) * (unSL2Diag u)⁻¹ := by
          group
      _ = _ := by rw [h1, diag_upper_conj]
  have h' : ρ ((unSL2Diag u * sl2Upper s) * sl2Upper a * (unSL2Diag u * sl2Upper s)⁻¹) =
      ρ (sl2Upper a) := by
    simpa only [map_mul, map_inv] using h
  rw [e] at h'
  have h'' : (u : k) ^ 2 * a = a := un_sl2Upper_injective (hρinj h')
  have ha : a = 0 := by
    have : ((u : k) ^ 2 - 1) * a = 0 := by linear_combination h''
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0) hu2
    · exact h0
  rw [ha, sl2Upper_zero', map_one]

theorem exists_neg_frob {q : ℕ} (hq : Odd q) (hq1 : 3 ≤ q) [Finite k] (hk : Nat.card k = q ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ q) : ∃ w : k, w ≠ 0 ∧ ε w = -w := by
  have hs : 0 < (q + 1) * (q ^ 2 + 1) := by positivity
  have hG : Nat.card kˣ = (q - 1) * ((q + 1) * (q ^ 2 + 1)) := by
    rw [Nat.card_units, hk]
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (m + 1) ^ 4 = m * (((m + 1) + 1) * ((m + 1) ^ 2 + 1)) + 1 := by ring
    omega
  have hm1 : ((-1 : kˣ)) ^ ((q + 1) * (q ^ 2 + 1)) = 1 := by
    apply Even.neg_one_pow
    obtain ⟨r, hr⟩ := hq
    exact ⟨(r + 1) * (q ^ 2 + 1), by subst hr; ring⟩
  have hcard := card_pow_eq_of_isCyclic (G := kˣ) (d := q - 1) (s := (q + 1) * (q ^ 2 + 1))
    (by omega) hs hG (g := -1) hm1
  have hpos : 0 < Nat.card {x : kˣ // x ^ (q - 1) = -1} := by
    rw [hcard]
    omega
  obtain ⟨⟨x, hx⟩⟩ := Finite.card_pos_iff.1 hpos
  refine ⟨x, x.ne_zero, ?_⟩
  have h1 : (x : k) ^ (q - 1) = -1 := by
    have := congrArg Units.val hx
    simpa using this
  rw [hε]
  calc (x : k) ^ q = (x : k) ^ (q - 1) * x := by
        rw [← pow_succ]
        congr 1
        omega
    _ = -x := by rw [h1]; ring

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
