module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitEichler

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {p f : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  (h : UnitaryFieldData p f K) (G : Matrix ι ι K)

section Tau

variable (σ : K ≃+* K) (A : Matrix ι ι K)

@[expose] def tau (w : ι → K) : ι → K := A *ᵥ (fun i => σ (w i))

theorem tau_add (x y : ι → K) : tau σ A (x + y) = tau σ A x + tau σ A y := by
  unfold tau
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem tau_smul (c : K) (x : ι → K) : tau σ A (c • x) = σ c • tau σ A x := by
  simp only [tau]
  have : (fun i => σ ((c • x) i)) = σ c • (fun i => σ (x i)) := by
    funext i; simp
  rw [this, Matrix.mulVec_smul]

theorem tau_sub (x y : ι → K) : tau σ A (x - y) = tau σ A x - tau σ A y := by
  unfold tau
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simp

theorem tau_zero : tau σ A (0 : ι → K) = 0 := by
  unfold tau
  simp
  exact Matrix.mulVec_zero A

theorem hf_map (hσb : ∀ c, σ (h.bar c) = h.bar (σ c)) (hGσ : G.map σ = G) (x y : ι → K) :
    hf h G (fun i => σ (x i)) (fun i => σ (y i)) = σ (hf h G x y) := by
  have hG' : ∀ a b, σ (G a b) = G a b := fun a b => by
    have := congrFun (congrFun hGσ a) b
    simpa using this
  simp only [hf, gramForm_apply, dotProduct, Matrix.mulVec, map_sum, map_mul, hσb, hG']

theorem tau_hf (hσb : ∀ c, σ (h.bar c) = h.bar (σ c)) (hGσ : G.map σ = G)
    (hA : (A.map h.bar)ᵀ * G * A = G) (x y : ι → K) :
    hf h G (tau σ A x) (tau σ A y) = σ (hf h G x y) := by
  have hiso := (gramForm_isometry_iff h G A).2 hA
  unfold tau
  have h1 : hf h G (A *ᵥ (fun i => σ (x i))) (A *ᵥ fun i => σ (y i)) =
      hf h G (fun i => σ (x i)) (fun i => σ (y i)) := hiso _ _
  rw [h1, hf_map h G σ hσb hGσ]

theorem mulVec_map_sigma (M : Matrix ι ι K) (w : ι → K) :
    (M.map σ) *ᵥ (fun i => σ (w i)) = fun i => σ ((M *ᵥ w) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem tau_tau (hσ2 : ∀ c, σ (σ c) = c) (B : Matrix ι ι K) (w : ι → K) :
    tau σ A (tau σ B w) = (A * B.map σ) *ᵥ w := by
  unfold tau
  have e : (fun i => σ ((B *ᵥ fun i => σ (w i)) i)) = (B.map σ) *ᵥ w := by
    rw [← mulVec_map_sigma σ B (fun i => σ (w i))]
    have : (fun i => σ (σ (w i))) = w := funext fun i => hσ2 _
    rw [this]
  rw [e, Matrix.mulVec_mulVec]

end Tau

section Conj

variable (σ : K ≃+* K) (hσb : ∀ c, σ (h.bar c) = h.bar (σ c)) (hσ2 : ∀ c, σ (σ c) = c)
  (hGσ : G.map σ = G) (A : GL ι K) (hA : (((A : Matrix ι ι K)).map h.bar)ᵀ * G * A = G)
  (hG : (G.map h.bar)ᵀ = G)

include hσb hσ2 hGσ hA

theorem conj_eM (v u : ι → K) (c : K) :
    (A : Matrix ι ι K) * (eM h G v u c).map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K) =
      eM h G (tau σ A v) (tau σ A u) (σ c) := by
  refine Matrix.ext_iff_mulVec.2 fun w' => ?_
  set w : ι → K := fun i => σ ((((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w') i) with hw
  have hAA : ((A : Matrix ι ι K)) *ᵥ (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w') = w' := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hτw : tau σ (A : Matrix ι ι K) w = w' := by
    unfold tau
    have : (fun i => σ (w i)) = ((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w' := by
      funext i; simp [hw, hσ2]
    rw [this, hAA]
  have hσw : (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w') = fun i => σ (w i) := by
    funext i; simp [hw, hσ2]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hσw, mulVec_map_sigma, eM_mulVec,
    ← hτw, eM_mulVec]
  have hA' : (((A : Matrix ι ι K)).map h.bar)ᵀ * G * (A : Matrix ι ι K) = G := hA
  have key : ∀ x y : ι → K, hf h G (tau σ (A : Matrix ι ι K) x) (tau σ (A : Matrix ι ι K) y) =
      σ (hf h G x y) := fun x y => tau_hf h G σ _ hσb hGσ hA' x y
  show tau σ (A : Matrix ι ι K) (w + hf h G v w • u - hf h G u w • v + (c * hf h G v w) • v) = _
  rw [tau_add, tau_sub, tau_add, tau_smul, tau_smul, tau_smul, map_mul, key, key]

end Conj

section Inversion

variable (hG : (G.map h.bar)ᵀ = G)

theorem eM_eigen_eq (v u : ι → K) (lam mu c' c'' : K) (hl : h.bar lam * mu = -1)
    (hc : c' * (lam * h.bar lam) = c'') :
    eM h G (lam • v) (mu • u) c' = eM h G v (-u) c'' := by
  have hl' : h.bar mu * lam = -1 := by
    have := congrArg h.bar hl
    rw [map_mul, UnitaryFieldData.bar_bar, map_neg, map_one] at this
    linear_combination this
  refine Matrix.ext_iff_mulVec.2 fun w => ?_
  rw [eM_mulVec, eM_mulVec]
  simp only [hf_smul_left, hf_smul_right, hf_neg_left, hf_neg_right, smul_neg, neg_smul]
  have e1 : (h.bar lam * hf h G v w) • mu • u = (-hf h G v w) • u := by
    rw [smul_smul]; congr 1; linear_combination (hf h G v w) * hl
  have e2 : (h.bar mu * hf h G u w) • lam • v = (-hf h G u w) • v := by
    rw [smul_smul]; congr 1; linear_combination (hf h G u w) * hl'
  have e3 : (c' * (h.bar lam * hf h G v w)) • lam • v = (c'' * hf h G v w) • v := by
    rw [smul_smul]; congr 1; linear_combination (hf h G v w) * hc
  rw [e1, e2, e3]
  module

theorem Tsu_inv_eq {v u : ι → K} {c : K} (hq : IsQ h G v u c) :
    (Tsu h G hG hq)⁻¹ = Tsu h G hG (hq.neg h G hG) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Tsu_mul, ← Tsu_zero h G hG hq.1]
  refine Tsu_congr h G hG _ _ (add_neg_cancel u) ?_
  rw [hf_neg_right]
  linear_combination hq.2.2

end Inversion


section PsiInv

variable (σ : K ≃+* K) (hσb : ∀ c, σ (h.bar c) = h.bar (σ c)) (hσ2 : ∀ c, σ (σ c) = c)
  (hGσ : G.map σ = G) (A : GL ι K) (hA : (((A : Matrix ι ι K)).map h.bar)ᵀ * G * A = G)
  (hG : (G.map h.bar)ᵀ = G)

include hG in
theorem bar_cc (u : ι → K) : h.bar (cc h G u) = cc h G u := by
  rw [cc, map_neg, map_mul, hf_self_bar h G hG, map_inv₀, map_ofNat]

include hσb hσ2 hGσ hA

theorem psi_inv_of_eigen {N : Subgroup ↥(gramSU h G)} [N.Normal]
    (ψ : MulAut (↥(gramSU h G) ⧸ N))
    (hψ : ∀ g g' : ↥(gramSU h G), smat h G g' =
      (A : Matrix ι ι K) * (smat h G g).map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K) →
      ψ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hσfix : ∀ c, h.bar c = c → σ c = c) (h2 : (2 : K) ≠ 0) {v u : ι → K}
    (hv : hf h G v v = 0) (hu : hf h G v u = 0) (lam mu : K)
    (hτv : tau σ (A : Matrix ι ι K) v = lam • v) (hτu : tau σ (A : Matrix ι ι K) u = mu • u)
    (hl : h.bar lam * mu = -1) (hc : lam * h.bar lam = 1 ∨ hf h G u u = 0) :
    ψ (QuotientGroup.mk (Tcan h G hG h2 hv hu)) = (QuotientGroup.mk (Tcan h G hG h2 hv hu))⁻¹ := by
  have hq := IsQ.can h G hG h2 hv hu
  have hbc := bar_cc h G hG u
  have hσc : σ (cc h G u) = cc h G u := hσfix _ hbc
  have hinv : (Tcan h G hG h2 hv hu)⁻¹ = Tsu h G hG (hq.neg h G hG) := Tsu_inv_eq h G hG hq
  rw [← QuotientGroup.mk_inv, hinv]
  refine hψ _ _ ?_
  have e1 : smat h G (Tcan h G hG h2 hv hu) = eM h G v u (cc h G u) := rfl
  rw [smat_Tsu, e1]
  rw [conj_eM h G σ hσb hσ2 hGσ A hA, hτv, hτu, hσc,
    eM_eigen_eq h G v u lam mu (cc h G u) (h.bar (cc h G u)) hl, hbc]
  rcases hc with hc | hc
  · rw [hc, mul_one, hbc]
  · have h0 : cc h G u = 0 := by rw [cc, hc]; simp
    rw [h0]; simp

end PsiInv

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
