module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Unit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNegCore

open Matrix Polynomial CFSG.LocalAnalysis.GLTheoremA.SFM12

variable {F : Type} [Field F] [CharP F 2]

theorem two_eq_zero' : (2 : F) = 0 := by
  have h : ((2 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 2 2).2 dvd_rfl
  simpa using h

theorem mulVec_mulVec_comm {A B : Matrix (Fin 6) (Fin 6) F} (h : Commute A B) (v : Fin 6 → F) :
    A *ᵥ (B *ᵥ v) = B *ᵥ (A *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.eq]

section Adjoint

theorem herm_adj_one {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm (Y *ᵥ a) (Y *ᵥ b) = herm a b) (hY7 : Y ^ 7 = 1) (a b : Fin 6 → F) :
    herm (Y *ᵥ a) b = herm a ((Y ^ 6) *ᵥ b) := by
  have hinv : Y * Y ^ 6 = 1 := by
    rw [← pow_succ']
    exact hY7
  have h : Y *ᵥ ((Y ^ 6) *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  calc herm (Y *ᵥ a) b = herm (Y *ᵥ a) (Y *ᵥ ((Y ^ 6) *ᵥ b)) := by rw [h]
    _ = herm a ((Y ^ 6) *ᵥ b) := hY _ _

theorem herm_adj_pow {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm (Y *ᵥ a) (Y *ᵥ b) = herm a b) (hY7 : Y ^ 7 = 1) (k : ℕ)
    (a b : Fin 6 → F) : herm ((Y ^ k) *ᵥ a) b = herm a (((Y ^ 6) ^ k) *ᵥ b) := by
  induction k generalizing a b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, herm_adj_one hY hY7, ih, pow_succ (Y ^ 6) k,
      ← Matrix.mulVec_mulVec]

theorem herm_adj_f {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm (Y *ᵥ a) (Y *ᵥ b) = herm a b) (hY7 : Y ^ 7 = 1) (u v : Fin 6 → F) :
    herm ((Y ^ 3 + Y + 1) *ᵥ u) v = herm u (((Y ^ 6) ^ 3 + Y ^ 6 + 1) *ᵥ v) := by
  have h3 := herm_adj_pow hY hY7 3 u v
  have h1 := herm_adj_pow hY hY7 1 u v
  rw [pow_one, pow_one] at h1
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, herm_add_left, herm_add_right, h3, h1]

end Adjoint

section Identities

theorem poly_two : (2 : F[X]) = 0 := by
  have h : (2 : F[X]) = Polynomial.C (2 : F) := (map_ofNat Polynomial.C 2).symm
  rw [h, two_eq_zero', map_zero]

theorem poly_I1 : (X ^ 3 + X + 1 : F[X]) * (X ^ 3 + X ^ 2 + 1) * (X + 1) = X ^ 7 - 1 := by
  linear_combination (X ^ 6 + X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + X + 1 : F[X]) * (poly_two (F := F))

theorem poly_I2 : ((X ^ 6) ^ 3 + X ^ 6 + 1 : F[X]) * (X ^ 3 * (X + 1)) =
    1 + X * (X ^ 3 + X + 1) + (X ^ 7 - 1) * ((X + 1) * (X ^ 14 + X ^ 7 + 1) + X ^ 3 + X ^ 2) := by
  linear_combination (X ^ 3 : F[X]) * (poly_two (F := F))

theorem poly_I3 : ((X ^ 6) ^ 3 + X ^ 6 + 1 : F[X]) =
    X ^ 4 * (X ^ 3 + X ^ 2 + 1) + (X ^ 7 - 1) * (X ^ 11 + X ^ 4 - 1) := by
  ring

section Mat

variable {Z : Matrix (Fin 6) (Fin 6) F}

theorem matI1 (hZ7 : Z ^ 7 = 1) : (Z ^ 3 + Z + 1) * (Z ^ 3 + Z ^ 2 + 1) * (Z + 1) = 0 := by
  have h := congrArg (Polynomial.aeval (R := F) Z) (poly_I1 (F := F))
  simp only [map_mul, map_add, map_sub, map_pow, map_one, Polynomial.aeval_X] at h
  rw [hZ7, sub_self] at h
  exact h

theorem matI2 (hZ7 : Z ^ 7 = 1) :
    ((Z ^ 6) ^ 3 + Z ^ 6 + 1) * (Z ^ 3 * (Z + 1)) = 1 + Z * (Z ^ 3 + Z + 1) := by
  have h := congrArg (Polynomial.aeval (R := F) Z) (poly_I2 (F := F))
  simp only [map_mul, map_add, map_sub, map_pow, map_one, Polynomial.aeval_X] at h
  rw [hZ7, sub_self, zero_mul, add_zero] at h
  exact h

theorem matI3 (hZ7 : Z ^ 7 = 1) : (Z ^ 6) ^ 3 + Z ^ 6 + 1 = Z ^ 4 * (Z ^ 3 + Z ^ 2 + 1) := by
  have h := congrArg (Polynomial.aeval (R := F) Z) (poly_I3 (F := F))
  simp only [map_mul, map_add, map_sub, map_pow, map_one, Polynomial.aeval_X] at h
  rw [hZ7, sub_self, zero_mul, add_zero] at h
  exact h

end Mat

end Identities

section Isotropy

theorem herm_iso_f {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm (Y *ᵥ a) (Y *ᵥ b) = herm a b) (hY7 : Y ^ 7 = 1)
    {u u' : Fin 6 → F} (hu : (Y ^ 3 + Y + 1) *ᵥ u = 0) (hu' : (Y ^ 3 + Y + 1) *ᵥ u' = 0) :
    herm u u' = 0 := by
  have hM := matI2 (Z := Y) hY7
  have hv : ((Y ^ 6) ^ 3 + Y ^ 6 + 1) *ᵥ ((Y ^ 3 * (Y + 1)) *ᵥ u') = u' := by
    rw [Matrix.mulVec_mulVec, hM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hu',
      Matrix.mulVec_zero, add_zero]
  calc herm u u' = herm u (((Y ^ 6) ^ 3 + Y ^ 6 + 1) *ᵥ ((Y ^ 3 * (Y + 1)) *ᵥ u')) := by rw [hv]
    _ = herm ((Y ^ 3 + Y + 1) *ᵥ u) ((Y ^ 3 * (Y + 1)) *ᵥ u') := (herm_adj_f hY hY7 _ _).symm
    _ = 0 := by rw [hu, herm_zero_left]

end Isotropy

section Roots

theorem root_free_f [Finite F] (hF : Nat.card F = 16) (x : F) : x ^ 3 + x + 1 ≠ 0 := by
  classical
  intro h
  have h16 : x ^ 16 = x := pow16_eq hF x
  have hI1 : (x ^ 3 + x + 1) * (x ^ 3 + x ^ 2 + 1) * (x + 1) = x ^ 7 - 1 := by
    linear_combination (x ^ 6 + x ^ 5 + 2 * x ^ 4 + 2 * x ^ 3 + x ^ 2 + x + 1) * (two_eq_zero' (F := F))
  have h7 : x ^ 7 = 1 := by
    have h0 : x ^ 7 - 1 = 0 := by rw [← hI1, h, zero_mul, zero_mul]
    linear_combination h0
  have h8 : x ^ 8 = x := by linear_combination x * h7
  have h2 : x ^ 2 = x := by linear_combination h16 - (x ^ 8 + x) * h8
  have h3 : x ^ 3 = x := by linear_combination (x + 1) * h2
  have h1 : (1 : F) = 0 := by linear_combination h - h3 - x * (two_eq_zero' (F := F))
  exact one_ne_zero h1

section Indep

variable (Z : Matrix (Fin 6) (Fin 6) F)

theorem indep3 (hf3 : ∀ x : F, x ^ 3 + x + 1 ≠ 0) {u : Fin 6 → F} (hu0 : u ≠ 0)
    (hu : (Z ^ 3 + Z + 1) *ᵥ u = 0) : LinearIndependent F ![u, Z *ᵥ u, Z *ᵥ (Z *ᵥ u)] := by
  have hpow3 : (Z ^ 3) *ᵥ u = Z *ᵥ (Z *ᵥ (Z *ᵥ u)) := by
    simp only [pow_succ', pow_one, pow_zero, mul_one, Matrix.mulVec_mulVec]
  have hexp : (Z ^ 3 + Z + 1) *ᵥ u = Z *ᵥ (Z *ᵥ (Z *ᵥ u)) + Z *ᵥ u + u := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hpow3]
  have R0 : Z *ᵥ (Z *ᵥ (Z *ᵥ u)) + Z *ᵥ u + u = 0 := by
    rw [← hexp]
    exact hu
  have line : ∀ l m : F, l • u + m • (Z *ᵥ u) = 0 → l = 0 ∧ m = 0 := by
    intro l m h
    by_cases hm : m = 0
    · subst hm
      rw [zero_smul, add_zero] at h
      exact ⟨(smul_eq_zero.1 h).resolve_right hu0, rfl⟩
    · exfalso
      have h' : m • (Z *ᵥ u) = (-l) • u := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_right h
      obtain ⟨ν, hν⟩ : ∃ ν : F, ν = m⁻¹ * (-l) := ⟨_, rfl⟩
      have hZu : Z *ᵥ u = ν • u := by
        calc Z *ᵥ u = (m⁻¹ * m) • (Z *ᵥ u) := by rw [inv_mul_cancel₀ hm, one_smul]
          _ = m⁻¹ • (m • (Z *ᵥ u)) := by rw [mul_smul]
          _ = m⁻¹ • ((-l) • u) := by rw [h']
          _ = ν • u := by rw [smul_smul, hν]
      have hZ2 : Z *ᵥ (Z *ᵥ u) = (ν ^ 2) • u := by
        rw [hZu, Matrix.mulVec_smul, hZu, smul_smul, pow_two]
      have hZ3 : Z *ᵥ (Z *ᵥ (Z *ᵥ u)) = (ν ^ 3) • u := by
        rw [hZ2, Matrix.mulVec_smul, hZu, smul_smul, ← pow_succ]
      rw [hZ3, hZu] at R0
      have hR : (ν ^ 3 + ν + 1) • u = 0 := by
        rw [add_smul, add_smul, one_smul]
        exact R0
      have hν0 : ν ^ 3 + ν + 1 = 0 := (smul_eq_zero.1 hR).resolve_right hu0
      exact hf3 ν hν0
  have key : ∀ l m c : F, l • u + m • (Z *ᵥ u) + c • (Z *ᵥ (Z *ᵥ u)) = 0 → c = 0 := by
    intro l m c h
    by_contra hc
    obtain ⟨α, hα⟩ : ∃ α : F, α = -(c⁻¹ * l) := ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ : ∃ β : F, β = -(c⁻¹ * m) := ⟨_, rfl⟩
    have hw2 : Z *ᵥ (Z *ᵥ u) = α • u + β • (Z *ᵥ u) := by
      have h1 : c • (Z *ᵥ (Z *ᵥ u)) = -(l • u + m • (Z *ᵥ u)) := eq_neg_of_add_eq_zero_right h
      calc Z *ᵥ (Z *ᵥ u) = c⁻¹ • (c • (Z *ᵥ (Z *ᵥ u))) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = c⁻¹ • (-(l • u + m • (Z *ᵥ u))) := by rw [h1]
        _ = α • u + β • (Z *ᵥ u) := by rw [hα, hβ]; module
    have hw3 : Z *ᵥ (Z *ᵥ (Z *ᵥ u)) = α • (Z *ᵥ u) + β • (α • u + β • (Z *ᵥ u)) := by
      rw [hw2, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hw2]
    have hrel : (α * β + 1) • u + (α + β ^ 2 + 1) • (Z *ᵥ u) = 0 := by
      calc (α * β + 1) • u + (α + β ^ 2 + 1) • (Z *ᵥ u)
          = (α • (Z *ᵥ u) + β • (α • u + β • (Z *ᵥ u))) + Z *ᵥ u + u := by module
        _ = Z *ᵥ (Z *ᵥ (Z *ᵥ u)) + Z *ᵥ u + u := by rw [hw3]
        _ = 0 := R0
    obtain ⟨h1, h2⟩ := line _ _ hrel
    exact hf3 β (by linear_combination β * h2 - h1 + (two_eq_zero' (F := F)))
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have hc2 : g 2 = 0 := key (g 0) (g 1) (g 2) hg
  rw [hc2, zero_smul, add_zero] at hg
  have hl := line (g 0) (g 1) hg
  intro i
  fin_cases i
  · exact hl.1
  · exact hl.2
  · exact hc2

end Indep

end Roots

section Dimension

variable {F : Type} [Field F] [CharP F 2]

@[expose] def phiHerm (w : Fin 3 → Fin 6 → F) : (Fin 6 → F) →ₗ[F] (Fin 3 → F) where
  toFun v i := herm (w i) v
  map_add' v v' := by
    funext i
    exact herm_add_right _ _ _
  map_smul' c v := by
    funext i
    simp [herm_smul_right]

theorem phiHerm_apply (w : Fin 3 → Fin 6 → F) (v : Fin 6 → F) (i : Fin 3) :
    phiHerm w v i = herm (w i) v := rfl

theorem eq_zero_of_herm_forall {x : Fin 6 → F} (h : ∀ v : Fin 6 → F, herm x v = 0) : x = 0 := by
  funext j
  have h1 := h (fun k => if k = j then 1 else 0)
  have h2 : x j ^ 4 = 0 := by
    simpa [herm, mul_ite] using h1
  exact pow_eq_zero_iff (n := 4) (by norm_num) |>.1 h2

theorem phiHerm_surjective {w : Fin 3 → Fin 6 → F} (hF16 : ∀ x : F, x ^ 16 = x)
    (hw : LinearIndependent F w) : Function.Surjective (phiHerm w) := by
  by_contra hns
  have hlt : LinearMap.range (phiHerm w) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hns ?_
    exact LinearMap.range_eq_top.1 htop
  obtain ⟨ψ, hψ0, hψ⟩ := (LinearMap.range (phiHerm w)).exists_le_ker_of_lt_top hlt
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → F, ∀ i, c i = ψ (fun j => if i = j then 1 else 0) := ⟨_, fun i => rfl⟩
  have hψx : ∀ x : Fin 3 → F, ψ x = ∑ i, x i * c i := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, ← hc i]
  have hval : ∀ v : Fin 6 → F, ∑ i, herm (w i) v * c i = 0 := by
    intro v
    have h := hψ (LinearMap.mem_range_self (phiHerm w) v)
    rw [LinearMap.mem_ker, hψx] at h
    exact h
  have hc0 : ∀ i, c i = 0 := by
    have hsum : ∑ i, (c i ^ 4) • w i = 0 := by
      refine eq_zero_of_herm_forall fun v => ?_
      rw [herm_sum_left]
      have hterm : ∀ i, herm ((c i ^ 4) • w i) v = herm (w i) v * c i := by
        intro i
        rw [herm_smul_left, ← pow_mul, show (4 : ℕ) * 4 = 16 from rfl, hF16 (c i), mul_comm]
      calc ∑ i, herm ((c i ^ 4) • w i) v = ∑ i, herm (w i) v * c i :=
            Finset.sum_congr rfl fun i _ => hterm i
        _ = 0 := hval v
    intro i
    have h1 : c i ^ 4 = 0 := Fintype.linearIndependent_iff.1 hw (fun i => c i ^ 4) hsum i
    calc c i = c i ^ 16 := (hF16 (c i)).symm
      _ = (c i ^ 4) ^ 4 := by ring
      _ = 0 := by rw [h1]; ring
  apply hψ0
  refine LinearMap.ext fun x => ?_
  rw [hψx]
  simp [hc0]

theorem finrank_ker_phiHerm {w : Fin 3 → Fin 6 → F} (hF16 : ∀ x : F, x ^ 16 = x)
    (hw : LinearIndependent F w) : Module.finrank F (LinearMap.ker (phiHerm w)) = 3 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (phiHerm w)
  rw [LinearMap.range_eq_top.2 (phiHerm_surjective hF16 hw), finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h1
  omega

theorem ker_phiHerm_eq_span {w : Fin 3 → Fin 6 → F} (hF16 : ∀ x : F, x ^ 16 = x)
    (hw : LinearIndependent F w) (hiso : ∀ i j, herm (w i) (w j) = 0) :
    LinearMap.ker (phiHerm w) = Submodule.span F (Set.range w) := by
  have hle : Submodule.span F (Set.range w) ≤ LinearMap.ker (phiHerm w) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext j
    simp [phiHerm_apply, hiso]
  have hfin : Module.finrank F (Submodule.span F (Set.range w)) = 3 := by
    rw [finrank_span_eq_card hw]
    simp
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hfin, finrank_ker_phiHerm hF16 hw])).symm

end Dimension

section Main

variable {F : Type} [Field F] [CharP F 2]

theorem fixed_no_kernel (hF16 : ∀ x : F, x ^ 16 = x) (hf3 : ∀ x : F, x ^ 3 + x + 1 ≠ 0)
    {Z P : Matrix (Fin 6) (Fin 6) F}
    (hZ : ∀ a b : Fin 6 → F, herm (Z *ᵥ a) (Z *ᵥ b) = herm a b) (hZ7 : Z ^ 7 = 1)
    (hPZ : Commute P Z) (hPs : ∀ a b : Fin 6 → F, herm (P *ᵥ a) b = herm a (P *ᵥ b))
    {t : Fin 6 → F} (ht0 : t ≠ 0) (hPt : P *ᵥ t = 0)
    {u : Fin 6 → F} (hPu : P *ᵥ u = u) (hu : (Z ^ 3 + Z + 1) *ᵥ u = 0) : u = 0 := by
  by_contra hu0
  set w : Fin 3 → Fin 6 → F := ![u, Z *ᵥ u, Z *ᵥ (Z *ᵥ u)] with hw_def
  have hw : LinearIndependent F w := indep3 Z hf3 hu0 hu
  have hcZ : Commute Z (Z ^ 3 + Z + 1) :=
    ((Commute.refl Z).pow_right 3 |>.add_right (Commute.refl Z)).add_right (Commute.one_right Z)
  have hker : ∀ i : Fin 3, (Z ^ 3 + Z + 1) *ᵥ (w i) = 0 := by
    intro i
    fin_cases i
    · exact hu
    · show (Z ^ 3 + Z + 1) *ᵥ (Z *ᵥ u) = 0
      rw [← mulVec_mulVec_comm hcZ, hu, Matrix.mulVec_zero]
    · show (Z ^ 3 + Z + 1) *ᵥ (Z *ᵥ (Z *ᵥ u)) = 0
      rw [← mulVec_mulVec_comm hcZ, ← mulVec_mulVec_comm hcZ, hu, Matrix.mulVec_zero,
        Matrix.mulVec_zero]
  have hfix : ∀ i : Fin 3, P *ᵥ (w i) = w i := by
    intro i
    fin_cases i
    · exact hPu
    · show P *ᵥ (Z *ᵥ u) = Z *ᵥ u
      rw [mulVec_mulVec_comm hPZ, hPu]
    · show P *ᵥ (Z *ᵥ (Z *ᵥ u)) = Z *ᵥ (Z *ᵥ u)
      rw [mulVec_mulVec_comm hPZ, mulVec_mulVec_comm hPZ, hPu]
  have hiso : ∀ i j, herm (w i) (w j) = 0 := fun i j => herm_iso_f hZ hZ7 (hker i) (hker j)
  have hwt : ∀ i, herm (w i) t = 0 := by
    intro i
    calc herm (w i) t = herm (P *ᵥ w i) t := by rw [hfix i]
      _ = herm (w i) (P *ᵥ t) := hPs _ _
      _ = 0 := by rw [hPt, herm_zero_right]
  have ht_mem : t ∈ LinearMap.ker (phiHerm w) := by
    rw [LinearMap.mem_ker]
    funext i
    rw [phiHerm_apply, hwt i]
    rfl
  rw [ker_phiHerm_eq_span hF16 hw hiso] at ht_mem
  have hsub : Submodule.span F (Set.range w) ≤ LinearMap.ker (Matrix.mulVecLin P - LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    simp [hfix i]
  have hPt' : P *ᵥ t = t := by
    have h := hsub ht_mem
    rw [LinearMap.mem_ker] at h
    simpa [sub_eq_zero] using h
  exact ht0 (hPt'.symm.trans hPt)

end Main

end CFSG.LocalAnalysis.GLTheoremA.Y10GNegCore
