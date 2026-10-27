module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HU7Herm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HU7

open Matrix CFSG.LocalAnalysis.GLTheoremA.Y10GNegCore

variable {F : Type} [Field F] [CharP F 2]

@[expose] def phiHerm2 (w : Fin 3 → Fin 6 → F) : (Fin 6 → F) →ₗ[F] (Fin 3 → F) where
  toFun v i := herm2 (w i) v
  map_add' v v' := by
    funext i
    exact herm2_add_right _ _ _
  map_smul' c v := by
    funext i
    simp [herm2_smul_right]

theorem phiHerm2_apply (w : Fin 3 → Fin 6 → F) (v : Fin 6 → F) (i : Fin 3) :
    phiHerm2 w v i = herm2 (w i) v := rfl

theorem eq_zero_of_herm2_forall {x : Fin 6 → F} (h : ∀ v : Fin 6 → F, herm2 x v = 0) : x = 0 := by
  funext j
  have h1 := h (fun k => if k = j then 1 else 0)
  have h2 : x j ^ 2 = 0 := by
    simpa [herm2, mul_ite] using h1
  exact (pow_eq_zero_iff two_ne_zero).1 h2

theorem phiHerm2_surjective {w : Fin 3 → Fin 6 → F} (hF4 : ∀ x : F, x ^ 4 = x)
    (hw : LinearIndependent F w) : Function.Surjective (phiHerm2 w) := by
  by_contra hns
  have hlt : LinearMap.range (phiHerm2 w) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hns ?_
    exact LinearMap.range_eq_top.1 htop
  obtain ⟨ψ, hψ0, hψ⟩ := (LinearMap.range (phiHerm2 w)).exists_le_ker_of_lt_top hlt
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → F, ∀ i, c i = ψ (fun j => if i = j then 1 else 0) :=
    ⟨_, fun i => rfl⟩
  have hψx : ∀ x : Fin 3 → F, ψ x = ∑ i, x i * c i := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, ← hc i]
  have hval : ∀ v : Fin 6 → F, ∑ i, herm2 (w i) v * c i = 0 := by
    intro v
    have h := hψ (LinearMap.mem_range_self (phiHerm2 w) v)
    rw [LinearMap.mem_ker, hψx] at h
    exact h
  have hc0 : ∀ i, c i = 0 := by
    have hsum : ∑ i, (c i ^ 2) • w i = 0 := by
      refine eq_zero_of_herm2_forall fun v => ?_
      rw [herm2_sum_left]
      have hterm : ∀ i, herm2 ((c i ^ 2) • w i) v = herm2 (w i) v * c i := by
        intro i
        rw [herm2_smul_left, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, hF4 (c i), mul_comm]
      calc ∑ i, herm2 ((c i ^ 2) • w i) v = ∑ i, herm2 (w i) v * c i :=
            Finset.sum_congr rfl fun i _ => hterm i
        _ = 0 := hval v
    intro i
    have h1 : c i ^ 2 = 0 := Fintype.linearIndependent_iff.1 hw (fun i => c i ^ 2) hsum i
    calc c i = c i ^ 4 := (hF4 (c i)).symm
      _ = (c i ^ 2) ^ 2 := by ring
      _ = 0 := by rw [h1]; ring
  apply hψ0
  refine LinearMap.ext fun x => ?_
  rw [hψx]
  simp [hc0]

theorem finrank_ker_phiHerm2 {w : Fin 3 → Fin 6 → F} (hF4 : ∀ x : F, x ^ 4 = x)
    (hw : LinearIndependent F w) : Module.finrank F (LinearMap.ker (phiHerm2 w)) = 3 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (phiHerm2 w)
  rw [LinearMap.range_eq_top.2 (phiHerm2_surjective hF4 hw), finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h1
  omega

theorem ker_phiHerm2_eq_span {w : Fin 3 → Fin 6 → F} (hF4 : ∀ x : F, x ^ 4 = x)
    (hw : LinearIndependent F w) (hiso : ∀ i j, herm2 (w i) (w j) = 0) :
    LinearMap.ker (phiHerm2 w) = Submodule.span F (Set.range w) := by
  have hle : Submodule.span F (Set.range w) ≤ LinearMap.ker (phiHerm2 w) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext j
    simp [phiHerm2_apply, hiso]
  have hfin : Module.finrank F (Submodule.span F (Set.range w)) = 3 := by
    rw [finrank_span_eq_card hw]
    simp
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hfin, finrank_ker_phiHerm2 hF4 hw])).symm

theorem fixed_no_kernel2 (hF4 : ∀ x : F, x ^ 4 = x)
    {Z P : Matrix (Fin 6) (Fin 6) F}
    (hZ : ∀ a b : Fin 6 → F, herm2 (Z *ᵥ a) (Z *ᵥ b) = herm2 a b) (hZ7 : Z ^ 7 = 1)
    (hPZ : Commute P Z) (hPs : ∀ a b : Fin 6 → F, herm2 (P *ᵥ a) b = herm2 a (P *ᵥ b))
    {t : Fin 6 → F} (ht0 : t ≠ 0) (hPt : P *ᵥ t = 0)
    {u : Fin 6 → F} (hPu : P *ᵥ u = u) (hu : (Z ^ 3 + Z + 1) *ᵥ u = 0) : u = 0 := by
  by_contra hu0
  set w : Fin 3 → Fin 6 → F := ![u, Z *ᵥ u, Z *ᵥ (Z *ᵥ u)] with hw_def
  have hw : LinearIndependent F w := indep3 Z (root_free_two hF4) hu0 hu
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
  have hiso : ∀ i j, herm2 (w i) (w j) = 0 := fun i j => herm2_iso_f hZ hZ7 (hker i) (hker j)
  have hwt : ∀ i, herm2 (w i) t = 0 := by
    intro i
    calc herm2 (w i) t = herm2 (P *ᵥ w i) t := by rw [hfix i]
      _ = herm2 (w i) (P *ᵥ t) := hPs _ _
      _ = 0 := by rw [hPt, herm2_zero_right]
  have ht_mem : t ∈ LinearMap.ker (phiHerm2 w) := by
    rw [LinearMap.mem_ker]
    funext i
    rw [phiHerm2_apply, hwt i]
    rfl
  rw [ker_phiHerm2_eq_span hF4 hw hiso] at ht_mem
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

theorem isometry_pow2 {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm2 (Y *ᵥ a) (Y *ᵥ b) = herm2 a b) (k : ℕ) (a b : Fin 6 → F) :
    herm2 ((Y ^ k) *ᵥ a) ((Y ^ k) *ᵥ b) = herm2 a b := by
  induction k generalizing a b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hY, ih]

theorem key_lemma2 {Y P : Matrix (Fin 6) (Fin 6) F} (hF4 : ∀ x : F, x ^ 4 = x)
    (hY : ∀ a b : Fin 6 → F, herm2 (Y *ᵥ a) (Y *ᵥ b) = herm2 a b) (hY7 : Y ^ 7 = 1)
    (hYP : Commute Y P) (hPs : ∀ a b : Fin 6 → F, herm2 (P *ᵥ a) b = herm2 a (P *ᵥ b))
    (hP2 : ∀ v : Fin 6 → F, P *ᵥ (P *ᵥ v) = P *ᵥ v)
    {t : Fin 6 → F} (ht0 : t ≠ 0) (hPt : P *ᵥ t = 0) (v : Fin 6 → F) :
    Y *ᵥ (P *ᵥ v) = P *ᵥ v := by
  set x : Fin 6 → F := P *ᵥ v
  have hx : P *ᵥ x = x := hP2 v
  have hPY : ∀ w : Fin 6 → F, P *ᵥ (Y *ᵥ w) = Y *ᵥ (P *ᵥ w) := fun w => mulVec_mulVec_comm hYP.symm w
  set z : Fin 6 → F := (Y + 1) *ᵥ x with hzdef
  have hPz : P *ᵥ z = z := by
    rw [hzdef, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, hPY, hx]
  have hcomm_q : Commute P (Y ^ 3 + Y ^ 2 + 1) :=
    ((hYP.symm.pow_right 3).add_right (hYP.symm.pow_right 2)).add_right (Commute.one_right P)
  have hPq : ∀ w : Fin 6 → F, P *ᵥ ((Y ^ 3 + Y ^ 2 + 1) *ᵥ w) = (Y ^ 3 + Y ^ 2 + 1) *ᵥ (P *ᵥ w) :=
    fun w => mulVec_mulVec_comm hcomm_q w
  set z' : Fin 6 → F := (Y ^ 3 + Y ^ 2 + 1) *ᵥ z with hz'def
  have hPz' : P *ᵥ z' = z' := by
    rw [hz'def, hPq, hPz]
  have hfz' : (Y ^ 3 + Y + 1) *ᵥ z' = 0 := by
    rw [hz'def, hzdef, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, matI1 hY7, Matrix.zero_mulVec]
  have hz'0 : z' = 0 := fixed_no_kernel2 hF4 hY hY7 hYP.symm hPs ht0 hPt hPz' hfz'
  have hfz6 : ((Y ^ 6) ^ 3 + Y ^ 6 + 1) *ᵥ z = 0 := by
    rw [matI3 hY7, ← Matrix.mulVec_mulVec, ← hz'def, hz'0, Matrix.mulVec_zero]
  have hZ7 : (Y ^ 6) ^ 7 = 1 := by
    rw [← pow_mul, show 6 * 7 = 7 * 6 by norm_num, pow_mul, hY7, one_pow]
  have hz0 : z = 0 :=
    fixed_no_kernel2 hF4 (isometry_pow2 hY 6) hZ7 (hYP.symm.pow_right 6) hPs ht0 hPt hPz hfz6
  rw [hzdef, Matrix.add_mulVec, Matrix.one_mulVec] at hz0
  have hxx : x + x = 0 := by
    rw [← two_smul F x, two_eq_zero' (F := F), zero_smul]
  calc Y *ᵥ x = Y *ᵥ x + (x + x) := by rw [hxx, add_zero]
    _ = (Y *ᵥ x + x) + x := by abel
    _ = x := by rw [hz0, zero_add]

end CFSG.LocalAnalysis.GLTheoremA.HU7

end
