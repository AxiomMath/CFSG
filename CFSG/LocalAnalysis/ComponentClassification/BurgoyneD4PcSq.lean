module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Pc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Fix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4SignGeom
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOAntiComp

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points pointMk pointMk_submodule
  exists_eq_pointMk)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self reflGL rotGL
  mul_conj_mul_inv)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem supp_of_sign_line {d : ℕ} (h2 : (2 : K) ≠ 0) {M : Finset (Fin d)} {v : Fin d → K}
    (h : signMat K M *ᵥ v ∈ Submodule.span K {v}) :
    (∀ i ∈ M, v i = 0) ∨ (∀ i ∉ M, v i = 0) := by
  have hW : ∀ u ∈ Submodule.span K {v}, signMat K M *ᵥ u ∈ Submodule.span K {v} := by
    intro u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [mulVec_smul]
    exact Submodule.smul_mem _ a h
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1
    (restr_mem h2 hW (Submodule.mem_span_singleton_self v))
  by_cases hα0 : α = 0
  · left
    intro i hi
    have := congrFun hα i
    simp only [hα0, zero_smul, Pi.zero_apply, restr, hi, ite_true] at this
    exact this.symm
  · right
    intro i hi
    have := congrFun hα i
    simp only [Pi.smul_apply, smul_eq_mul, restr, hi, ite_false] at this
    exact (mul_eq_zero.1 this).resolve_left hα0

abbrev cyc₁ : Equiv.Perm (Fin 4) := (⁅Equiv.swap (0 : Fin 4) 1, Equiv.swap (1 : Fin 4) 2⁆)⁻¹

abbrev cyc₂ : Equiv.Perm (Fin 4) := (⁅Equiv.swap (1 : Fin 4) 2, Equiv.swap (2 : Fin 4) 3⁆)⁻¹

theorem cyc_no_common_fixed : ∀ i : Fin 4, cyc₁ i = i → cyc₂ i = i → False := by decide

theorem blocks_eq_of_chars : ∀ i k : Fin 4, (i ∈ ({0, 1} : Finset (Fin 4)) ↔
    k ∈ ({0, 1} : Finset (Fin 4))) → (i ∈ ({1, 2} : Finset (Fin 4)) ↔
    k ∈ ({1, 2} : Finset (Fin 4))) → i = k := by decide

theorem no_line_kron (h2 : (2 : K) ≠ 0) {v : Fin (2 * 4) → K} (hv : v ≠ 0)
    (h₁ : signMat K (pairSet {0, 1}) *ᵥ v ∈ Submodule.span K {v})
    (h₂ : signMat K (pairSet {1, 2}) *ᵥ v ∈ Submodule.span K {v})
    (h₃ : kronI K 4 (cyc₁.permMatrix K) *ᵥ v ∈ Submodule.span K {v})
    (h₄ : kronI K 4 (cyc₂.permMatrix K) *ᵥ v ∈ Submodule.span K {v}) : False := by
  obtain ⟨p₀, hp₀⟩ : ∃ p, v p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  obtain ⟨⟨i₀, j₀⟩, rfl⟩ := (pairEquiv 4).surjective p₀
  have hblk : ∀ i j, v (pairEquiv 4 (i, j)) ≠ 0 → i = i₀ := by
    intro i j hij
    have hc : ∀ M : Finset (Fin 4), signMat K (pairSet M) *ᵥ v ∈ Submodule.span K {v} →
        (i ∈ M ↔ i₀ ∈ M) := by
      intro M hM
      rcases supp_of_sign_line h2 hM with h | h
      · constructor
        · intro hi
          exact absurd (h _ ((mem_pairSet M i j).2 hi)) hij
        · intro hi
          exact absurd (h _ ((mem_pairSet M i₀ j₀).2 hi)) hp₀
      · constructor
        · intro _
          by_contra hi
          exact hp₀ (h _ fun hm => hi ((mem_pairSet M i₀ j₀).1 hm))
        · intro _
          by_contra hi
          exact hij (h _ fun hm => hi ((mem_pairSet M i j).1 hm))
    exact blocks_eq_of_chars i i₀ (hc _ h₁) (hc _ h₂)
  have hfix : ∀ σ : Equiv.Perm (Fin 4), kronI K 4 (σ.permMatrix K) *ᵥ v ∈ Submodule.span K {v} →
      σ i₀ = i₀ := by
    intro σ hσ
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 hσ
    have e := congrFun hμ (pairEquiv 4 (σ⁻¹ i₀, j₀))
    have hσσ : σ (σ⁻¹ i₀) = i₀ := by simp
    rw [kronI_perm_mulVec, hσσ, Pi.smul_apply, smul_eq_mul] at e
    have hne : v (pairEquiv 4 (σ⁻¹ i₀, j₀)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e
      exact hp₀ e.symm
    have := hblk _ _ hne
    rw [Equiv.Perm.inv_eq_iff_eq] at this
    exact this.symm
  exact cyc_no_common_fixed i₀ (hfix _ h₃) (hfix _ h₄)

@[expose] def eigPlusMap (s : K) : (Fin 4 → K) →ₗ[K] (Fin (2 * 4) → K) where
  toFun x := blkVec fun i => ![s * x i, x i]
  map_add' x x' := by
    funext p
    simp only [blkVec, Pi.add_apply]
    generalize ((pairEquiv 4).symm p).2 = j
    fin_cases j <;> simp [mul_add]
  map_smul' a x := by
    funext p
    simp only [blkVec, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    generalize ((pairEquiv 4).symm p).2 = j
    fin_cases j <;> simp [mul_left_comm]

theorem eigPlusMap_apply (s : K) (x : Fin 4 → K) :
    eigPlusMap s x = blkVec fun i => ![s * x i, x i] := rfl

theorem mem_eigPlus_iff (s : K) (v : Fin (2 * 4) → K) :
    v ∈ LinearMap.range (eigPlusMap s) ↔ blkDiag 4 (jMat (s ^ 2)) *ᵥ v = s • v := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [eigPlusMap_apply, blkDiag_eq, blkDiagF_mulVec]
    funext p
    obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv 4).surjective p
    rw [Pi.smul_apply, blkVec_apply, blkVec_apply]
    fin_cases j <;> simp [jMat, mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · intro h
    refine ⟨fun i => v (pairEquiv 4 (i, 1)), ?_⟩
    rw [eigPlusMap_apply]
    conv_rhs => rw [← blkVec_blkOf v]
    congr 1
    funext i j
    have e := congrFun h (pairEquiv 4 (i, 1))
    rw [← blkVec_blkOf v, blkDiag_eq, blkDiagF_mulVec, blkVec_apply, Pi.smul_apply,
      blkVec_apply] at e
    simp only [jMat, mulVec, dotProduct, Fin.sum_univ_two, blkOf] at e
    fin_cases j
    · simpa [blkOf] using e.symm
    · simp [blkOf]

theorem isTS_eigPlus {s : K} {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (wMat 1 (-(s ^ 2)))) :
    IsTS (oQ R) 4 (LinearMap.range (eigPlusMap s)) := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj, Module.finrank_fin_fun]
    intro x x' h
    funext i
    have := congrArg (fun v => v (pairEquiv 4 (i, 1))) h
    simp only [eigPlusMap_apply, blkVec_apply] at this
    simpa using this
  · rintro _ ⟨x, rfl⟩
    rw [eigPlusMap_apply, oQ_blkDiag_pc hR]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp
    ring

theorem subPerm_eigPlus {s : K} {X : GL (Fin (2 * 4)) K}
    (hX : (X : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * blkDiag 4 (jMat (s ^ 2)) =
      blkDiag 4 (jMat (s ^ 2)) * X) :
    subPerm X (LinearMap.range (eigPlusMap s)) = LinearMap.range (eigPlusMap s) := by
  have hle : ∀ Y : GL (Fin (2 * 4)) K,
      (Y : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * blkDiag 4 (jMat (s ^ 2)) =
        blkDiag 4 (jMat (s ^ 2)) * Y →
      subPerm Y (LinearMap.range (eigPlusMap s)) ≤ LinearMap.range (eigPlusMap s) := by
    rintro Y hY _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_eigPlus_iff] at hv
    rw [mem_eigPlus_iff]
    change blkDiag 4 (jMat (s ^ 2)) *ᵥ ((Y : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
      s • ((Y : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v)
    rw [mulVec_mulVec, ← hY, ← mulVec_mulVec, hv, mulVec_smul]
  refine le_antisymm (hle X hX) ?_
  have hXi : ((X⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
      blkDiag 4 (jMat (s ^ 2)) = blkDiag 4 (jMat (s ^ 2)) * (X⁻¹ : GL (Fin (2 * 4)) K) := by
    have h1 : ((X⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
        (X : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (X : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
        ((X⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((X⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
          blkDiag 4 (jMat (s ^ 2)) =
        ((X⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
          blkDiag 4 (jMat (s ^ 2)) * ((X : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
            ((X⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)) := by
          rw [h2, Matrix.mul_one]
      _ = ((X⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
          ((blkDiag 4 (jMat (s ^ 2)) * X) *
            ((X⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [← hX]
          simp only [← Matrix.mul_assoc]
          rw [h1, Matrix.one_mul]
  have h := Submodule.map_mono (f := (matrixLinearEquiv X).toLinearMap) (hle _ hXi)
  rw [← subPerm_apply, ← subPerm_apply, ← Equiv.Perm.mul_apply, ← subPerm_mul, mul_inv_cancel,
    subPerm, map_one, map_one, Equiv.Perm.one_apply] at h
  exact h

theorem commutator_isoCent_le {d : ℕ} (h2 : (2 : K) ≠ 0) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (A : GL (Fin d) K) :
    ⁅isoCent R A, isoCent R A⁆ ≤ matrixDerived (oQ R) := by
  rw [matrixDerived_oQ h2 R hR]
  exact commutator_mono inf_le_left inf_le_left

theorem cent_fix_gen [Finite K] {d : ℕ} (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))).range ≤ B)
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hcd : CompData ⁅isoCent R g.val.left, isoCent R g.val.left⁆)
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (hy : y ∈ oddCoreIn B (oκ _ g))
    {X : GL (Fin d) K} (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆) :
    y (projH _ ⟨X, commutator_isoCent_le (Ring.two_ne_zero hK) hR _ hX⟩) =
      projH _ ⟨X, commutator_isoCent_le (Ring.two_ne_zero hK) hR _ hX⟩ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set A := g.val.left with hA
  set φ := (matrixDerivedConjugation (oQ R) g).toMonoidHom with hφ
  have hφc : ∀ Y : matrixDerived (oQ R), ((φ Y : matrixDerived (oQ R)) : GL (Fin d) K) =
      A * Y * A⁻¹ := by
    intro Y
    change (matrixDerivedConjugation (oQ R) g Y).val = _
    rw [matrixDerivedConjugation_val, hg1, map_one, MulAut.one_apply]
  refine fix_of_compData hinj hB φ (fun Y => kappa_lift _ Y) (commutator_isoCent_le h2 hR A)
    (fun X hX => ?_) (fun h hh X hX => ?_) hcd hy hX
  · apply Subtype.ext
    rw [hφc]
    have hc := mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (Subgroup.commutator_le_self _ hX)).2
    change A * X * A⁻¹ = X
    rw [← hc, mul_inv_cancel_right]
  · have hh' : A * (h : GL (Fin d) K) * A⁻¹ =
        GeneralLinearGroup.scalar (Fin d) (1 : Kˣ) * h := by
      rw [map_one, one_mul, ← hφc, hh]
    have hhI : (h : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K R :=
      Subgroup.commutator_le_self _ (by rw [← matrixDerived_oQ h2 R hR]; exact h.2)
    exact conj_mem_commutator_isoCent hhI hh' hX

section Kron

variable {R A : GL (Fin (2 * 4)) K} {W₀ j₀ : Matrix (Fin 2) (Fin 2) K}
  (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 W₀)
  (hA : (A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 j₀)

include hR hA in
theorem exists_kron_sign {i k : Fin 4} (hik : i ≠ k) :
    ∃ e ∈ ⁅isoCent R A, isoCent R A⁆,
      (e : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = signMat K (pairSet {i, k}) := by
  have hab : (0 : K) ^ 2 + 1 ^ 2 = 1 := by ring
  refine ⟨⁅kronGL K 4 (reflGL i), kronGL K 4 (rotGL i k hik hab)⁆,
    commutator_mem_commutator (kronGL_mem_isoCent_blkDiag hR hA (reflGL_orth _))
      (kronGL_mem_isoCent_blkDiag hR hA (rotGL_orth _ hab)), ?_⟩
  rw [← map_commutatorElement, coe_kronGL, signMat_pair_eq_commutator, kronI_signMat]

include hR hA in
theorem exists_kron_cyc (σ τ : Equiv.Perm (Fin 4)) :
    ∃ e ∈ ⁅isoCent R A, isoCent R A⁆,
      (e : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 ((⁅σ, τ⁆)⁻¹.permMatrix K) := by
  refine ⟨⁅kronGL K 4 (permGL K 4 σ), kronGL K 4 (permGL K 4 τ)⁆,
    commutator_mem_commutator (kronGL_mem_isoCent_blkDiag hR hA (permGL_orth _))
      (kronGL_mem_isoCent_blkDiag hR hA (permGL_orth _)), ?_⟩
  rw [← map_commutatorElement, coe_kronGL, coe_commutator_permGL]

end Kron

theorem commute_of_mem_commutator_isoCent {d : ℕ} {R A X : GL (Fin d) K}
    (hX : X ∈ ⁅isoCent R A, isoCent R A⁆) :
    (X : Matrix (Fin d) (Fin d) K) * A = (A : Matrix (Fin d) (Fin d) K) * X := by
  have hc := mem_centralizer_singleton_iff.1
    (Subgroup.mem_inf.1 (Subgroup.commutator_le_self _ hX)).2
  rw [← Units.val_mul, ← Units.val_mul, hc]

theorem pc_sq_false [Finite K] (hK : ringChar K ≠ 2) {s : K} (hs : s ≠ 0)
    {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (wMat 1 (-(s ^ 2))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat (s ^ 2)))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : Sit (oQ R) B (oκ _ g) y) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRs : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R := by
    rw [hR, blkDiag_transpose', wMat_transpose]
  have hcd := compData_anti h2 hs (by norm_num) hR hgA
  obtain ⟨e₁, hm₁, hv₁⟩ := exists_kron_sign hR hgA (i := 0) (k := 1) (by decide)
  obtain ⟨e₂, hm₂, hv₂⟩ := exists_kron_sign hR hgA (i := 1) (k := 2) (by decide)
  obtain ⟨e₃, hm₃, hv₃⟩ := exists_kron_cyc hR hgA (Equiv.swap 0 1) (Equiv.swap 1 2)
  obtain ⟨e₄, hm₄, hv₄⟩ := exists_kron_cyc hR hgA (Equiv.swap 1 2) (Equiv.swap 2 3)
  have hle := commutator_isoCent_le h2 hRs g.val.left
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (StatedProj (matrixDerived (oQ R))),
      H = closure {projH _ ⟨e₁, hle hm₁⟩, projH _ ⟨e₂, hle hm₂⟩, projH _ ⟨e₃, hle hm₃⟩,
        projH _ ⟨e₄, hle hm₄⟩} := ⟨_, rfl⟩
  have hHfix : ∀ x ∈ H, y x = x := by
    rw [hH]
    refine fix_closure ?_
    rintro _ (rfl | rfl | rfl | rfl)
    · exact cent_fix_gen hK hRs h.inj h.inn hg1 hcd h.core hm₁
    · exact cent_fix_gen hK hRs h.inj h.inn hg1 hcd h.core hm₂
    · exact cent_fix_gen hK hRs h.inj h.inn hg1 hcd h.core hm₃
    · exact cent_fix_gen hK hRs h.inj h.inn hg1 hcd h.core hm₄
  have hfixV : ∀ {X : GL (Fin (2 * 4)) K} (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆),
      projH _ ⟨X, hle hX⟩ ∈ subStab (oQ R) (LinearMap.range (eigPlusMap s)) := by
    intro X hX
    rw [proj_mem_subStab_iff]
    exact subPerm_eigPlus (by rw [← hgA]; exact commute_of_mem_commutator_isoCent hX)
  have hHV : H ≤ subStab (oQ R) (LinearMap.range (eigPlusMap s)) := by
    rw [hH, closure_le]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hfixV hm₁
    · exact hfixV hm₂
    · exact hfixV hm₃
    · exact hfixV hm₄
  have htri := h.geom y (odd_orderOf_of_mem_oddCoreIn h.core) h.move
  obtain ⟨L, hHL⟩ := htri.exists_pt_of_ts hHfix (isTS_eigPlus hR) hHV
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  have hline : ∀ {X : GL (Fin (2 * 4)) K} (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆),
      projH _ ⟨X, hle hX⟩ ∈ H → (X : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x ∈
        Submodule.span K {x} := by
    intro X hX hXH
    have h1 := hHL hXH
    rw [proj_mem_subStab_iff, pointMk_submodule] at h1
    rw [← h1]
    exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
  have hin : ∀ i : Fin 4, ∀ X (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆),
      (i = 0 ∧ X = e₁) ∨ (i = 1 ∧ X = e₂) ∨ (i = 2 ∧ X = e₃) ∨ (i = 3 ∧ X = e₄) →
      projH _ ⟨X, hle hX⟩ ∈ H := by
    rintro i X hX (⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩) <;> rw [hH] <;>
      exact subset_closure (by simp)
  have l₁ := hline hm₁ (hin 0 _ hm₁ (Or.inl ⟨rfl, rfl⟩))
  have l₂ := hline hm₂ (hin 1 _ hm₂ (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have l₃ := hline hm₃ (hin 2 _ hm₃ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have l₄ := hline hm₄ (hin 3 _ hm₄ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  rw [hv₁] at l₁
  rw [hv₂] at l₂
  rw [hv₃] at l₃
  rw [hv₄] at l₄
  exact no_line_kron h2 hx l₁ l₂ l₃ l₄

end CFSG.ComponentClassification.Burgoyne.D4
