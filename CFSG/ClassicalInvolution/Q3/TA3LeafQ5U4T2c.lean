module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4T2b
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Fix
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTU4Cls

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks PSpL UnitaryOut
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem bdK_slU (c : h.fixedField) :
    bdK h (slU c, (1 : SpecialLinearGroup (Fin 2) h.fixedField)) = bd (uu (c : K)) 1 := by
  rw [bdK]
  simp only [slU, Matrix.SpecialLinearGroup.coe_one]
  rw [map_one_fixed, map_uu]

theorem map_bar_eq_neg_inv {A : GL (Fin 4) K}
    (hAu : ((A : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K)) :
    (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -(↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  have hAAi : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : ((A : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    calc ((A : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ =
        ((A : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * ((A : Matrix (Fin 4) (Fin 4) K) *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by rw [hAAi, Matrix.mul_one]
      _ = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by rw [← Matrix.mul_assoc, hAu, Matrix.one_mul]
  have h2 : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ = -(↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    have e1 : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ * (A : Matrix (Fin 4) (Fin 4) K)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hAAi, Matrix.transpose_one]
    rw [hAt, Matrix.mul_neg] at e1
    have e2 : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ * (A : Matrix (Fin 4) (Fin 4) K) = -1 :=
      neg_eq_iff_eq_neg.mp e1
    calc (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ *
        ((A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          rw [hAAi, Matrix.mul_one]
      _ = -(↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
          rw [← Matrix.mul_assoc, e2, Matrix.neg_mul, Matrix.one_mul]
  rw [← Matrix.transpose_transpose ((A : Matrix (Fin 4) (Fin 4) K).map h.bar), h1, h2]

theorem mul_self_eq_one_of_map_bar {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    {A : GL (Fin 4) K} {φ : K ≃+* K}
    {hA : ∀ g : unitarySU p f K 4, A * glAut φ (g : GL (Fin 4) K) * A⁻¹ ∈ unitarySU p f K 4}
    (hlift : ∀ g : unitarySU p f K 4,
      (QuotientGroup.mk (unitaryConjHom A φ hA g) : StatedProj (StatedSU 4 (p ^ f) K)) =
        α (QuotientGroup.mk g))
    (hφ : ∀ c, φ c = h.bar c)
    (hbA : (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -(↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) :
    α * α = 1 := by
  have hφm : ∀ M : Matrix (Fin 4) (Fin 4) K, M.map φ = M.map h.bar := fun M => by
    ext i j
    simp [hφ]
  have hAA : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAA' : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar = -(A : Matrix (Fin 4) (Fin 4) K) := by
    have e1 : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (A : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
      rw [← Matrix.map_mul, hAA', Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hbA, Matrix.mul_neg] at e1
    calc (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar =
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (A : Matrix (Fin 4) (Fin 4) K)) := by rw [hAA', Matrix.mul_one]
      _ = -(A : Matrix (Fin 4) (Fin 4) K) := by
          rw [← Matrix.mul_assoc, neg_eq_iff_eq_neg.mp e1, Matrix.neg_mul, Matrix.one_mul]
  refine MulEquiv.ext fun z => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  rw [MulAut.mul_apply, MulAut.one_apply, ← hlift g, ← hlift]
  congr 1
  apply ext_val
  rw [coe_unitaryConjHom, Units.val_mul, Units.val_mul, coe_glAut, coe_unitaryConjHom,
    Units.val_mul, Units.val_mul, coe_glAut, hφm, hφm, Matrix.map_mul, Matrix.map_mul,
    hbA, hbAi, Matrix.map_map]
  have hbb : (h.bar ∘ h.bar) = id := funext h.bar_bar
  rw [hbb, Matrix.map_id]
  calc (A : Matrix (Fin 4) (Fin 4) K) * (-(↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * -(A : Matrix (Fin 4) (Fin 4) K)) *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
      ((A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
        simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    _ = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
        rw [hAA, Matrix.one_mul, Matrix.mul_one]

include h in
theorem dichotomy_t2 (hp2 : p ≠ 2) {R : GL (Fin 4) K} {t : K} (ht0 : t ≠ 0)
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    (α : MulAut (StatedProj (StatedSU 4 (p ^ f) K)))
    (hfix : ∀ x, α (QuotientGroup.mk (bdHomU h hR x)) = QuotientGroup.mk (bdHomU h hR x)) :
    α ∈ blkConjU p f R ∨ α * α = 1 := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2K h2K
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' (scal p f K) with hθdef
  have hθ : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hker : θ.ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [hθdef, QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  obtain ⟨A, φ, hA, hAu, hlift, -⟩ :=
    GH74.Generic.S45.exists_lift_unitarySU' h hp2 (d := 4) (by norm_num) θ hθ hker α
  have hlift' : ∀ g : unitarySU p f K 4,
      (QuotientGroup.mk (unitaryConjHom A φ hA g) : StatedProj (StatedSU 4 (p ^ f) K)) =
        α (QuotientGroup.mk g) := hlift
  have key : ∀ x, (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).trace = 4 →
      (A : Matrix (Fin 4) (Fin 4) K) *
        (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    intro x hx
    have e := conj_eq_of_fix h4 hlift' (hfix x) hx
    have e' := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) e
    simpa only [Units.val_mul, coe_glAut] using e'
  obtain ⟨G, hG⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
      M = (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (R : Matrix (Fin 4) (Fin 4) K).map φ :=
    ⟨_, rfl⟩
  have hcomm : ∀ x, (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).trace = 4 → G * (bdK h x).map φ = bdK h x * G := by
    intro x hx
    have e := comm_cP_of_fix_map R φ (key x hx)
    rw [cP_bdHomU] at e
    rw [hG]
    exact e
  obtain ⟨k1, k2, k3, k4⟩ := gens_mem (F := h.fixedField)
  obtain ⟨g1, g2, g3, g4⟩ := bdK_gens h
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) K, (M = bd (uu 1) 1 ∨ M = bd (ll 1) 1 ∨
      M = bd 1 (uu 1) ∨ M = bd 1 (ll 1)) → M.map φ = M := by
    intro M hM
    rcases hM with rfl | rfl | rfl | rfl <;>
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [bd, uu, ll]
  have c1 := hcomm _ (trace_bdHomU_gens h hR k1)
  have c2 := hcomm _ (trace_bdHomU_gens h hR k2)
  have c3 := hcomm _ (trace_bdHomU_gens h hR k3)
  have c4 := hcomm _ (trace_bdHomU_gens h hR k4)
  rw [g1, hmap _ (Or.inl rfl)] at c1
  rw [g2, hmap _ (Or.inr (Or.inl rfl))] at c2
  rw [g3, hmap _ (Or.inr (Or.inr (Or.inl rfl)))] at c3
  rw [g4, hmap _ (Or.inr (Or.inr (Or.inr rfl)))] at c4
  have hGd := eq_of_comm_bd c1 c2 c3 c4
  set x₀ := G 0 0 with hx₀
  set y₀ := G 2 2 with hy₀
  have hGdet : G.det ≠ 0 := by
    rw [hG, det_mul, det_mul, ← RingEquiv.mapMatrix_apply, ← RingEquiv.map_det]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact (Matrix.isUnits_det_units R⁻¹).ne_zero
    · exact (Matrix.isUnits_det_units A).ne_zero
    · exact (map_ne_zero φ).mpr (Matrix.isUnits_det_units R).ne_zero
  have hx0 : x₀ ≠ 0 := by
    intro h0
    apply hGdet
    rw [hGd, det_bd, h0]
    simp
  have hφF : ∀ c : K, h.bar c = c → φ c = c := by
    intro c hc
    set c' : h.fixedField := ⟨c, h.mem_fixedField.2 hc⟩ with hc'
    have htr : (((bdHomU h hR (slU c', 1) : unitarySU p f K 4) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).trace = 4 := by
      rw [val_bdHomU, StabU.trace_conj', bdK_slU h c', trace_bd, trace_uu, Matrix.trace_one,
        Fintype.card_fin]
      norm_num
    have e := hcomm (slU c', 1) htr
    have hmb : ∀ a b : Matrix (Fin 2) (Fin 2) K, (bd a b).map φ = bd (a.map φ) (b.map φ) :=
      fun a b => map_bd (φ : K →+* K) a b
    rw [bdK_slU h c', hmb, Matrix.map_one _ (map_zero φ) (map_one φ), hGd, bd_mul,
      bd_mul] at e
    have e1 := congrArg ul e
    rw [ul_bd, ul_bd, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at e1
    have e2 := smul_right_injective _ hx0 e1
    have e3 := congrFun (congrFun e2 0) 1
    simpa [uu] using e3
  rcases ringEquiv_eq_refl_or_bar_of_fixes' h hφF with hφ1 | hφb
  · left
    subst hφ1
    have hmap1 : ∀ M : Matrix (Fin 4) (Fin 4) K, M.map (RingEquiv.refl K) = M := fun M => by
      ext
      simp
    refine ⟨A, ⟨x₀, y₀, ?_⟩, fun g => ⟨unitaryConjHom A (RingEquiv.refl K) hA g, ?_,
      (hlift' g).symm⟩⟩
    · rw [← hGd, hG, hmap1]
    · rw [coe_unitaryConjHom, Units.val_mul, Units.val_mul, coe_glAut, hmap1]
  · right
    have hφm : ∀ M : Matrix (Fin 4) (Fin 4) K, M.map φ = M.map h.bar := fun M => by
      ext i j
      simp [hφb]
    have hAeq : (A : Matrix (Fin 4) (Fin 4) K) = (R : Matrix (Fin 4) (Fin 4) K) * G *
        (t⁻¹ • (bJ 1 1 * (R : Matrix (Fin 4) (Fin 4) K)ᵀ)) := by
      rw [hG, hφm]
      exact eq_conj_of_mul_eq_one R (map_bar_mul_eq_one h ht0 hR)
    have hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K) := by
      have e1 : (A : Matrix (Fin 4) (Fin 4) K) = t⁻¹ • ((R : Matrix (Fin 4) (Fin 4) K) *
          bJ x₀ y₀ * (R : Matrix (Fin 4) (Fin 4) K)ᵀ) := by
        rw [hAeq, hGd, Matrix.mul_smul, ← bd_smul_mul_bJ x₀ y₀]
        simp only [Matrix.mul_assoc]
      rw [e1, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, TBlocks.transpose_bJ, Matrix.neg_mul, Matrix.mul_neg,
        ← Matrix.mul_assoc, smul_neg]
    exact mul_self_eq_one_of_map_bar h hlift' hφb (map_bar_eq_neg_inv h hAu hAt)

include h in
theorem noQ8Fix_t2 (hp2 : p ≠ 2) {R : GL (Fin 4) K} {t : K} (ht0 : t ≠ 0)
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1) :
    NoQ8Fix (StatedProj (StatedSU 4 (p ^ f) K))
      ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range :=
  noQ8Fix_of_dichotomy (blkConjU p f R) (blkConjU_comm R) fun α hfix =>
    dichotomy_t2 h hp2 ht0 hR α fun x => hfix _ ⟨x, rfl⟩

end CFSG.ClassicalInvolution.Q3.TA3.Q5U4
