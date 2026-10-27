module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Pairb
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4T2c

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks UnitaryOut UnitaryConj
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

variable {P : GL (Fin 4) K}
  (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)

include hP in
theorem unitary_conj_map {A : GL (Fin 4) K} {φ : K ≃+* K}
    (hAu : ((A : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    {M : Matrix (Fin 4) (Fin 4) K}
    (hM : M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (P : Matrix (Fin 4) (Fin 4) K).map φ) :
    uStar h M * stdG * M = stdG := by
  have hAu' : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := hAu
  have hPi := uStar_inv_mul h P hP
  rw [hM, uStar_mul, uStar_mul]
  calc uStar h ((P : Matrix (Fin 4) (Fin 4) K).map φ) *
        (uStar h (A : Matrix (Fin 4) (Fin 4) K) * uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
        stdG * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) *
          (P : Matrix (Fin 4) (Fin 4) K).map φ) =
      uStar h ((P : Matrix (Fin 4) (Fin 4) K).map φ) *
        (uStar h (A : Matrix (Fin 4) (Fin 4) K) * ((uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          stdG * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (A : Matrix (Fin 4) (Fin 4) K))) *
        (P : Matrix (Fin 4) (Fin 4) K).map φ := by simp only [Matrix.mul_assoc]
    _ = uStar h ((P : Matrix (Fin 4) (Fin 4) K).map φ) *
        (P : Matrix (Fin 4) (Fin 4) K).map φ := by
        rw [hPi, Matrix.one_mul, hAu', Matrix.mul_one]
    _ = stdG := by
        rw [uStar_map_equiv, ← Matrix.map_mul, hP]
        exact stdG_map (φ : K →+* K)

theorem map_bar_eq_neg_inv_of_conj {A : GL (Fin 4) K} {M : Matrix (Fin 4) (Fin 4) K}
    (hM : M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (P : Matrix (Fin 4) (Fin 4) K).map h.bar)
    (hMM : M * M.map h.bar = -1) :
    (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -(↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  have hbb : (h.bar ∘ h.bar) = id := funext h.bar_bar
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbP : (P : Matrix (Fin 4) (Fin 4) K).map h.bar *
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
    rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hbP' : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar *
      (P : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero _) (map_one _)]
  have hAe : (A : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar := by
    rw [hM]
    simp only [← Matrix.mul_assoc]
    rw [hPP, Matrix.one_mul, Matrix.mul_assoc, hbP, Matrix.mul_one]
  have hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -1 := by
    rw [hAe, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, hbb, Matrix.map_id]
    calc (P : Matrix (Fin 4) (Fin 4) K) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar *
          ((P : Matrix (Fin 4) (Fin 4) K).map h.bar * M.map h.bar *
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        (P : Matrix (Fin 4) (Fin 4) K) * (M * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar *
          (P : Matrix (Fin 4) (Fin 4) K).map h.bar) * M.map h.bar) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
      _ = -1 := by
          rw [hbP', Matrix.mul_one, hMM, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hPP]
  have hAA' : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * A) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar := by
        rw [hAA', Matrix.one_mul]
    _ = -(↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        rw [Matrix.mul_assoc, hAA, Matrix.mul_neg, Matrix.mul_one]

include h in
theorem dichotomy_pair (hp2 : p ≠ 2) {μ : Kˣ} (hμ : ∀ x : Kˣ, x ∈ Subgroup.zpowers μ)
    (α : MulAut (StatedProj (StatedSU 4 (p ^ f) K)))
    (h1 : α (QuotientGroup.mk (uU h P hP 1)) = QuotientGroup.mk (uU h P hP 1))
    (h2 : α (QuotientGroup.mk (uL h P hP 1)) = QuotientGroup.mk (uL h P hP 1))
    (h3 : α (QuotientGroup.mk (uU h P hP μ)) = QuotientGroup.mk (uU h P hP μ)) :
    α ∈ blkConjU p f P ∨ α * α = 1 := by
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
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
      M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (P : Matrix (Fin 4) (Fin 4) K).map φ :=
    ⟨_, rfl⟩
  have key : ∀ g : unitarySU p f K 4, α (QuotientGroup.mk g) = QuotientGroup.mk g →
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4 →
      M * (cP P g).map φ = cP P g * M := by
    intro g hg htr
    have e := conj_eq_of_fix h4 hlift' hg htr
    have e' := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) e
    simp only [Units.val_mul, coe_glAut] at e'
    rw [hM]
    exact comm_cP_of_fix_map P φ e'
  have hE1 := key _ h1 (trace_uU h hP 1)
  have hE2 := key _ h2 (trace_uL h hP 1)
  have hE3 := key _ h3 (trace_uU h hP μ)
  rw [cP_uU, map_U12_equiv, map_one] at hE1
  rw [cP_uL, map_U21_equiv, map_one] at hE2
  rw [cP_uU, map_U12_equiv] at hE3
  have hblk := eq_blk_of_comm h hE1 hE2
  rw [hblk] at hE3
  obtain ⟨r1, r2, r3, r4⟩ := blk_rel h hE3
  have hMu := unitary_conj_map h hP hAu hM
  rw [hblk] at hMu
  have hun := blk_unitary h hMu
  have hμb := bar_ne_of_generator h hμ
  by_cases hφμ : φ (μ : K) = μ
  · left
    have hφ1 : φ = RingEquiv.refl K := RingEquiv.ext fun c =>
      eq_of_eq_on_generator hμ (φ : K →+* K) (RingHom.id K) hφμ c
    have hb : M 0 3 = 0 := by
      rw [hφμ] at r2
      rcases mul_eq_zero.1 r2 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hμb
    have hf : M 2 1 = 0 := by
      rw [hφμ] at r3
      rcases mul_eq_zero.1 r3 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0).symm hμb
    have hMd : M = bd (M 0 0 • 1) (M 2 2 • 1) := by
      conv_lhs => rw [hblk]
      rw [hb, hf]
      exact blk_zero_eq_bd _ _
    subst hφ1
    have hmap1 : ∀ N : Matrix (Fin 4) (Fin 4) K, N.map (RingEquiv.refl K) = N := fun N => by
      ext
      simp
    refine ⟨A, ⟨M 0 0, M 2 2, ?_⟩, fun g => ⟨unitaryConjHom A (RingEquiv.refl K) hA g, ?_,
      (hlift' g).symm⟩⟩
    · rw [← hMd, hM, hmap1]
    · rw [coe_unitaryConjHom, Units.val_mul, Units.val_mul, coe_glAut, hmap1]
  · right
    have hx : M 0 0 = 0 := by
      rcases mul_eq_zero.1 r1 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hφμ
    have hy : M 2 2 = 0 := by
      rcases mul_eq_zero.1 r4 with h0 | h0
      · exact h0
      · exfalso
        apply hφμ
        have e := congrArg h.bar (sub_eq_zero.1 h0)
        rwa [h.bar_bar, h.bar_bar] at e
    rw [hx, hy, map_zero, zero_mul, add_zero] at hun
    have hf0 : M 2 1 ≠ 0 := by
      intro h0
      rw [h0, map_zero, mul_zero] at hun
      exact zero_ne_one hun
    have hφμb : φ (μ : K) = h.bar μ := by
      rcases mul_eq_zero.1 r3 with h0 | h0
      · exact absurd h0 hf0
      · exact sub_eq_zero.1 h0
    have hφb : ∀ c, φ c = h.bar c := eq_of_eq_on_generator hμ (φ : K →+* K) h.bar hφμb
    have hMb : M = blk 0 (M 0 3) (M 2 1) 0 := by
      conv_lhs => rw [hblk]
      rw [hx, hy]
    have hMM : M * M.map h.bar = -1 := by
      rw [hMb]
      exact blk_mul_map_bar h hun
    have hφm : ∀ N : Matrix (Fin 4) (Fin 4) K, N.map φ = N.map h.bar := fun N => by
      ext i j
      simp [hφb]
    rw [hφm] at hM
    exact mul_self_eq_one_of_map_bar h hlift' hφb (map_bar_eq_neg_inv_of_conj h hM hMM)

include h in
theorem noQ8Fix_pair (hp2 : p ≠ 2) :
    NoQ8Fix (StatedProj (StatedSU 4 (p ^ f) K))
      ((QuotientGroup.mk' (scal p f K)).comp (pairHom h hP)).range := by
  have : Finite K := h.finite
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨hu1, hu2, hu3⟩ := hasUnipU_pair h hP (μ : K)
  exact noQ8Fix_of_dichotomy (blkConjU p f P) (blkConjU_comm P) fun α hfix =>
    dichotomy_pair h hP hp2 hμ α (hfix _ hu1) (hfix _ hu2) (hfix _ hu3)

end CFSG.ClassicalInvolution.Q3.TA3.Q5U4
