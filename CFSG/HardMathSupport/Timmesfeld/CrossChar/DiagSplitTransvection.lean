module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane

variable {n : ℕ} {F : Type} [Field F]

theorem transvection_data_gl (M P : GL (Fin n) F)
    (hdiag : ∀ k l, k ≠ l → ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l = 0)
    (k : Fin n) :
    ∃ u : Fin n → F, u ≠ 0 ∧ (M : Matrix (Fin n) (Fin n) F).mulVec u =
      ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k k • u ∧
      (P : Matrix (Fin n) (Fin n) F).mulVec u = Pi.single k 1 := by
  set D : Matrix (Fin n) (Fin n) F :=
    ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hDdef
  have hPP : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin n) (Fin n) F) *
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA : (M : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * D := by
    simp only [hDdef, Units.val_mul]
    calc (M : Matrix (Fin n) (Fin n) F) * ↑P⁻¹
        = ↑P⁻¹ * ↑P * ↑M * ↑P⁻¹ := by rw [hPP, Matrix.one_mul]
      _ = ↑P⁻¹ * (↑P * ↑M * ↑P⁻¹) := by simp only [Matrix.mul_assoc]
  refine ⟨((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single k 1), ?_, ?_, ?_⟩
  · intro h0
    have := congrArg (fun v => (P : Matrix (Fin n) (Fin n) F).mulVec v) h0
    simp only [Matrix.mulVec_mulVec, hPP', Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have h1 := congrFun this k
    simp at h1
  · have hDk : D.mulVec (Pi.single k 1) = D k k • (Pi.single k 1 : Fin n → F) := by
      ext r
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      by_cases hr : r = k
      · subst hr
        rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb])
          (fun h => absurd (Finset.mem_univ r) h)]
      · simp [hdiag r k hr, Pi.single_apply, hr]
    rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hDk, Matrix.mulVec_smul]
  · rw [Matrix.mulVec_mulVec, hPP', Matrix.one_mulVec]

theorem transvection_mem_blockImage_gl (M P : GL (Fin n) F)
    (hdiag : ∀ k l, k ≠ l → ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l = 0)
    {i j : Fin n} (hij : i ≠ j)
    (hd : ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i =
      ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j)
    (c : F) (hsq : Squarefree (minpoly F (Matrix.toLin' (M : Matrix (Fin n) (Fin n) F)))) :
    ∃ hX : (X - C (((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i) : F[X]) ∈
        primaryFactors (Matrix.toLin' (M : Matrix (Fin n) (Fin n) F)),
      2 ≤ mult (Matrix.toLin' (M : Matrix (Fin n) (Fin n) F))
          ⟨X - C (((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i), hX⟩ ∧
      ∀ s : SpecialLinearGroup (Fin n) F,
        (s : Matrix (Fin n) (Fin n) F) =
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 + Matrix.single i j c) *
            (P : Matrix (Fin n) (Fin n) F) →
        SpecialLinearGroup.toGL s ∈ blockImage hsq
          ⟨X - C (((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i), hX⟩ := by
  classical
  set D : Matrix (Fin n) (Fin n) F :=
    ((P * M * P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hDdef
  set μ : F := D i i with hμ
  set x : Module.End F (Fin n → F) := Matrix.toLin' (M : Matrix (Fin n) (Fin n) F) with hx
  obtain ⟨ui, hui0, hAui, hPui⟩ := transvection_data_gl M P hdiag i
  obtain ⟨uj, huj0, hAuj, hPuj⟩ := transvection_data_gl M P hdiag j
  have hAui' : (M : Matrix (Fin n) (Fin n) F).mulVec ui = μ • ui := hAui
  have hAuj' : (M : Matrix (Fin n) (Fin n) F).mulVec uj = μ • uj := by rw [hd]; exact hAuj
  have hmemi : ui ∈ primaryComponent x (X - C μ) := by
    rw [mem_primaryComponent]
    simp [hx, Matrix.toLin'_apply, hAui']
  have hmemj : uj ∈ primaryComponent x (X - C μ) := by
    rw [mem_primaryComponent]
    simp [hx, Matrix.toLin'_apply, hAuj']
  have hX : (X - C μ : F[X]) ∈ primaryFactors x :=
    mem_primaryFactors_of_ne_zero (irreducible_X_sub_C μ) (monic_X_sub_C μ) hui0 hmemi
  have : Fact (Irreducible (X - C μ : F[X])) := ⟨irreducible_X_sub_C μ⟩
  have hmult2 : 2 ≤ mult x ⟨X - C μ, hX⟩ := by
    have hli : LinearIndependent F ![ui, uj] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (fun v => (P : Matrix (Fin n) (Fin n) F).mulVec v) hst
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hPui, hPuj, Matrix.mulVec_zero] at h1
      have hi := congrFun h1 i
      have hj := congrFun h1 j
      simp [hij, Ne.symm hij] at hi hj
      exact ⟨hi, hj⟩
    have hspan : Submodule.span F (Set.range ![ui, uj]) ≤ primaryComponent x (X - C μ) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      fin_cases t
      · exact hmemi
      · exact hmemj
    have h2 : 2 ≤ finrank F (primaryComponent x (X - C μ)) := by
      have h4 := finrank_span_eq_card hli
      rw [Fintype.card_fin] at h4
      calc 2 = _ := h4.symm
        _ ≤ _ := Submodule.finrank_mono hspan
    have h3 := finrank_primaryComponent x (X - C μ)
    rw [natDegree_X_sub_C, one_mul] at h3
    change 2 ≤ finrank (AdjoinRoot (X - C μ)) (primaryComponent x (X - C μ))
    omega
  refine ⟨hX, hmult2, ?_⟩
  intro s hs
  have hPP : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin n) (Fin n) F) *
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP'' : ∀ N : Matrix (Fin n) (Fin n) F, (P : Matrix (Fin n) (Fin n) F) *
      (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * N) = N := fun N => by
    rw [← Matrix.mul_assoc, hPP', Matrix.one_mul]
  have hPP''' : ∀ N : Matrix (Fin n) (Fin n) F,
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((P : Matrix (Fin n) (Fin n) F) * N) =
        N := fun N => by
    rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hDdiag : D = Matrix.diagonal (fun k => D k k) := by
    ext r s'
    by_cases h : r = s'
    · subst h; simp
    · simp [hdiag r s' h, Matrix.diagonal_apply_ne _ h]
  have hAD : (M : Matrix (Fin n) (Fin n) F) =
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (D * (P : Matrix (Fin n) (Fin n) F)) := by
    simp only [hDdef, Units.val_mul, Matrix.mul_assoc, hPP''']
    rw [hPP, Matrix.mul_one]
  set E : Matrix (Fin n) (Fin n) F := Matrix.single i j c with hE
  set Bm : Matrix (Fin n) (Fin n) F := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
    (E * (P : Matrix (Fin n) (Fin n) F)) with hBm
  have hED : E * D = D * E := by
    have := single_mul_diagonal_comm (i := i) (j := j) (fun k => D k k) hd c
    rwa [← hDdiag] at this
  have hcommM : Bm * (M : Matrix (Fin n) (Fin n) F) = (M : Matrix (Fin n) (Fin n) F) * Bm := by
    rw [hAD]
    simp only [hBm, Matrix.mul_assoc, hPP'']
    rw [← Matrix.mul_assoc E, ← Matrix.mul_assoc D, hED]
  have hBB : Bm * Bm = 0 := by
    simp only [hBm, Matrix.mul_assoc, hPP'']
    rw [← Matrix.mul_assoc E, hE, Matrix.single_mul_single_of_ne c i j i hij.symm c,
      Matrix.zero_mul, Matrix.mul_zero]
  set β : Module.End F (Fin n → F) := Matrix.toLin' Bm with hβdef
  have hcomm : β * x = x * β := by
    rw [hβdef, hx, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      ← Matrix.toLin'_mul, hcommM]
  have hβ : β ∈ commutant x := (mem_commutant x).2 hcomm
  have hββ : β * β = 0 := by
    rw [hβdef, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hBB, map_zero]
  have hβv : ∀ v, β v = (c * (P : Matrix (Fin n) (Fin n) F).mulVec v j) • ui := by
    intro v
    have hui : ui = ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single i 1) := by
      rw [← hPui, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
    rw [hβdef, Matrix.toLin'_apply, hBm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hE,
      single_mulVec, hui, ← Matrix.mulVec_smul]
    congr 1
    ext r
    simp [Pi.single_apply]
  have hkill : ∀ k ∈ primaryFactors x, k ≠ (⟨X - C μ, hX⟩ : primaryFactors x).1 →
      ∀ v ∈ primaryComponent x k, β v = 0 := by
    intro k hk hkne v hv
    have h1 : β v ∈ primaryComponent x k := apply_mem_primaryComponent hcomm hv
    have h2 : β v ∈ primaryComponent x (X - C μ) := by
      rw [hβv]; exact Submodule.smul_mem _ _ hmemi
    exact eq_zero_of_mem_primaryComponent_ne hk hX hkne h1 h2
  have hdet : LinearMap.det (1 + commutantRestrict (X - C μ) ⟨β, hβ⟩) = 1 := by
    apply det_eq_one_of_restrictScalars (natDegree_X_sub_C μ)
    have hmaps : ∀ w ∈ primaryComponent x (X - C μ), β w ∈ primaryComponent x (X - C μ) :=
      fun w hw => apply_mem_primaryComponent hcomm hw
    have hrs : ((1 + commutantRestrict (X - C μ) ⟨β, hβ⟩ :
        Module.End (AdjoinRoot (X - C μ)) (primaryComponent x (X - C μ))).restrictScalars F) =
        1 + β.restrict hmaps := rfl
    rw [hrs]
    refine det_one_add_of_range_le_ker (β.restrict hmaps)
      (Submodule.span F {(⟨ui, hmemi⟩ : primaryComponent x (X - C μ))}) ?_ ?_
    · intro w
      refine Submodule.mem_span_singleton.2 ⟨c * (P : Matrix (Fin n) (Fin n) F).mulVec w j, ?_⟩
      apply Subtype.ext
      exact (hβv w).symm
    · intro w hw
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul]
      have : (β.restrict hmaps) ⟨ui, hmemi⟩ = 0 := by
        apply Subtype.ext
        change β ui = 0
        rw [hβv, hPui]
        simp [Ne.symm hij]
      rw [this, smul_zero]
  obtain ⟨gb, hgb, hgbv⟩ := exists_mem_blockImage_one_add hsq (a0 := M) rfl ⟨X - C μ, hX⟩ β hβ
    hββ hkill hdet
  have hsm : (s : Matrix (Fin n) (Fin n) F) = 1 + Bm := by
    rw [hs, hBm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP, Matrix.mul_assoc]
  have hgs : SpecialLinearGroup.toGL s = gb := by
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [hgbv v]
    change Matrix.toLin' (s : Matrix (Fin n) (Fin n) F) v = v + β v
    rw [hsm, Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec, hβdef, Matrix.toLin'_apply]
  rw [hgs]
  exact hgb

end CFSG.HardMathSupport.Timmesfeld.CrossChar
