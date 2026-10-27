module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcT1a

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Dr

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C (compInd_compl commute_compInd_of_commute_sign
  matrixDerived_le_isometryGroup)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL signMat compInd signMat_mul_self
  signMat_eq)

variable {K : Type} [Field K] {d : ℕ}

theorem exists_block_of_sign [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {M : Subgroup (GL (Fin d) K)} (hd : ExcData (diagGL hw) M)
    {J : Finset (Fin d)} (hJ : J.Nonempty) (hJc : Jᶜ.Nonempty)
    (hfix : ∀ X ∈ M, X * signGL K J = signGL K J * X)
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ (diagGL hw)))).map
      (projH _)).subgroupOf (autFixed (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))))
    {A : GL (Fin d) K} {a₀ : K} (ha₀ : a₀ ≠ 0)
    (hA2 : (A : Matrix (Fin d) (Fin d) K) * A = a₀ • 1)
    (hAR : (A : Matrix (Fin d) (Fin d) K)ᵀ * diagonal w = -(diagonal w * A))
    (hAM' : ∀ X ∈ M, A⁻¹ * X * A ∈ M)
    (hAS : A * signGL K J = signGL K J * A ∨
      (A : Matrix (Fin d) (Fin d) K) * signMat K J = -(signMat K J * A)) :
    ∃ I : Finset (Fin d), (I = J ∨ I = Jᶜ) ∧ M ≤ oBlock K hw I ∧
      compInd K I * (A : Matrix (Fin d) (Fin d) K) = A * compInd K I ∧ 4 ≤ I.card ∧
      Iᶜ.Nonempty := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨u₁, hu₁, u₂, hu₂, e₁, e₂, n₁, n₂, n₁₂, -⟩ := hd.klein
  obtain ⟨I, hI, hMO⟩ := exists_block_of_comp hK hw hd.le hd.perf J hfix hQc
  have hMI : M ≤ oIsoBlock K hw I := hMO.trans (oBlock_le_oIsoBlock hw I)
  have hcI : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → ∀ m ∈ M,
      (m : Matrix (Fin d) (Fin d) K) * compInd K I = compInd K I * m :=
    fun I hI m hm => (commute_compInd_of_commute_sign hK J I hI (hfix m hm)).symm
  have hcS : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → ∀ m ∈ M,
      (m : Matrix (Fin d) (Fin d) K) * signMat K I = signMat K I * m := by
    intro I hI m hm
    rw [signMat_eq, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, hcI I hI m hm,
      Matrix.mul_one, Matrix.one_mul]
  have hcompl : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → (Iᶜ = J ∨ Iᶜ = Jᶜ) := by
    rintro I (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (compl_compl _)
  have hIc := hcompl I hI
  have hIne : I.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJ
    · exact hJc
  have hIcne : Iᶜ.Nonempty := by
    rcases hIc with h | h <;> rw [h]
    · exact hJ
    · exact hJc
  have hsplit : ∀ v ∈ M,
      finrank K (negE ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
        finrank K ↥(negE ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ⊓
          negE (signMat K Iᶜ)) +
        finrank K ↥(negE ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ⊓
          negE (signMat K I)) := by
    intro v hv
    rw [← posE_signMat h2 I]
    refine finrank_split h2 (signMat_mul_self I) fun x hx => ?_
    rw [mem_negE] at hx ⊢
    rw [mulVec_mulVec, hcS I hI v hv, ← mulVec_mulVec, hx, mulVec_neg]
  have hnd : ∀ T : Finset (Fin d), ∀ v ∈ negE (signMat K T),
      (∀ x ∈ negE (signMat K T), v ⬝ᵥ diagonal w *ᵥ x = 0) → v = 0 :=
    fun T => nondeg_eig h2 (R := diagGL hw) (diagGL_transpose hw) (signMat_isometry w T)
      (signMat_mul_self T) (Or.inr rfl)
  have hinvA : ∀ T : Finset (Fin d), compInd K T * (A : Matrix (Fin d) (Fin d) K) =
      A * compInd K T → ∀ x ∈ negE (signMat K T),
        (A : Matrix (Fin d) (Fin d) K) *ᵥ x ∈ negE (signMat K T) := by
    intro T hT x hx
    rw [mem_negE_signMat h2, ← compInd_mulVec_eq_zero_iff] at hx ⊢
    rw [mulVec_mulVec, hT, ← mulVec_mulVec, hx, mulVec_zero]
  have hVc : ∀ x : Fin d → K, x ∈ negE (signMat K Iᶜ) ↔ ∀ i ∈ I, x i = 0 := by
    intro x
    rw [mem_negE_signMat h2]
    exact ⟨fun h i hi => h i (by simpa using hi), fun h i hi => h i (by simpa using hi)⟩
  have hAc : compInd K I * (A : Matrix (Fin d) (Fin d) K) = A * compInd K I := by
    rcases hAS with hAS | hAS
    · exact commute_compInd_of_commute_sign hK J I hI hAS
    · exfalso
      set c := compInd K I with hc
      have hXY : (A : Matrix (Fin d) (Fin d) K) * compInd K J + compInd K J * A = A := by
        have E := hAS
        rw [signMat_eq, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.one_mul] at E
        have h3 : (2 : K) • ((A : Matrix (Fin d) (Fin d) K) * compInd K J +
            compInd K J * A) = (2 : K) • (A : Matrix (Fin d) (Fin d) K) := by
          rw [smul_add, two_smul K (A : Matrix (Fin d) (Fin d) K), ← sub_eq_zero]
          calc (2 : K) • ((A : Matrix (Fin d) (Fin d) K) * compInd K J) +
                (2 : K) • (compInd K J * A) - (A + A) =
              (2 : K) • ((A : Matrix (Fin d) (Fin d) K) * compInd K J) - A -
                -((2 : K) • (compInd K J * A) - A) := by abel
            _ = 0 := sub_eq_zero.2 E
        exact smul_right_injective _ h2 h3
      have hAc' : (A : Matrix (Fin d) (Fin d) K) * c = (1 - c) * A := by
        rcases hI with rfl | rfl
        · rw [sub_mul, Matrix.one_mul]
          exact eq_sub_of_add_eq hXY
        · rw [hc, compInd_compl, mul_sub, Matrix.mul_one, sub_sub_cancel]
          exact (eq_sub_of_add_eq' hXY).symm
      have hX : ∀ X ∈ M, X = 1 := by
        intro X hX
        obtain ⟨-, -, hX2⟩ := hMI hX
        obtain ⟨-, -, hY2⟩ := hMI (hAM' X hX)
        set Am := (A : Matrix (Fin d) (Fin d) K) with hAm
        set Ai := ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hAi
        set Xm := (X : Matrix (Fin d) (Fin d) K) with hXm
        have hAAi : Am * Ai = 1 := by
          rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
        have hY2' : Ai * Xm * Am * c = c := by
          have := hY2
          simp only [Units.val_mul] at this
          exact this
        have e1 : Xm * (Am * c) = Am * c := by
          calc Xm * (Am * c) = Am * (Ai * Xm * Am * c) := by
                simp only [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
            _ = Am * c := by rw [hY2']
        rw [hAc'] at e1
        have e2 : Xm * (1 - c) = 1 - c := by
          have := congrArg (· * Ai) e1
          simp only [Matrix.mul_assoc, hAAi, Matrix.mul_one] at this
          exact this
        apply Units.ext
        change Xm = 1
        calc Xm = Xm * (1 - c) + Xm * c := by
              rw [← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
          _ = 1 := by rw [e2, hX2, sub_add_cancel]
      exact n₁ (hX u₁ hu₁)
  have hevI := even_finrank_of_skew (diagonal_transpose w) h2 hAR ha₀ hA2 (hnd I) (hinvA I hAc)
  rw [finrank_negE_signMat h2] at hevI
  refine ⟨I, hI, hMO, hAc, ?_, hIcne⟩
  have hpos := hIne.card_pos
  obtain ⟨k, hk⟩ := hevI
  by_contra h4
  have hc2 : I.card = 2 := by omega
  have hfull : ∀ v ∈ M, v * v = 1 → v ≠ 1 →
      negE (signMat K I) ≤ negE ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro v hv hvv hv1
    have hk' := hd.par v hv hvv hv1
    have hbot' : negE ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ⊓
        negE (signMat K Iᶜ) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      rw [mem_negE] at hx1
      have e := mulVec_eq_of_mem_oIsoBlock hw (hMI hv) ((hVc x).1 hx2)
      rw [hx1] at e
      rw [Submodule.mem_bot]
      have h2x : (2 : K) • x = 0 := by
        rw [two_smul]
        nth_rw 1 [← e]
        rw [neg_add_cancel]
      exact (smul_eq_zero.1 h2x).resolve_left h2
    have hsp' := hsplit v hv
    rw [hbot', finrank_bot, zero_add] at hsp'
    have hle' : finrank K ↥(negE ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ⊓
        negE (signMat K I)) ≤ 2 := by
      rw [← hc2, ← finrank_negE_signMat h2 I]
      exact Submodule.finrank_mono inf_le_right
    have heq2 : finrank K ↥(negE ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ⊓
        negE (signMat K I)) = finrank K (negE (signMat K I)) := by
      rw [finrank_negE_signMat h2, hc2]
      omega
    have := Submodule.eq_of_le_of_finrank_eq inf_le_right heq2
    rw [← this]
    exact inf_le_left
  apply n₁₂
  apply Units.ext
  ext i j
  have hcol : ∀ v ∈ M, v * v = 1 → v ≠ 1 →
      ((v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single j 1 =
        if j ∈ I then -(Pi.single j 1) else Pi.single j 1 := by
    intro v hv hvv hv1
    by_cases hj : j ∈ I
    · rw [ite_eq_left hj]
      have hx : (Pi.single j 1 : Fin d → K) ∈ negE (signMat K I) :=
        (mem_negE_signMat h2).2 fun i' hi' => by
          rw [Pi.single_apply, ite_eq_right (show i' ≠ j from fun h => hi' (h ▸ hj))]
      exact mem_negE.1 (hfull v hv hvv hv1 hx)
    · rw [ite_eq_right hj]
      exact mulVec_eq_of_mem_oIsoBlock hw (hMI hv) fun i' hi' => by
        rw [Pi.single_apply, ite_eq_right (show i' ≠ j from fun h => hj (h ▸ hi'))]
  have h1 := congrFun (hcol u₁ hu₁ e₁ n₁) i
  have h2' := congrFun (hcol u₂ hu₂ e₂ n₂) i
  rw [mulVec_single_one, Matrix.col_apply] at h1 h2'
  rw [h1, h2']

end CFSG.ComponentClassification.Burgoyne.DX.Dr
