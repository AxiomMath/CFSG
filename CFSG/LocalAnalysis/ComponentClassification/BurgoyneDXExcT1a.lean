module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcBlk
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcT3

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.C (blkL compInd_mul_self compInd_compl
  commute_compInd_of_commute_sign matrixDerived_le_isometryGroup)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat compInd compInd_apply
  signMat_mul_self signMat_eq commute_compInd_iff)

variable {K : Type} [Field K]

theorem mulVec_eq_of_mem_oIsoBlock {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {I : Finset (Fin d)} {g : GL (Fin d) K} (hg : g ∈ oIsoBlock K hw I) {x : Fin d → K}
    (hx : ∀ i ∈ I, x i = 0) : (g : Matrix (Fin d) (Fin d) K) *ᵥ x = x := by
  have hge := ((mem_oIsoBlock_iff hw).1 hg).2
  funext i
  rw [mulVec, dotProduct, Finset.sum_eq_single i]
  · by_cases hi : i ∈ I
    · rw [hx i hi, mul_zero]
    · rw [hge i i (Or.inl hi), ite_eq_left rfl, one_mul]
  · intro j _ hji
    by_cases hj : j ∈ I
    · rw [hx j hj, mul_zero]
    · rw [hge i j (Or.inr hj), ite_eq_right (Ne.symm hji), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem signMat_isometry {d : ℕ} (w : Fin d → K) (I : Finset (Fin d)) :
    (signMat K I)ᵀ * diagonal w * signMat K I = diagonal w := by
  rw [signMat, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext k
  split_ifs <;> ring

theorem exists_block_of_sign [Finite K] (hK : ringChar K ≠ 2) {w : Fin 8 → K}
    (hw : ∀ i, w i ≠ 0) {M : Subgroup (GL (Fin 8) K)} (hd : ExcData (diagGL hw) M)
    {J : Finset (Fin 8)} (hJ : J.Nonempty) (hJc : Jᶜ.Nonempty)
    (hfix : ∀ X ∈ M, X * signGL K J = signGL K J * X)
    {A : GL (Fin 8) K} {a₀ : K} (ha₀ : a₀ ≠ 0)
    (hA2 : (A : Matrix (Fin 8) (Fin 8) K) * A = a₀ • 1)
    (hAR : (A : Matrix (Fin 8) (Fin 8) K)ᵀ * diagonal w = -(diagonal w * A))
    (hAM' : ∀ X ∈ M, A⁻¹ * X * A ∈ M)
    (hAS : A * signGL K J = signGL K J * A ∨
      (A : Matrix (Fin 8) (Fin 8) K) * signMat K J = -(signMat K J * A)) :
    ∃ I : Finset (Fin 8), (I = J ∨ I = Jᶜ) ∧ M ≤ oBlock K hw I ∧
      compInd K I * (A : Matrix (Fin 8) (Fin 8) K) = A * compInd K I ∧
      (I.card = 4 ∨ I.card = 6) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨u₁, hu₁, u₂, hu₂, e₁, e₂, n₁, n₂, n₁₂, c₁₂⟩ := hd.klein
  have hu₃ : u₁ * u₂ ∈ M := mul_mem hu₁ hu₂
  have e₃ : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [c₁₂]
      _ = 1 := by rw [← mul_assoc, e₁, one_mul, e₂]
  have n₃ : u₁ * u₂ ≠ 1 := fun h =>
    n₁₂ ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right e₁)).symm
  have hk₁ := hd.par u₁ hu₁ e₁ n₁
  have hk₂ := hd.par u₂ hu₂ e₂ n₂
  have hk₃ := hd.par _ hu₃ e₃ n₃
  rw [Units.val_mul] at hk₃
  have hm₁ : (u₁ : Matrix (Fin 8) (Fin 8) K) * u₁ = 1 := by
    rw [← Units.val_mul, e₁, Units.val_one]
  have hm₂ : (u₂ : Matrix (Fin 8) (Fin 8) K) * u₂ = 1 := by
    rw [← Units.val_mul, e₂, Units.val_one]
  have hm₁₂ : (u₁ : Matrix (Fin 8) (Fin 8) K) * u₂ = u₂ * u₁ := by
    rw [← Units.val_mul, c₁₂, Units.val_mul]
  obtain ⟨u, hu, huu, hu1, hu2⟩ : ∃ u ∈ M, u * u = 1 ∧ u ≠ 1 ∧
      finrank K (negE ((u : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)) = 2 := by
    rcases exists_two_of_klein h2 le_rfl hm₁ hm₂ hm₁₂ hk₁ hk₂ hk₃ with h | h | h
    · exact ⟨u₁, hu₁, e₁, n₁, h⟩
    · exact ⟨u₂, hu₂, e₂, n₂, h⟩
    · exact ⟨u₁ * u₂, hu₃, e₃, n₃, by rw [Units.val_mul]; exact h⟩
  have hmu : (u : Matrix (Fin 8) (Fin 8) K) * u = 1 := by
    rw [← Units.val_mul, huu, Units.val_one]
  have hcI : ∀ I : Finset (Fin 8), (I = J ∨ I = Jᶜ) → ∀ m ∈ M,
      (m : Matrix (Fin 8) (Fin 8) K) * compInd K I = compInd K I * m :=
    fun I hI m hm => (commute_compInd_of_commute_sign hK J I hI (hfix m hm)).symm
  have hcS : ∀ I : Finset (Fin 8), (I = J ∨ I = Jᶜ) → ∀ m ∈ M,
      (m : Matrix (Fin 8) (Fin 8) K) * signMat K I = signMat K I * m := by
    intro I hI m hm
    rw [signMat_eq, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, hcI I hI m hm,
      Matrix.mul_one, Matrix.one_mul]
  have hiso : ∀ m ∈ M, m ∈ CatalogueBGraphForm.isometryGroup 8 K (diagGL hw) :=
    fun m hm => matrixDerived_le_isometryGroup hw h2 (hd.le hm)
  have hsplit : ∀ v ∈ M, ∀ I : Finset (Fin 8), (I = J ∨ I = Jᶜ) →
      finrank K (negE ((v : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)) =
        finrank K ↥(negE ((v : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ⊓
          negE (signMat K Iᶜ)) +
        finrank K ↥(negE ((v : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ⊓
          negE (signMat K I)) := by
    intro v hv I hI
    rw [← posE_signMat h2 I]
    refine finrank_split h2 (signMat_mul_self I) fun x hx => ?_
    rw [mem_negE] at hx ⊢
    rw [mulVec_mulVec, hcS I hI v hv, ← mulVec_mulVec, hx, mulVec_neg]
  have hcompl : ∀ I : Finset (Fin 8), (I = J ∨ I = Jᶜ) → (Iᶜ = J ∨ Iᶜ = Jᶜ) := by
    rintro I (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (compl_compl _)
  have hnd : ∀ T : Finset (Fin 8), ∀ v ∈ negE (signMat K T),
      (∀ x ∈ negE (signMat K T), v ⬝ᵥ diagonal w *ᵥ x = 0) → v = 0 :=
    fun T => nondeg_eig h2 (R := diagGL hw) (diagGL_transpose hw) (signMat_isometry w T)
      (signMat_mul_self T) (Or.inr rfl)
  have hinvA : ∀ T : Finset (Fin 8), compInd K T * (A : Matrix (Fin 8) (Fin 8) K) =
      A * compInd K T → ∀ x ∈ negE (signMat K T),
        (A : Matrix (Fin 8) (Fin 8) K) *ᵥ x ∈ negE (signMat K T) := by
    intro T hT x hx
    rw [mem_negE_signMat h2, ← compInd_mulVec_eq_zero_iff] at hx ⊢
    rw [mulVec_mulVec, hT, ← mulVec_mulVec, hx, mulVec_zero]
  have key : ∀ I : Finset (Fin 8), (I = J ∨ I = Jᶜ) →
      finrank K ↥(negE ((u : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ⊓
        negE (signMat K Iᶜ)) = 0 →
      ∃ I : Finset (Fin 8), (I = J ∨ I = Jᶜ) ∧ M ≤ oBlock K hw I ∧
        compInd K I * (A : Matrix (Fin 8) (Fin 8) K) = A * compInd K I ∧
        (I.card = 4 ∨ I.card = 6) := by
    intro I hI h0
    have hIc := hcompl I hI
    have hbot := Submodule.finrank_eq_zero.1 h0
    have hVc : ∀ x : Fin 8 → K, x ∈ negE (signMat K Iᶜ) ↔ ∀ i ∈ I, x i = 0 := by
      intro x
      rw [mem_negE_signMat h2]
      exact ⟨fun h i hi => h i (by simpa using hi), fun h i hi => h i (by simpa using hi)⟩
    have hu_triv : ∀ x : Fin 8 → K, (∀ i ∈ I, x i = 0) →
        (u : Matrix (Fin 8) (Fin 8) K) *ᵥ x = x := by
      intro x hx
      have hxV : x ∈ negE (signMat K Iᶜ) := (hVc x).2 hx
      have huxV : (u : Matrix (Fin 8) (Fin 8) K) *ᵥ x ∈ negE (signMat K Iᶜ) := by
        rw [mem_negE] at hxV ⊢
        rw [mulVec_mulVec, ← hcS Iᶜ hIc u hu, ← mulVec_mulVec, hxV, mulVec_neg]
      have hz : x - (u : Matrix (Fin 8) (Fin 8) K) *ᵥ x ∈
          negE ((u : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ⊓ negE (signMat K Iᶜ) := by
        refine Submodule.mem_inf.2 ⟨mem_negE.2 ?_, Submodule.sub_mem _ hxV huxV⟩
        rw [mulVec_sub, mulVec_mulVec, hmu, one_mulVec, neg_sub]
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at hz
      exact hz.symm
    have hblk_u := (commute_compInd_iff I (u : Matrix (Fin 8) (Fin 8) K)).1 (hcI I hI u hu).symm
    have huI : u ∈ oIsoBlock K hw I := by
      rw [mem_oIsoBlock_iff]
      refine ⟨hiso u hu, fun i j hij => ?_⟩
      by_cases hj : j ∈ I
      · have hi : i ∉ I := hij.resolve_right (not_not.2 hj)
        rw [hblk_u i j (by simp [hi, hj]), ite_eq_right (show i ≠ j from fun h => hi (h ▸ hj))]
      · have e := congrFun (hu_triv (Pi.single j 1) fun i' hi' => by
          rw [Pi.single_apply, ite_eq_right (show i' ≠ j from fun h => hj (h ▸ hi'))]) i
        rw [mulVec_single_one, Matrix.col_apply, Pi.single_apply] at e
        exact e
    have hN : M ⊓ oIsoBlock K hw I = M := by
      refine hd.normal _ inf_le_left ⟨fun a ha b => ?_⟩ ⟨u, Subgroup.mem_inf.2 ⟨hu, huI⟩, huu, hu1⟩
      rw [mem_subgroupOf] at ha ⊢
      obtain ⟨haM, haI⟩ := Subgroup.mem_inf.1 ha
      change (b : GL (Fin 8) K) * a * (b : GL (Fin 8) K)⁻¹ ∈ M ⊓ oIsoBlock K hw I
      exact Subgroup.mem_inf.2 ⟨M.mul_mem (M.mul_mem b.2 haM) (M.inv_mem b.2),
        conj_mem_oIsoBlock hw (hiso b b.2) (hcI I hI b b.2).symm haI⟩
    have hMI : M ≤ oIsoBlock K hw I := by
      intro m hm
      have : m ∈ M ⊓ oIsoBlock K hw I := by rw [hN]; exact hm
      exact (Subgroup.mem_inf.1 this).2
    have hMO : M ≤ oBlock K hw I := by
      rw [← hd.perf]
      exact commutator_mono hMI hMI
    have hAc : compInd K I * (A : Matrix (Fin 8) (Fin 8) K) = A * compInd K I := by
      rcases hAS with hAS | hAS
      · exact commute_compInd_of_commute_sign hK J I hI hAS
      · exfalso
        set c := compInd K I with hc
        have hXY : (A : Matrix (Fin 8) (Fin 8) K) * compInd K J + compInd K J * A = A := by
          have E := hAS
          rw [signMat_eq, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
            Matrix.one_mul] at E
          have h3 : (2 : K) • ((A : Matrix (Fin 8) (Fin 8) K) * compInd K J +
              compInd K J * A) = (2 : K) • (A : Matrix (Fin 8) (Fin 8) K) := by
            rw [smul_add, two_smul K (A : Matrix (Fin 8) (Fin 8) K), ← sub_eq_zero]
            calc (2 : K) • ((A : Matrix (Fin 8) (Fin 8) K) * compInd K J) +
                  (2 : K) • (compInd K J * A) - (A + A) =
                (2 : K) • ((A : Matrix (Fin 8) (Fin 8) K) * compInd K J) - A -
                  -((2 : K) • (compInd K J * A) - A) := by abel
              _ = 0 := sub_eq_zero.2 E
          exact smul_right_injective _ h2 h3
        have hAc' : (A : Matrix (Fin 8) (Fin 8) K) * c = (1 - c) * A := by
          rcases hI with rfl | rfl
          · rw [sub_mul, Matrix.one_mul]
            exact eq_sub_of_add_eq hXY
          · rw [hc, compInd_compl, mul_sub, Matrix.mul_one, sub_sub_cancel]
            exact (eq_sub_of_add_eq' hXY).symm
        have hX : ∀ X ∈ M, X = 1 := by
          intro X hX
          obtain ⟨-, -, hX2⟩ := hMI hX
          obtain ⟨-, -, hY2⟩ := hMI (hAM' X hX)
          set Am := (A : Matrix (Fin 8) (Fin 8) K) with hAm
          set Ai := ((A⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) with hAi
          set Xm := (X : Matrix (Fin 8) (Fin 8) K) with hXm
          have hAAi : Am * Ai = 1 := by
            rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
          have hAiA : Ai * Am = 1 := by
            rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
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
    have hAcc : compInd K Iᶜ * (A : Matrix (Fin 8) (Fin 8) K) = A * compInd K Iᶜ := by
      rw [compInd_compl, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hAc]
    have hevI := even_finrank_of_skew (diagonal_transpose w) h2 hAR ha₀ hA2 (hnd I) (hinvA I hAc)
    have hevIc := even_finrank_of_skew (diagonal_transpose w) h2 hAR ha₀ hA2 (hnd Iᶜ)
      (hinvA Iᶜ hAcc)
    rw [finrank_negE_signMat h2] at hevI hevIc
    have hcard : I.card + Iᶜ.card = 8 := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_univ I
      rw [Fintype.card_fin] at this
      omega
    have hIcne : Iᶜ.Nonempty := by
      rcases hIc with h | h <;> rw [h]
      · exact hJ
      · exact hJc
    have hIc1 := hIcne.card_pos
    have hsp := hsplit u hu I hI
    rw [h0, zero_add, hu2] at hsp
    have hle : finrank K ↥(negE ((u : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ⊓
        negE (signMat K I)) ≤ I.card := by
      rw [← finrank_negE_signMat h2 I]
      exact Submodule.finrank_mono inf_le_right
    obtain ⟨k₁, hk₁'⟩ := hevI
    obtain ⟨k₂, hk₂'⟩ := hevIc
    have hcases : I.card = 2 ∨ I.card = 4 ∨ I.card = 6 := by omega
    rcases hcases with hc2 | hc4 | hc6
    ·
      exfalso
      have hfull : ∀ v ∈ M, v * v = 1 → v ≠ 1 →
          negE (signMat K I) ≤ negE ((v : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) := by
        intro v hv hvv hv1
        have hk := hd.par v hv hvv hv1
        have hbot' : negE ((v : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ⊓
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
        have hsp' := hsplit v hv I hI
        rw [hbot', finrank_bot, zero_add] at hsp'
        have hle' : finrank K ↥(negE ((v : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ⊓
            negE (signMat K I)) ≤ 2 := by
          rw [← hc2, ← finrank_negE_signMat h2 I]
          exact Submodule.finrank_mono inf_le_right
        have heq2 : finrank K ↥(negE ((v : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ⊓
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
          ((v : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) *ᵥ Pi.single j 1 =
            if j ∈ I then -(Pi.single j 1) else Pi.single j 1 := by
        intro v hv hvv hv1
        by_cases hj : j ∈ I
        · rw [ite_eq_left hj]
          have hx : (Pi.single j 1 : Fin 8 → K) ∈ negE (signMat K I) :=
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
    · exact ⟨I, hI, hMO, hAc, Or.inl hc4⟩
    · exact ⟨I, hI, hMO, hAc, Or.inr hc6⟩
  have hsJ := hsplit u hu J (Or.inl rfl)
  rw [hu2] at hsJ
  have hevJ := even_finrank_negE_inf h2 hd.perf (hcI J (Or.inl rfl)) hu huu
  have hevJc := even_finrank_negE_inf h2 hd.perf (hcI Jᶜ (Or.inr rfl)) hu huu
  obtain ⟨a, ha⟩ := hevJ
  obtain ⟨b, hb⟩ := hevJc
  by_cases hb0 : b = 0
  · exact key J (Or.inl rfl) (by rw [hb, hb0])
  · refine key Jᶜ (Or.inr rfl) ?_
    rw [compl_compl, ha]
    omega

end CFSG.ComponentClassification.Burgoyne.DX
