module

public import CFSG.ClassicalGroups.Orthogonal.SiegelSLAxis
import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Dim4

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelSL

open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.HardMathSupport.Kantor79 CFSG.CGT.Timmesfeld75
open CFSG.CGT.T75E QuadraticMap Module Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m' : ℕ} {Qf : QuadraticForm K V} {ρ : SL(m' + 2, K) →* (V ≃ₗ[K] V)}

omit [Finite K] in
theorem SLSetting.isStar_of_forall_le (hs : SLSetting Qf ρ) {P : Submodule K V}
    (hP1 : finrank K P = 1)
    (hP : ∀ (γ : Fin (m' + 2) → K) (h : γ ⬝ᵥ (Pi.single (0 : Fin (m' + 2)) (1 : K)) = 0),
      (∃ j : Fin (m' + 2), j ≠ 0 ∧ ∃ μ : K, μ ≠ 0 ∧ γ = μ • Pi.single j 1) →
        P ≤ movedSpace (ρ (tvSL (Pi.single (0 : Fin (m' + 2)) (1 : K)) γ h))) :
    IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ) := by
  set e₀ : Fin (m' + 2) → K := Pi.single 0 1 with he₀def
  set E := (tvCenterSL e₀).map ρ with hEdef
  have hE := hs.isSiegelGroup_center e₀
  have hWs := hE.qf_eq_zero_of_mem_commutatorSpace hs.nondeg
  have h1 : (1 : Fin (m' + 2)) ≠ 0 := by simp
  have hγ1 : (Pi.single (1 : Fin (m' + 2)) (1 : K)) ⬝ᵥ e₀ = 0 := by
    simp [he₀def, dotProduct_single]
  have hPW : P ≤ commutatorSpace E := by
    refine (hP _ hγ1 ⟨1, h1, 1, one_ne_zero, (one_smul K _).symm⟩).trans ?_
    exact movedSpace_le_commutatorSpace ⟨_, ⟨_, hγ1, rfl⟩, rfl⟩
  have hH : tvCenterSL e₀ ≤ (piGroup Qf P (commutatorSpace E)).comap ρ := by
    refine tvCenterSL_single_zero_le _ fun γ h ⟨j, hj, μ, hγ⟩ => ?_
    by_cases hμ : μ = 0
    · have hγ0 : γ = 0 := by rw [hγ, hμ, zero_smul]
      subst hγ0
      have : tvSL e₀ (0 : Fin (m' + 2) → K) h = 1 := Subtype.ext (by simp [coe_tvSL])
      rw [Subgroup.mem_comap, this, map_one]
      exact one_mem _
    · have hγne : γ ≠ 0 := fun h0 => by
        rw [h0] at hγ
        have := congrFun hγ j
        simp at this
        exact hμ this.symm
      have he₀ne : e₀ ≠ 0 := fun h0 => by simpa [he₀def] using congrFun h0 0
      exact isLongRootElement_mem_piGroup (hs.siegel _ _ h he₀ne hγne)
        (hP γ h ⟨j, hj, μ, hμ, hγ⟩) (movedSpace_le_commutatorSpace ⟨_, ⟨γ, h, rfl⟩, rfl⟩)
  refine ⟨P, hP1, ?_⟩
  rintro A ⟨s, ⟨x, hx, rfl⟩, hs1, rfl⟩
  exact ((mem_piGroup_iff_of_ne_one hs.nondeg hWs hP1 hPW hs1).mp (hH hx)).2.1

omit [CharP K 2] [Finite K] in
private theorem exists_point_le_of_finrank_eq_three {W A₁ A₂ : Submodule K V}
    (h3 : finrank K W = 3) (h₁ : finrank K A₁ = 2) (h₂ : finrank K A₂ = 2) (hA₁ : A₁ ≤ W)
    (hA₂ : A₂ ≤ W) : ∃ P : Submodule K V, finrank K P = 1 ∧ P ≤ A₁ ∧ P ≤ A₂ := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A₁ A₂
  have hle := Submodule.finrank_mono (sup_le hA₁ hA₂)
  have hne : A₁ ⊓ A₂ ≠ ⊥ := fun hb => by
    rw [hb, finrank_bot] at hsum
    omega
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨K ∙ p, finrank_span_singleton hp0,
    (Submodule.span_singleton_le_iff_mem p _).mpr (Submodule.mem_inf.mp hp).1,
    (Submodule.span_singleton_le_iff_mem p _).mpr (Submodule.mem_inf.mp hp).2⟩

omit [Finite K] [FiniteDimensional K V] in
private theorem SLSetting.axis_single (hs : SLSetting Qf ρ) (j : Fin (m' + 2))
    (h : (Pi.single j (1 : K) : Fin (m' + 2) → K) ⬝ᵥ Pi.single 0 1 = 0) :
    finrank K (movedSpace (ρ (tvSL (Pi.single (0 : Fin (m' + 2)) (1 : K)) (Pi.single j 1) h))) =
      2 ∧ movedSpace (ρ (tvSL (Pi.single (0 : Fin (m' + 2)) (1 : K)) (Pi.single j 1) h)) ≤
        commutatorSpace ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ) := by
  have he₀ : (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) ≠ 0 := fun h0 => by
    simpa using congrFun h0 0
  have hej : (Pi.single j (1 : K) : Fin (m' + 2) → K) ≠ 0 := fun h0 => by
    simpa using congrFun h0 j
  exact ⟨(hs.siegel _ _ h he₀ hej).finrank_movedSpace hs.nondeg,
    movedSpace_le_commutatorSpace (Subgroup.mem_map_of_mem ρ ⟨_, h, rfl⟩)⟩

private theorem SLSetting.isStar_of_forall_le_single (hs : SLSetting Qf ρ) {P : Submodule K V}
    (hP1 : finrank K P = 1)
    (hP : ∀ j : Fin (m' + 2), j ≠ 0 →
      ∀ h : (Pi.single j (1 : K) : Fin (m' + 2) → K) ⬝ᵥ Pi.single 0 1 = 0,
        P ≤ movedSpace (ρ (tvSL (Pi.single (0 : Fin (m' + 2)) (1 : K)) (Pi.single j 1) h))) :
    IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ) := by
  refine hs.isStar_of_forall_le hP1 fun γ h ⟨j, hj, μ, hμ, hγ⟩ => ?_
  subst hγ
  have hj' : (Pi.single j (1 : K) : Fin (m' + 2) → K) ⬝ᵥ Pi.single 0 1 = 0 := by
    simp [dotProduct_single, hj]
  have he₀ : (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) ≠ 0 := fun h0 => by
    simpa using congrFun h0 0
  have hej : (Pi.single j (1 : K) : Fin (m' + 2) → K) ≠ 0 := fun h0 => by
    simpa using congrFun h0 j
  rw [hs.movedSpace_tvSL_smul_eq he₀ hej hj' hμ]
  exact hP j hj hj'

theorem SLSetting.finrank_commutatorSpace_center_eq_three (hs : SLSetting Qf ρ)
    (hst : ¬ IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)) :
    finrank K (commutatorSpace ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)) =
      3 ∧ m' + 2 ≤ 4 := by
  set e₀ : Fin (m' + 2) → K := Pi.single 0 1 with he₀def
  have he₀ : e₀ ≠ 0 := fun h0 => by simpa [he₀def] using congrFun h0 0
  have hE := hs.isSiegelGroup_center e₀
  have hcard := hs.card_map_center he₀
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hm := hs.three_le
  have hlt : Nat.card K < Nat.card ((tvCenterSL e₀).map ρ) := by
    rw [hcard]
    calc Nat.card K = Nat.card K ^ 1 := (pow_one _).symm
      _ < Nat.card K ^ (m' + 2 - 1) := Nat.pow_lt_pow_right hq (by omega)
  obtain ⟨A₁, hA₁, -, -, -⟩ := hE.exists_ne_axes hs.nondeg hlt
  have h3 := hE.finrank_commutatorSpace_eq_three hs.nondeg ⟨A₁, hA₁⟩ hst
  refine ⟨h3, ?_⟩
  have hsig := natCard_sigmaGroup hs.nondeg (hE.qf_eq_zero_of_mem_commutatorSpace hs.nondeg) h3
  have hfin : Finite (sigmaGroup Qf (commutatorSpace ((tvCenterSL e₀).map ρ))) :=
    Nat.finite_of_card_ne_zero (by rw [hsig]; exact pow_ne_zero _ (by omega))
  have hle := Subgroup.card_le_of_le hE.le_sigmaGroup
  rw [hcard, hsig] at hle
  have := (pow_le_pow_iff_right₀ hq).mp hle
  omega

theorem SLSetting.finrank_eq_six_of_not_isStar (hs : SLSetting Qf ρ)
    (hV : commutatorSpace ρ.range = ⊤)
    (hst : ¬ IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)) :
    finrank K V = 6 := by
  set e₀ : Fin (m' + 2) → K := Pi.single 0 1 with he₀def
  have h3 : finrank K (commutatorSpace ((tvCenterSL e₀).map ρ)) = 3 :=
    (hs.finrank_commutatorSpace_center_eq_three hst).1
  have hE := hs.isSiegelGroup_center e₀
  have hE' := hs.isSiegelGroup_axis e₀
  have htop : commutatorSpace ((tvCenterSL e₀).map ρ) ⊔ commutatorSpace ((tvAxisSL e₀).map ρ) =
      ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hV]
    refine commutatorSpace_range_le ρ (S := (tvCenterSL e₀ : Set _) ∪ tvAxisSL e₀) ?_ ?_
    · rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      exact tvCenterSL_sup_tvAxisSL_single_zero m'
    · rintro x (hx | hx)
      · exact (movedSpace_le_commutatorSpace (Subgroup.mem_map_of_mem ρ hx)).trans le_sup_left
      · exact (movedSpace_le_commutatorSpace (Subgroup.mem_map_of_mem ρ hx)).trans le_sup_right
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (commutatorSpace ((tvCenterSL e₀).map ρ))
    (commutatorSpace ((tvAxisSL e₀).map ρ))
  rw [htop, finrank_top] at hsum
  have h1 := two_mul_finrank_le_of_totallySingular hs.nondeg
    (hE.qf_eq_zero_of_mem_commutatorSpace hs.nondeg)
  have h2 := two_mul_finrank_le_of_totallySingular hs.nondeg
    (hE'.qf_eq_zero_of_mem_commutatorSpace hs.nondeg)
  omega

theorem SLSetting.ne_one_of_not_isStar (hs : SLSetting Qf ρ)
    (hst : ¬ IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)) :
    m' ≠ 1 := by
  rintro rfl
  obtain ⟨h3, -⟩ := hs.finrank_commutatorSpace_center_eq_three hst
  have hdot : ∀ j : Fin (1 + 2), j ≠ 0 →
      (Pi.single j (1 : K) : Fin (1 + 2) → K) ⬝ᵥ Pi.single 0 1 = 0 :=
    fun j hj => by simp [dotProduct_single, hj]
  obtain ⟨f₁, l₁⟩ := hs.axis_single 1 (hdot 1 (by decide))
  obtain ⟨f₂, l₂⟩ := hs.axis_single 2 (hdot 2 (by decide))
  obtain ⟨P, hP1, hP₁, hP₂⟩ := exists_point_le_of_finrank_eq_three h3 f₁ f₂ l₁ l₂
  refine hst (hs.isStar_of_forall_le_single hP1 fun j hj h => ?_)
  rcases (by decide : ∀ j : Fin (1 + 2), j ≠ 0 → j = 1 ∨ j = 2) j hj with rfl | rfl
  · exact hP₁
  · exact hP₂

theorem SLSetting.exists_config_of_not_isStar {ρ : SL(2 + 2, K) →* (V ≃ₗ[K] V)}
    (hs : SLSetting Qf ρ)
    (hst : ¬ IsStar ((tvCenterSL (Pi.single (0 : Fin (2 + 2)) (1 : K))).map ρ)) :
    ∃ (c₁ a₁ c₂ a₂ : Fin (2 + 2) → K) (h₁ : a₁ ⬝ᵥ c₁ = 0) (h₂ : a₂ ⬝ᵥ c₂ = 0),
      c₁ ≠ 0 ∧ a₁ ≠ 0 ∧ c₂ ≠ 0 ∧ a₂ ≠ 0 ∧
      tvSL c₁ a₁ h₁ * tvSL c₂ a₂ h₂ = tvSL c₂ a₂ h₂ * tvSL c₁ a₁ h₁ ∧
      finrank K ↥(movedSpace (ρ (tvSL c₁ a₁ h₁)) ⊓ movedSpace (ρ (tvSL c₂ a₂ h₂))) = 1 ∧
      ¬ movedSpace (ρ (tvSL c₁ a₁ h₁)) ≤
        LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace (ρ (tvSL c₂ a₂ h₂))) := by
  have hd : ∀ i j : Fin (2 + 2), i ≠ j →
      (Pi.single i (1 : K) : Fin (2 + 2) → K) ⬝ᵥ Pi.single j 1 = 0 :=
    fun i j hij => by simp [dotProduct_single, hij.symm]
  have hne : ∀ i : Fin (2 + 2), (Pi.single i (1 : K) : Fin (2 + 2) → K) ≠ 0 := fun i h0 => by
    simpa using congrFun h0 i
  have h01 := hd 1 0 (by decide)
  have h02 := hd 2 0 (by decide)
  have h03 := hd 3 0 (by decide)
  have h13 := hd 3 1 (by decide)
  obtain ⟨h3, -⟩ := hs.finrank_commutatorSpace_center_eq_three hst
  obtain ⟨f₁, l₁⟩ := hs.axis_single 1 h01
  obtain ⟨f₂, l₂⟩ := hs.axis_single 2 h02
  obtain ⟨f₃, l₃⟩ := hs.axis_single 3 h03
  have hsy := hs.siegel _ _ h13 (hne 1) (hne 3)
  have hne23 : movedSpace (ρ (tvSL _ _ h02)) ≠ movedSpace (ρ (tvSL _ _ h03)) := by
    intro heq
    obtain ⟨P, hP1, hP₁, hP₂⟩ := exists_point_le_of_finrank_eq_three h3 f₁ f₂ l₁ l₂
    refine hst (hs.isStar_of_forall_le_single hP1 fun j hj h => ?_)
    rcases (by decide : ∀ j : Fin (2 + 2), j ≠ 0 → j = 1 ∨ j = 2 ∨ j = 3) j hj with
      rfl | rfl | rfl
    · exact hP₁
    · exact hP₂
    · exact hP₂.trans heq.le
  have hsup : movedSpace (ρ (tvSL _ _ h02)) ⊔ movedSpace (ρ (tvSL _ _ h03)) =
      commutatorSpace ((tvCenterSL (Pi.single (0 : Fin (2 + 2)) (1 : K))).map ρ) := by
    refine Submodule.eq_of_le_of_finrank_le (sup_le l₂ l₃) ?_
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (movedSpace (ρ (tvSL _ _ h02)))
      (movedSpace (ρ (tvSL _ _ h03)))
    have hle := Submodule.finrank_mono
      (inf_le_left : movedSpace (ρ (tvSL _ _ h02)) ⊓ movedSpace (ρ (tvSL _ _ h03)) ≤ _)
    have hinf : finrank K ↥(movedSpace (ρ (tvSL _ _ h02)) ⊓ movedSpace (ρ (tvSL _ _ h03))) ≠
        2 := fun h2 => hne23 <|
      (Submodule.eq_of_le_of_finrank_le inf_le_left (f₂.trans h2.symm).le).symm.trans
        (Submodule.eq_of_le_of_finrank_le inf_le_right (f₃.trans h2.symm).le)
    omega
  have hWα := (hs.isSiegelGroup_axis
    (Pi.single (3 : Fin (2 + 2)) (1 : K))).qf_eq_zero_of_mem_commutatorSpace hs.nondeg
  have m03 : movedSpace (ρ (tvSL _ _ h03)) ≤
      commutatorSpace ((tvAxisSL (Pi.single (3 : Fin (2 + 2)) (1 : K))).map ρ) :=
    movedSpace_le_commutatorSpace (Subgroup.mem_map_of_mem ρ ⟨_, h03, rfl⟩)
  have m13 : movedSpace (ρ (tvSL _ _ h13)) ≤
      commutatorSpace ((tvAxisSL (Pi.single (3 : Fin (2 + 2)) (1 : K))).map ρ) :=
    movedSpace_le_commutatorSpace (Subgroup.mem_map_of_mem ρ ⟨_, h13, rfl⟩)
  have hy3 : movedSpace (ρ (tvSL _ _ h03)) ≤
      LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace (ρ (tvSL _ _ h13))) :=
    fun x hx => mem_orthogonal_iff_polar.mpr fun y hy =>
      polar_eq_zero_of_totallySingular hWα (m13 hy) (m03 hx)
  have hP5 := (hs.not_commute_of_dot h01 h13 h03 (by simp [dotProduct_single]) (hne 0)
    (hne 3)).2.2
  have hno : ¬ movedSpace (ρ (tvSL _ _ h02)) ≤
      LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace (ρ (tvSL _ _ h13))) := by
    intro h2
    have hW := hsup ▸ sup_le h2 hy3
    refine hP5 fun x hx y hy => ?_
    rw [QuadraticMap.polar_comm]
    exact mem_orthogonal_iff_polar.mp (hW (l₁ hx)) y hy
  have hcomm : tvSL _ _ h02 * tvSL _ _ h13 = tvSL _ _ h13 * tvSL _ _ h02 := by
    have hAB : vecMulVec (Pi.single (0 : Fin (2 + 2)) (1 : K)) (Pi.single (2 : Fin (2 + 2)) 1) *
        vecMulVec (Pi.single (1 : Fin (2 + 2)) (1 : K)) (Pi.single (3 : Fin (2 + 2)) 1) = 0 := by
      rw [vecMulVec_mul_vecMulVec, hd 2 1 (by decide), zero_smul, vecMulVec_zero]
    have hBA : vecMulVec (Pi.single (1 : Fin (2 + 2)) (1 : K)) (Pi.single (3 : Fin (2 + 2)) 1) *
        vecMulVec (Pi.single (0 : Fin (2 + 2)) (1 : K)) (Pi.single (2 : Fin (2 + 2)) 1) = 0 := by
      rw [vecMulVec_mul_vecMulVec, h03, zero_smul, vecMulVec_zero]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hAB, hBA]
    abel
  have hmeet := (movedSpace_le_orthogonal_or_inf_ne_bot_of_commute
    (hs.siegel _ _ h02 (hne 0) (hne 2)) hsy (by rw [← map_mul, hcomm, map_mul])).resolve_left hno
  have hfin : finrank K ↥(movedSpace (ρ (tvSL _ _ h02)) ⊓ movedSpace (ρ (tvSL _ _ h13))) = 1 := by
    have h0 : finrank K ↥(movedSpace (ρ (tvSL _ _ h02)) ⊓ movedSpace (ρ (tvSL _ _ h13))) ≠ 0 :=
      fun h => hmeet (Submodule.finrank_eq_zero.mp h)
    have h2 : finrank K ↥(movedSpace (ρ (tvSL _ _ h02)) ⊓ movedSpace (ρ (tvSL _ _ h13))) ≠ 2 :=
      fun h2 => hno ((inf_eq_left.mp (Submodule.eq_of_le_of_finrank_le inf_le_left
        (f₂.trans h2.symm).le)).trans
          (le_orthogonal_of_totallySingular fun _ hw => hsy.qf_eq_zero_of_mem_movedSpace hw))
    have hle := Submodule.finrank_mono
      (inf_le_left : movedSpace (ρ (tvSL _ _ h02)) ⊓ movedSpace (ρ (tvSL _ _ h13)) ≤ _)
    omega
  exact ⟨_, _, _, _, h02, h13, hne 0, hne 2, hne 1, hne 3, hcomm, hfin, hno⟩

end CFSG.ClassicalGroups.Orthogonal.SiegelSL
