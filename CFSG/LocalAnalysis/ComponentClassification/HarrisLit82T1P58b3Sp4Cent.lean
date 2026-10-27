module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Sp4Key
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelfNormal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSp4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff
  lam coe_lam pairMat sl2Diag coe_sl2Diag)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  exists_bilin_split_equiv eigen_ne_bot isCompl_ker_sub_one_ker_add_one invSMulOp_mul_self)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped MatrixGroups

namespace P58b3

variable {F : Type} [Field F]

theorem finrank_VMl_eq_two (hF : ringChar F ≠ 2) {A : gsp 2 F}
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = ((1 : F) ^ 2) • 1)
    (hJ : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      formJ 2 F * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((1 : F) ^ 2) • formJ 2 F)
    (hAns : ∀ c : Fˣ, (A : GL (Fin 2 ⊕ Fin 2) F) ≠ GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c) :
    Module.finrank F (VMl A 1) = 2 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hAA' := linA_mul_self hAA
  have hTB : ∀ v w, pairedSympForm F 2 (invSMulOp 1 ((linA A :
      LinearMap.GeneralLinearGroup F (Fin 2 ⊕ Fin 2 → F)) : Module.End F (Fin 2 ⊕ Fin 2 → F)) v)
      (invSMulOp 1 ((linA A : LinearMap.GeneralLinearGroup F (Fin 2 ⊕ Fin 2 → F)) :
        Module.End F (Fin 2 ⊕ Fin 2 → F)) w) = pairedSympForm F 2 v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  have hAns' : ∀ c : F, ((linA A : LinearMap.GeneralLinearGroup F (Fin 2 ⊕ Fin 2 → F)) :
      Module.End F (Fin 2 ⊕ Fin 2 → F)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  obtain ⟨hPne, hMne⟩ := eigen_ne_bot h2 one_ne_zero hAA' hAns'
  obtain ⟨-, haltP, haltM, hndP, hndM, -⟩ := exists_bilin_split_equiv h2 pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate one_ne_zero hAA' hTB
  have hc := isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self one_ne_zero hAA')
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hV : Module.finrank F (Fin 2 ⊕ Fin 2 → F) = 4 := by simp
  have heP := CatalogueBAlternatingIsometry.even_finrank _ haltP hndP
  have heM := CatalogueBAlternatingIsometry.even_finrank _ haltM hndM
  have hP0 : Module.finrank F (VPl A 1) ≠ 0 := fun h => hPne (Submodule.finrank_eq_zero.mp h)
  have hM0 : Module.finrank F (VMl A 1) ≠ 0 := fun h => hMne (Submodule.finrank_eq_zero.mp h)
  change Module.finrank F (VPl A 1) + Module.finrank F (VMl A 1) = _ at hsum
  rw [hV] at hsum
  obtain ⟨a, ha⟩ := heP
  obtain ⟨b, hb⟩ := heM
  change Module.finrank F (VPl A 1) = a + a at ha
  change Module.finrank F (VMl A 1) = b + b at hb
  omega

theorem exists_conj_lrInv (hF : ringChar F ≠ 2) {g : StatedSp 2 F} (hgg : g * g = 1)
    (hns : ∀ c : Fˣ, (g : GL (Fin 2 ⊕ Fin 2) F) ≠ GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c) :
    ∃ H : StatedSp 2 F, H⁻¹ * g * H = lrInv F 0 := by
  set A : gsp 2 F := ⟨(g : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp g.2⟩ with hA
  have hAA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((1 : F) ^ 2) • 1 := by
    have h := congrArg
      (fun x : StatedSp 2 F => ((x : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hgg
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at h
    rw [one_pow, one_smul]
    exact h
  have hJ : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      formJ 2 F * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((1 : F) ^ 2) • formJ 2 F := by
    rw [one_pow, one_smul]
    exact mem_statedSp_iff.1 g.2
  obtain ⟨H, hH⟩ := exists_split_self_lrInv_normal_form (A := A) (l := 1) hF (by norm_num)
    one_ne_zero hAA hJ (finrank_VMl_eq_two hF hAA hJ hns)
  rw [one_smul] at hH
  refine ⟨H, statedSp_ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  exact hH

theorem det_pairBlock_of_blockDiag {r : ℕ} (i₀ : Fin r)
    {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F} (hM : BlockDiag (lrPair i₀) M)
    (hJ : Mᵀ * formJ r F * M = formJ r F) :
    (pairBlock (Sum.inl i₀) (Sum.inr i₀) M).det = 1 := by
  have h0 := blockDiag_iff.1 hM
  have hab : (Sum.inl i₀ : Fin r ⊕ Fin r) ≠ Sum.inr i₀ := Sum.inl_ne_inr
  have hcol : ∀ y ∈ lrPair i₀, ∀ z, z ∉ lrPair i₀ → M z y = 0 := fun y hy z hz =>
    h0 z y (iff_of_false hz (not_not.mpr hy))
  have hrow : ∀ y, (Mᵀ * formJ r F) (Sum.inl i₀) y =
      M (Sum.inl i₀) (Sum.inl i₀) * formJ r F (Sum.inl i₀) y +
        M (Sum.inr i₀) (Sum.inl i₀) * formJ r F (Sum.inr i₀) y := by
    intro y
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_add _ _ hab (fun z _ hz => ?_) (by simp) (by simp)
    rw [transpose_apply, hcol _ (by simp) z (by simp [hz.1, hz.2]), zero_mul]
  have hJab := congrFun (congrFun hJ (Sum.inl i₀)) (Sum.inr i₀)
  rw [Matrix.mul_apply, Finset.sum_eq_add (Sum.inl i₀) (Sum.inr i₀) hab (fun w _ hw => by
      rw [hcol _ (by simp) w (by simp [hw.1, hw.2]), mul_zero]) (by simp) (by simp),
    hrow, hrow] at hJab
  simp [formJ, pairBlock, det_fin_two_of] at hJab ⊢
  linear_combination hJab

theorem mem_lrPair_one_iff (x : Fin 2 ⊕ Fin 2) : x ∈ lrPair (1 : Fin 2) ↔ x ∉ lrPair 0 := by
  rcases x with x | x <;> fin_cases x <;> simp [lrPair]

theorem exists_lam_mul_lam (h2 : (2 : F) ≠ 0) {h : StatedSp 2 F}
    (hh : h * lrInv F 0 = lrInv F 0 * h) : ∃ A B : SL(2, F), h = lam 0 A * lam 1 B := by
  set M := ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hM
  have hMu : M * (((lrInv F (0 : Fin 2) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (((lrInv F (0 : Fin 2) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * M := by
    have := congrArg (fun x : StatedSp 2 F => ((x : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hh
    simpa only [Subgroup.coe_mul, Units.val_mul] using this
  have hbd0 := blockDiag_of_commute_lrInv h2 0 hMu
  have hbd1 : BlockDiag (lrPair (1 : Fin 2)) M := by
    rw [blockDiag_iff] at hbd0 ⊢
    intro i j hij
    refine hbd0 i j ?_
    rw [mem_lrPair_one_iff, mem_lrPair_one_iff] at hij
    tauto
  have hJ := mem_statedSp_iff.1 h.2
  have hd0 := det_pairBlock_of_blockDiag (0 : Fin 2) hbd0 hJ
  have hd1 := det_pairBlock_of_blockDiag (1 : Fin 2) hbd1 hJ
  have h0 := blockDiag_iff.1 hbd0
  have z1 : M (Sum.inl 0) (Sum.inl 1) = 0 := h0 _ _ (by simp [lrPair])
  have z2 : M (Sum.inl 0) (Sum.inr 1) = 0 := h0 _ _ (by simp [lrPair])
  have z3 : M (Sum.inr 0) (Sum.inl 1) = 0 := h0 _ _ (by simp [lrPair])
  have z4 : M (Sum.inr 0) (Sum.inr 1) = 0 := h0 _ _ (by simp [lrPair])
  have z5 : M (Sum.inl 1) (Sum.inl 0) = 0 := h0 _ _ (by simp [lrPair])
  have z6 : M (Sum.inl 1) (Sum.inr 0) = 0 := h0 _ _ (by simp [lrPair])
  have z7 : M (Sum.inr 1) (Sum.inl 0) = 0 := h0 _ _ (by simp [lrPair])
  have z8 : M (Sum.inr 1) (Sum.inr 0) = 0 := h0 _ _ (by simp [lrPair])
  refine ⟨⟨_, hd0⟩, ⟨_, hd1⟩, statedSp_ext ?_⟩
  show M = pairMat (Sum.inl 0) (Sum.inr 0) (pairBlock (Sum.inl 0) (Sum.inr 0) M) *
    pairMat (Sum.inl 1) (Sum.inr 1) (pairBlock (Sum.inl 1) (Sum.inr 1) M)
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, pairMat, pairBlock,
      one_apply, z1, z2, z3, z4, z5, z6, z7, z8]

theorem lam_zero_eq_lam_one {A B : SL(2, F)} (h : lam (k := F) (0 : Fin 2) A = lam 1 B) :
    A = 1 := by
  have e := congrArg (fun x : StatedSp 2 F => pairBlock (Sum.inl 0) (Sum.inr 0)
    ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
  simp only [coe_lam, pairBlock_pairMat Sum.inl_ne_inr] at e
  apply Subtype.ext
  rw [e, Matrix.SpecialLinearGroup.coe_one]
  ext s t
  fin_cases s <;> fin_cases t <;> simp [pairBlock, pairMat]

theorem lam_commute_lrInv_zero (i : Fin 2) (A : SL(2, F)) :
    lam i A * lrInv F 0 = lrInv F 0 * lam i A := by
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · exact longRoot_commute 0 _ ⟨A, rfl⟩
  · exact lam_commute_lrInv (by decide) A

theorem sl2Diag_neg_one : sl2Diag (-1 : Fˣ) = -1 := by
  apply Subtype.ext
  rw [SymplecticTorusWeyl.coe_sl2Diag, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext s t
  fin_cases s <;> fin_cases t <;> simp

theorem lrInv_mul_lrInv_commute (h : StatedSp 2 F) :
    lrInv F (0 : Fin 2) * lrInv F 1 * h = h * (lrInv F 0 * lrInv F 1) := by
  apply statedSp_ext
  have e := Burgoyne.B.lrInv_zero_mul_lrInv_one (K := F)
  simp only [Subgroup.coe_mul, Units.val_mul] at e ⊢
  rw [e, neg_one_mul, mul_neg_one]

theorem false_of_sp4 [Finite F] (hF : Nat.card F = 3) {X : Type} [Group X] [Finite X]
    (α : StatedSp 2 F →* X) (hαi : Function.Injective α) (hαs : Function.Surjective α)
    {g : StatedSp 2 F} (hgg : g * g = 1)
    (hns : ∀ c : Fˣ, (g : GL (Fin 2 ⊕ Fin 2) F) ≠ GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c)
    {Q : Subgroup X} (hQ : IsSolvableTwoComponentIn Q (centralizer {α g}))
    (hcQ : α (lrInv F 0 * lrInv F 1) ∈ Q) : False := by
  have h2 : (2 : F) ≠ 0 := Burgoyne.PSL.two_ne_zero_of_three hF
  have hK : ringChar F ≠ 2 := by
    intro h
    apply h2
    have := ringChar.spec F 2
    exact_mod_cast this.2 (by rw [h])
  obtain ⟨H, hH⟩ := exists_conj_lrInv hK hgg hns
  have hg : g = H * lrInv F 0 * H⁻¹ := by rw [← hH]; group
  set ρ : Fin 2 → SL(2, F) →* X := fun i =>
    α.comp ((MulAut.conj H).toMonoidHom.comp (lam i)) with hρ
  have hρapp : ∀ i A, ρ i A = α (H * lam i A * H⁻¹) := fun _ _ => rfl
  have hρi : ∀ i, Function.Injective (ρ i) := fun i =>
    hαi.comp ((MulAut.conj H).injective.comp (lam_injective i))
  have hcomm : ∀ A B, ρ 0 A * ρ 1 B = ρ 1 B * ρ 0 A := by
    intro A B
    rw [hρapp, hρapp, ← map_mul, ← map_mul]
    congr 1
    calc H * lam 0 A * H⁻¹ * (H * lam 1 B * H⁻¹) = H * (lam 0 A * lam 1 B) * H⁻¹ := by group
      _ = H * (lam 1 B * lam 0 A) * H⁻¹ := by rw [Burgoyne.B.lam_zero_commute_lam_one]
      _ = H * lam 1 B * H⁻¹ * (H * lam 0 A * H⁻¹) := by group
  have hdec : ∀ x ∈ centralizer ({α g} : Set X), ∃ A B, x = ρ 0 A * ρ 1 B := by
    intro x hx
    obtain ⟨y, rfl⟩ := hαs x
    have hy : y * g = g * y := hαi (by
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.mp hx)
    have hy' : H⁻¹ * y * H * lrInv F 0 = lrInv F 0 * (H⁻¹ * y * H) := by
      have e : lrInv F 0 = H⁻¹ * g * H := hH.symm
      rw [e]
      calc H⁻¹ * y * H * (H⁻¹ * g * H) = H⁻¹ * (y * g) * H := by group
        _ = H⁻¹ * (g * y) * H := by rw [hy]
        _ = H⁻¹ * g * H * (H⁻¹ * y * H) := by group
    obtain ⟨A, B, hAB⟩ := exists_lam_mul_lam h2 hy'
    refine ⟨A, B, ?_⟩
    rw [hρapp, hρapp, ← map_mul]
    congr 1
    calc y = H * (H⁻¹ * y * H) * H⁻¹ := by group
      _ = H * (lam 0 A * lam 1 B) * H⁻¹ := by rw [hAB]
      _ = H * lam 0 A * H⁻¹ * (H * lam 1 B * H⁻¹) := by group
  have hR : ∀ i, (ρ i).range ≤ centralizer ({α g} : Set X) := by
    rintro i _ ⟨A, rfl⟩
    rw [mem_centralizer_singleton_iff, hρapp, ← map_mul, ← map_mul, hg]
    congr 1
    calc H * lam i A * H⁻¹ * (H * lrInv F 0 * H⁻¹) = H * (lam i A * lrInv F 0) * H⁻¹ := by
          group
      _ = H * (lrInv F 0 * lam i A) * H⁻¹ := by rw [lam_commute_lrInv_zero]
      _ = H * lrInv F 0 * H⁻¹ * (H * lam i A * H⁻¹) := by group
  have hN : ∀ i, ((ρ i).range.subgroupOf (centralizer ({α g} : Set X))).Normal := by
    intro i
    rw [normal_subgroupOf_iff (hR i)]
    rintro _ c ⟨M, rfl⟩ hc
    obtain ⟨A, B, rfl⟩ := hdec c hc
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · refine ⟨A * M * A⁻¹, ?_⟩
      rw [_root_.mul_inv_rev, map_mul, map_mul, map_inv]
      have e : ρ 1 B * ρ 0 M = ρ 0 M * ρ 1 B := (hcomm M B).symm
      calc ρ 0 A * ρ 0 M * (ρ 0 A)⁻¹ = ρ 0 A * (ρ 0 M * ρ 1 B) * (ρ 1 B)⁻¹ * (ρ 0 A)⁻¹ := by
            group
        _ = ρ 0 A * (ρ 1 B * ρ 0 M) * (ρ 1 B)⁻¹ * (ρ 0 A)⁻¹ := by rw [e]
        _ = ρ 0 A * ρ 1 B * ρ 0 M * ((ρ 1 B)⁻¹ * (ρ 0 A)⁻¹) := by group
    · refine ⟨B * M * B⁻¹, ?_⟩
      rw [_root_.mul_inv_rev, map_mul, map_mul, map_inv]
      have e : ρ 0 A * ρ 1 (B * M * B⁻¹) = ρ 1 (B * M * B⁻¹) * ρ 0 A := hcomm A _
      rw [map_mul, map_mul, map_inv] at e
      calc ρ 1 B * ρ 1 M * (ρ 1 B)⁻¹ =
          ρ 0 A * (ρ 1 B * ρ 1 M * (ρ 1 B)⁻¹) * (ρ 0 A)⁻¹ := by
            rw [e, mul_inv_cancel_right]
        _ = ρ 0 A * ρ 1 B * ρ 1 M * ((ρ 1 B)⁻¹ * (ρ 0 A)⁻¹) := by group
  have hinf : ∀ A B, ρ 0 A = ρ 1 B → A = 1 := by
    intro A B h
    rw [hρapp, hρapp] at h
    have h' := hαi h
    have h'' : lam (k := F) (0 : Fin 2) A = lam 1 B := by
      calc lam (k := F) (0 : Fin 2) A = H⁻¹ * (H * lam 0 A * H⁻¹) * H := by group
        _ = H⁻¹ * (H * lam 1 B * H⁻¹) * H := by rw [h']
        _ = lam 1 B := by group
    exact lam_zero_eq_lam_one h''
  have hneg : ∀ i, ρ i (-1) = α (H * lrInv F i * H⁻¹) := fun i => by
    rw [hρapp, lrInv, sl2Diag_neg_one]
  have hZ : ∀ i, ∀ x ∈ centralizer ({α g} : Set X), ρ i (-1) * x = x * ρ i (-1) := by
    intro i x hx
    obtain ⟨A, B, rfl⟩ := hdec x hx
    have hc1 : ∀ (j : Fin 2) (A : SL(2, F)), ρ j (-1) * ρ j A = ρ j A * ρ j (-1) := by
      intro j A
      rw [← map_mul, ← map_mul, neg_one_mul, mul_neg_one]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · calc ρ 0 (-1) * (ρ 0 A * ρ 1 B) = (ρ 0 (-1) * ρ 0 A) * ρ 1 B := by group
        _ = (ρ 0 A * ρ 0 (-1)) * ρ 1 B := by rw [hc1]
        _ = ρ 0 A * (ρ 0 (-1) * ρ 1 B) := by group
        _ = ρ 0 A * (ρ 1 B * ρ 0 (-1)) := by rw [hcomm]
        _ = ρ 0 A * ρ 1 B * ρ 0 (-1) := by group
    · calc ρ 1 (-1) * (ρ 0 A * ρ 1 B) = (ρ 1 (-1) * ρ 0 A) * ρ 1 B := by group
        _ = (ρ 0 A * ρ 1 (-1)) * ρ 1 B := by rw [hcomm]
        _ = ρ 0 A * (ρ 1 (-1) * ρ 1 B) := by group
        _ = ρ 0 A * (ρ 1 B * ρ 1 (-1)) := by rw [hc1]
        _ = ρ 0 A * ρ 1 B * ρ 1 (-1) := by group
  have hc : ρ 0 (-1) * ρ 1 (-1) = α (lrInv F 0 * lrInv F 1) := by
    rw [hneg, hneg, ← map_mul]
    congr 1
    calc H * lrInv F 0 * H⁻¹ * (H * lrInv F 1 * H⁻¹) = H * (lrInv F 0 * lrInv F 1) * H⁻¹ := by
          group
      _ = lrInv F 0 * lrInv F 1 * H * H⁻¹ := by rw [← lrInv_mul_lrInv_commute H]
      _ = lrInv F 0 * lrInv F 1 := by group
  exact false_of_two_sl hF (ρ 0) (ρ 1) (hρi 0) (hρi 1) (hR 0) (hR 1) (hN 0) (hN 1) hcomm hinf
    (fun x hx _ => hdec x hx) (hZ 0) (hZ 1) hQ (hc ▸ hcQ)

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
