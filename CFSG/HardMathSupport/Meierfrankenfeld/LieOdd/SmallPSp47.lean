module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Small
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpOuter
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpInvolution
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.PSpOddOrder
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.SylowRank
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.RouteA
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Cls

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.Assembly.LowTwoRank TauCeti Matrix

@[expose] def gM47 (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.of fun i j =>
    if i = Sum.inl 0 ∧ j = Sum.inr 0 then 1
    else if i = Sum.inr 0 ∧ j = Sum.inl 0 then -1
    else if i = j ∧ i ≠ Sum.inl 0 ∧ i ≠ Sum.inr 0 then 1
    else 0

theorem gM47_mul_transpose (K : Type) [Field K] : gM47 K * (gM47 K)ᵀ = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [gM47, Matrix.mul_apply]

theorem gM47_transpose_mul (K : Type) [Field K] : (gM47 K)ᵀ * gM47 K = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [gM47, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

@[expose] def g47 (K : Type) [Field K] : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨gM47 K, (gM47 K)ᵀ, gM47_mul_transpose K, gM47_transpose_mul K⟩

theorem g47_mem (K : Type) [Field K] : g47 K ∈ StatedSp 2 K := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  show (gM47 K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * gM47 K = Matrix.fromBlocks 0 1 (-1) 0
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [gM47, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks]

theorem gM47_sq (K : Type) [Field K] :
    gM47 K * gM47 K = Matrix.diagonal (Sum.elim ![-1, 1] ![-1, 1]) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [gM47, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem gM47_pow_four (K : Type) [Field K] : gM47 K * gM47 K * (gM47 K * gM47 K) = 1 := by
  rw [gM47_sq, Matrix.diagonal_mul_diagonal]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp

section Group

variable {K : Type} [Field K] [Finite K]

theorem exists_orderOf_four_psp47 (hK : Nat.card K = 7) :
    ∃ y : StatedProj (StatedSp 2 K), orderOf y = 4 := by
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 7 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K 7 := charP_of_card_eq_prime_pow (f := 1) (by simpa using hcard)
  let g : StatedSp 2 K := ⟨g47 K, g47_mem K⟩
  have hpow4 : g ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change ((g47 K ^ 4 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1
    rw [Units.val_pow_eq_pow_val]
    change gM47 K ^ 4 = 1
    calc gM47 K ^ 4 = (gM47 K * gM47 K) * (gM47 K * gM47 K) := by noncomm_ring
      _ = 1 := gM47_pow_four K
  have h2 : ¬ (QuotientGroup.mk g : StatedProj (StatedSp 2 K)) ^ 2 = 1 := by
    intro h
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h
    have e' := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
    have hM : (((g ^ 2 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = gM47 K * gM47 K := by
      rw [sq, Subgroup.coe_mul, Units.val_mul]
      rfl
    simp only [hM, gM47_sq, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e'
    have e0 := congrFun (congrFun e' (Sum.inl 0)) (Sum.inl 0)
    have e1 := congrFun (congrFun e' (Sum.inl 1)) (Sum.inl 1)
    simp only [Matrix.diagonal_apply_eq, Sum.elim_inl] at e0 e1
    have h' : (-1 : K) = 1 := by
      have a0 : (c : K) = -1 := by simpa using e0
      have a1 : (c : K) = 1 := by simpa using e1
      rw [← a0, a1]
    have h2K : (2 : K) = 0 := by linear_combination -h'
    have := (CharP.cast_eq_zero_iff K 7 2).1 (by exact_mod_cast h2K)
    omega
  have h4 : (QuotientGroup.mk g : StatedProj (StatedSp 2 K)) ^ 4 = 1 := by
    rw [← QuotientGroup.mk_pow, hpow4]
    rfl
  refine ⟨QuotientGroup.mk g, ?_⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (QuotientGroup.mk g :
    StatedProj (StatedSp 2 K))) (by simpa using h2) (by simpa using h4)
  simpa using this

theorem noIrrFFOffender_psp47 (hK : Nat.card K = 7) :
    NoIrrFFOffender (StatedProj (StatedSp 2 K)) := by
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 7 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hchar : CharP K 7 := charP_of_card_eq_prime_pow (f := 1) (by simpa using hcard)
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 7 2).1 (by exact_mod_cast h)
    omega
  have hneg : ¬ IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, hcard]
    norm_num
  have h2r : (((2 + 2 : ℕ)) : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 7 (2 + 2)).1 h
    omega
  have hring : ringChar K ≠ 2 := by
    rw [ringChar.eq K 7]
    norm_num
  have hcent := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_psp4_eq_bot (F := K) hring
  have hProj : Nat.card (StatedProj (StatedSp 2 K)) = 2 ^ 8 * 540225 := by
    have h := Proving.card_statedProj_statedSp_of_two_ne_zero h2 (n := 2) (by norm_num)
    rw [hK] at h
    norm_num [Finset.prod_Icc_succ_top] at h
    omega
  have hSp : Nat.card (StatedSp 2 K) = 2 * Nat.card (StatedProj (StatedSp 2 K)) :=
    card_statedSp_eq_two_mul_card_proj h2 2
  have hcard2 : Nat.card (MulAut (StatedProj (StatedSp 2 K))) ≤
      2 * Nat.card (StatedProj (StatedSp 2 K)) := by
    have := card_mulAut_psp_le_card_sp_mul (K := K) (p := 7) (e := 1) (r := 2)
      (by norm_num) (by simpa using hK) le_rfl
    simpa [hSp] using this
  obtain ⟨y, hy⟩ := exists_orderOf_four_psp47 hK
  have hr : ∀ B : Subgroup (StatedProj (StatedSp 2 K)), (∀ x ∈ B, ∀ z ∈ B, x * z = z * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 7 :=
    FFToolkit.rank_le_two_pow_pred_of_orderOf_four (k := 8) hProj ⟨270112, by norm_num⟩ hy
  have hord2 : orderOf (2 : ZMod 7) = 3 := by
    apply orderOf_eq_prime <;> decide
  refine noIrrFFOffender_of_route_A (r := 7) (ρ := 9) (p := 7) (n := 0) hcent hcard2
    (by norm_num) (by norm_num) (by rw [hord2]; norm_num) hr ?_ ?_ ?_
  · intro L _ _ hq ⟨e⟩ hodd
    have := center_eq_bot_of_psp hq.1 hodd (K := K) le_rfl (Or.inl (by omega))
      (by rw [hK]; decide) e
    rw [this, Subgroup.card_bot]
    norm_num
  · intro t ht2 ht1
    classical
    exact exists_heisCfg_of_involution (p := 7) (n := 0) (by norm_num) hneg t ht2 ht1
  · intro ψ hψ hψ2
    obtain ⟨x, hx, hxinv⟩ := outer_involution_inverts_psp (p := 7) (K := K) (r := 2)
      (by norm_num) hK le_rfl hneg h2r ψ hψ hψ2
    exact ⟨7, ⟨by norm_num⟩, x, by norm_num, by rw [hord2], hx, hxinv⟩

end Group

theorem noIrrFFOffender_smallPSp47 {q : PrimePower} (hv : (LieTypeIndex.B 2 q).Valid)
    (h7 : q.card = 7) : NoIrrFFOffender (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group := by
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B 2 q, hv⟩ : ValidLieTypeIndex)
  have hK : Nat.card ↥(ValidLieTypeIndex.fixedField (⟨.B 2 q, hv⟩ : ValidLieTypeIndex)) = 7 := by
    rw [ValidLieTypeIndex.card_fixedField]
    simpa [ValidLieTypeIndex.fieldOrder, PrimePower.card_def] using
      (PrimePower.card_def q).symm.trans h7
  exact FFSporadic.noIrrFFOffender_transfer (noIrrFFOffender_psp47 hK)
    ⟨(CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv).symm⟩

theorem smallPSp47 : SmallPSp47 := by
  intro d q hq hd
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_smallPSp47 hv hq)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
