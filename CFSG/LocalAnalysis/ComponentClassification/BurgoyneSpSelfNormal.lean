module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSplit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpThree

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  exists_bilin_split_equiv)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem conjAut_eq_of_eq_smul [Finite K] (hr : 1 ≤ r) {D D' : gsp r K} {c : K} (hc : c ≠ 0)
    (h : ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      c • ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    conjAut r K D = conjAut r K D' := by
  have h1 : conjAut r K (D'⁻¹ * D) = 1 := by
    rw [conjAut_eq_one_iff hr]
    refine ⟨Units.mk0 c hc, Units.ext ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, h, Matrix.mul_smul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

theorem skewSplit_oddCoreIn_eq_bot_three [Finite K] (h3 : Nat.card K = 3) (hr : 3 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B) :
    oddCoreIn B (conjAut r K (stdSkewGsp r K)) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_three h3
  have hK : ringChar K ≠ 2 := fun h => h2 (by
    have := ringChar.spec K 2
    exact_mod_cast (this.2 (by rw [h])))
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hoddy := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨D, a, b, rfl, hD⟩ := skewSplit_oddCore hK (by omega) (Or.inl hr) hinj hB hy
  have hsq : ∀ x : K, x ≠ 0 → x * x = 1 := fun x hx => by
    rcases three_elements h3 x with h | h | h
    · exact absurd h hx
    · rw [h, one_mul]
    · rw [h, neg_mul_neg, one_mul]
  have hne : ∀ x : Fin r ⊕ Fin r, Sum.elim (fun _ => a) (fun _ => b) x ≠ 0 := by
    intro x h0
    have h1 := congrFun (congrFun (Units.mul_inv (D : GL (Fin r ⊕ Fin r) K)) x) x
    rw [hD, diagonal_mul, h0, zero_mul, one_apply_eq] at h1
    exact zero_ne_one h1
  have hD2 : conjAut r K (D ^ 2 ^ 1) = 1 := by
    rw [conjAut_eq_one_iff (by omega)]
    refine ⟨1, Units.ext ?_⟩
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hD, pow_one, sq, diagonal_mul_diagonal,
      map_one, Units.val_one, ← diagonal_one]
    congr 1
    funext x
    exact hsq _ (hne x)
  rw [map_pow] at hD2
  exact UnbalancedCatalog.SpChain.eq_one_of_odd_orderOf hoddy hD2

section SplitSelf

variable {A : gsp r K} {l : K}

theorem mem_VPl_of_orth (hl0 : l ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (l ^ 2) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (l ^ 2) • formJ r K)
    (hnd : ((pairedSympForm K r).domRestrict₁₂ (VMl A l) (VMl A l)).SeparatingLeft)
    {x : Fin r ⊕ Fin r → K} (hx : ∀ w ∈ VMl A l, pairedSympForm K r x w = 0) :
    x ∈ VPl A l := by
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set y := x - l⁻¹ • (M *ᵥ x) with hy
  have hMMx : M *ᵥ (M *ᵥ x) = (l ^ 2) • x := by rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  have hyM : y ∈ VMl A l := by
    rw [mem_eigenMinus hl0, hy, mulVec_sub, mulVec_smul, hMMx, smul_smul]
    rw [show l⁻¹ * l ^ 2 = l by field_simp]
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hl0]
    module
  have hMx : ∀ w ∈ VMl A l, pairedSympForm K r (M *ᵥ x) w = 0 := by
    intro w hw
    have h1 := form_similitude hJ x w
    rw [(mem_eigenMinus hl0).1 hw, hx w hw, mul_zero, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (neg_ne_zero.2 hl0)
  have hy0 : y = 0 := by
    have := hnd ⟨y, hyM⟩ fun w => by
      rw [LinearMap.domRestrict₁₂_apply]
      change pairedSympForm K r (x - l⁻¹ • (M *ᵥ x)) (w : Fin r ⊕ Fin r → K) = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hx w w.2, hMx w w.2,
        smul_zero, sub_zero]
    exact congrArg Subtype.val this
  rw [mem_eigenPlus hl0]
  have h := sub_eq_zero.1 (hy ▸ hy0)
  calc M *ᵥ x = l • (l⁻¹ • (M *ᵥ x)) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    _ = l • x := by rw [← h]

theorem smul_coe_lrInvGsp (i₀ : Fin r) (l : K) :
    l • ((lrInvGsp r K i₀ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      diagonal fun x => if x ∈ lrPair i₀ then -l else l := by
  rw [coe_lrInvGsp, offInd]
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.smul_apply, Matrix.sub_apply, diagonal_apply_eq, one_apply_eq,
      smul_eq_mul]
    split_ifs <;> ring
  · simp [hxy, one_apply_ne hxy]

theorem exists_split_self_lrInv_normal_form (hK : ringChar K ≠ 2) (hr : 1 ≤ r) (hl0 : l ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (l ^ 2) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (l ^ 2) • formJ r K)
    (hM2 : Module.finrank K (VMl A l) = 2) :
    ∃ H : StatedSp r K, ((((H : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        l • ((lrInvGsp r K ⟨0, by omega⟩ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAA' := linA_mul_self hAA
  have hTB : ∀ v w, pairedSympForm K r (invSMulOp l ((linA A :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (invSMulOp l ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = pairedSympForm K r v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  obtain ⟨-, -, -, -, hndM, -⟩ := exists_bilin_split_equiv h2 pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate hl0 hAA' hTB
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ VMl A l, a ≠ 0 := by
    by_contra h
    push Not at h
    have : VMl A l = ⊥ := (Submodule.eq_bot_iff _).2 h
    rw [this, finrank_bot] at hM2
    exact absurd hM2 (by norm_num)
  obtain ⟨b₀, hb₀, hab₀⟩ : ∃ b ∈ VMl A l, pairedSympForm K r a b ≠ 0 := by
    by_contra h
    push Not at h
    have := hndM.1 ⟨a, ha⟩ fun w => h w w.2
    exact ha0 (congrArg Subtype.val this)
  set b := (pairedSympForm K r a b₀)⁻¹ • b₀ with hb
  have hbM : b ∈ VMl A l := Submodule.smul_mem _ _ hb₀
  have hab : pairedSympForm K r a b = 1 := by
    rw [hb, map_smul, smul_eq_mul, inv_mul_cancel₀ hab₀]
  have hba : pairedSympForm K r b a = -1 := by
    rw [← bJ_eq, bJ_swap, bJ_eq, hab]
  have hind : LinearIndependent K ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrArg (pairedSympForm K r a) hst
    have e2 := congrArg (pairedSympForm K r b) hst
    simp only [map_add, map_smul, smul_eq_mul, map_zero, hab, hba,
      pairedSympForm_isAlt a, pairedSympForm_isAlt b] at e1 e2
    exact ⟨by linear_combination -e2, by linear_combination e1⟩
  have hspan : Submodule.span K {a, b} = VMl A l := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hbM
    · have h := finrank_span_eq_card hind
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union] at h
      rw [hM2, h]
      simp
  have horth : ∀ x, pairedSympForm K r x a = 0 → pairedSympForm K r x b = 0 → x ∈ VPl A l := by
    intro x hxa hxb
    refine mem_VPl_of_orth hl0 hAA hJ hndM.1 fun w hw => ?_
    rw [← hspan] at hw
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hw
    rw [map_add, map_smul, map_smul, hxa, hxb, smul_zero, smul_zero, add_zero]
  obtain ⟨m', c, hdim', hc11, hc22, hc12, hca, hcb⟩ :=
    CatalogueBAlternatingIsometry.exists_symplectic_basis_prescribed_pair (pairedSympForm K r)
      pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate a b hab
  rw [finrank_standard] at hdim'
  obtain rfl : r = m' + 1 := by omega
  have h0 : (⟨0, by omega⟩ : Fin (m' + 1)) = 0 := rfl
  have hc21 : ∀ i j, pairedSympForm K (m' + 1) (c (Sum.inr i)) (c (Sum.inl j)) =
      -(if j = i then 1 else 0) := by
    intro i j
    rw [← bJ_eq, bJ_swap, bJ_eq, hc12]
  have hgram : ∀ p q, pairedSympForm K (m' + 1) (c p) (c q) = formJ (m' + 1) K p q := by
    rintro (i | i) (j | j)
    · rw [hc11]
      simp [formJ]
    · rw [hc12]
      simp [formJ, one_apply]
    · rw [hc21]
      simp [formJ, one_apply, eq_comm]
    · rw [hc22]
      simp [formJ]
  obtain ⟨H, hH⟩ := exists_sp_of_gram hgram
  refine ⟨H, inv_mul_mul_eq_of_cols hH fun x => ?_⟩
  rw [smul_coe_lrInvGsp, sum_diagonal_smul, h0]
  by_cases hx : x ∈ lrPair (0 : Fin (m' + 1))
  · simp only [hx, ↓reduceIte]
    have hxm : c x ∈ VMl A l := by
      rcases (mem_pair.1 hx) with rfl | rfl
      · rw [hca]
        exact ha
      · rw [hcb]
        exact hbM
    exact (mem_eigenMinus hl0).1 hxm
  · simp only [hx, ↓reduceIte]
    have hx' : x ≠ Sum.inl 0 ∧ x ≠ Sum.inr 0 := by
      constructor <;> rintro rfl <;> simp [lrPair] at hx
    refine (mem_eigenPlus hl0).1 (horth _ ?_ ?_)
    · rw [← hca, hgram]
      rcases x with i | i
      · simp [formJ]
      · have hi : i ≠ 0 := fun h => hx'.2 (by rw [h])
        simp [formJ, one_apply, hi]
    · rw [← hcb, hgram]
      rcases x with i | i
      · have hi : i ≠ 0 := fun h => hx'.1 (by rw [h])
        simp [formJ, one_apply, hi]
      · simp [formJ]

end SplitSelf

end CFSG.ComponentClassification.Burgoyne.Sp
