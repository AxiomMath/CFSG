module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCAbs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCProj
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff
  sl2Diag)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  similitudeCentralizer exists_bilin_split_equiv eigen_ne_bot)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

@[expose] def fixSubEquivOfProd {A : gsp r K} {W : Submodule K (Fin r ⊕ Fin r → K)}
    {U U' : Type*} [Group U] [Group U'] (E : spCent r K A ≃* U × U')
    (hE : ∀ g : spCent r K A, (E g).2 = 1 ↔ ∀ v ∈ W,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v) : fixSub r K A W ≃* U :=
  MulEquiv.ofBijective ((MonoidHom.fst U U').comp
    (E.toMonoidHom.comp (Subgroup.inclusion (fixSub_le A W)))) (by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      have h1 : (E (Subgroup.inclusion (fixSub_le A W) g)).2 = 1 := (hE _).2 g.2.2
      have h2 : E (Subgroup.inclusion (fixSub_le A W) g) = 1 := Prod.ext hg h1
      rw [mem_bot]
      have h3 := E.injective (h2.trans (map_one E).symm)
      exact Subtype.ext (congrArg (fun x : spCent r K A => (x : StatedSp r K)) h3)
    · intro u
      have hfix := (hE (E.symm (u, 1))).1 (by rw [MulEquiv.apply_symm_apply])
      refine ⟨⟨E.symm (u, 1), (E.symm (u, 1)).2, hfix⟩, ?_⟩
      change (E (E.symm (u, 1))).1 = u
      rw [MulEquiv.apply_symm_apply])

theorem orderOf_lrInv (h2 : (2 : K) ≠ 0) (i₀ : Fin r) : orderOf (lrInv K i₀) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← map_mul, ← map_mul, neg_one_mul, neg_neg, map_one, map_one]
  · intro h1
    have := congrArg (fun g : StatedSp r K =>
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl i₀) (Sum.inl i₀)) h1
    simp only [coe_lrInv, Subgroup.coe_one, Units.val_one] at this
    rw [Matrix.sub_apply, Matrix.smul_apply, offInd, diagonal_apply_eq,
      ite_eq_left (by simp [lrPair]), one_apply_eq] at this
    simp only [smul_zero, zero_sub] at this
    exact h2 (by linear_combination -this)

theorem lrInv_commute_ne (h2 : (2 : K) ≠ 0) (hr : 2 ≤ r) :
    lrInv K (⟨0, by omega⟩ : Fin r) * lrInv K ⟨1, by omega⟩ =
        lrInv K ⟨1, by omega⟩ * lrInv K (⟨0, by omega⟩ : Fin r) ∧
      lrInv K (⟨0, by omega⟩ : Fin r) ≠ lrInv K ⟨1, by omega⟩ := by
  refine ⟨?_, ?_⟩
  · apply statedSp_ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_lrInv]
    have hcomm : offInd K (lrPair (⟨0, by omega⟩ : Fin r)) *
        offInd K (lrPair (⟨1, by omega⟩ : Fin r)) =
        offInd K (lrPair (⟨1, by omega⟩ : Fin r)) * offInd K (lrPair (⟨0, by omega⟩ : Fin r)) := by
      rw [offInd, offInd, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      ext i
      ring
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, hcomm]
    abel
  · intro h
    have := congrArg (fun g : StatedSp r K =>
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) h
    simp only [coe_lrInv] at this
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, offInd,
      offInd, diagonal_apply_eq, diagonal_apply_eq, ite_eq_left (by simp [lrPair]),
      ite_eq_right (by simp [lrPair])] at this
    simp only [smul_eq_mul, mul_one, one_apply_eq] at this
    exact h2 (by linear_combination -this)

variable [Finite K]

theorem blockOK_of_isometryEquiv (hK : ringChar K ≠ 2) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hdim : 2 ≤ Module.finrank K V) {P : Type} [Group P] [Finite P] {N : Subgroup P}
    (e : N ≃* CatalogueBAlternatingIsometry.isometryGroup B) : BlockOK K N := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  obtain ⟨m, hm, ⟨e'⟩⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  have hm1 : 1 ≤ m := by omega
  set eS : N ≃* StatedSp m K := (e.trans e').trans (MulEquiv.subgroupCongr
    (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := m) (K := K)).symm) with heS
  by_cases hsmall : Module.finrank K V = 2 ∧ Nat.card K = 3
  · left
    have := CatalogueBAlternatingIsometry.plane_fieldThree_solvable B hB hnd hsmall.1 hsmall.2
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  right
  have hq : IsQuasisimple N := LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CatalogueBAlternatingIsometry.isometry_quasisimple B hB hnd hdim hodd
      (not_and_or.1 hsmall))
  refine ⟨hq, ?_, ?_⟩
  ·
    rw [Nat.card_congr eS.toEquiv, ← Nat.card_congr (longRootEquiv K
      (⟨0, by omega⟩ : Fin m)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  · by_cases hd2 : Module.finrank K V = 2
    · right
      obtain ⟨f⟩ := CatalogueBAlternatingIsometry.exists_planeIsometryEquivSL B hB hnd hd2
      exact ⟨e.trans f⟩
    · left
      have hm2 : 2 ≤ m := by
        obtain ⟨k, hk⟩ := CatalogueBAlternatingIsometry.even_finrank B hB hnd
        omega
      obtain ⟨hc, hne⟩ := lrInv_commute_ne h2 hm2 (K := K)
      refine ⟨_, (eS.symm (lrInv K ⟨0, by omega⟩)).2, _, (eS.symm (lrInv K ⟨1, by omega⟩)).2,
        ?_, ?_, ?_, ?_⟩
      · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_lrInv h2]
      · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_lrInv h2]
      · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
      · intro h
        exact hne (eS.symm.injective (Subtype.ext h))

theorem psp_split_false (hK : ringChar K ≠ 2) {A : StatedSp r K}
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1)
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {R₁ R₂ : Subgroup (StatedProj (StatedSp r K))} {p m : ℕ} [Fact p.Prime]
    (hC : PropCData (projH _ A) R₁ R₂ p m) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Ag : gsp r K := ⟨A, statedSp_le_gsp A.2⟩ with hAg
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hl0 : (1 : K) ≠ 0 := one_ne_zero
  have hAA1 : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((1 : K) ^ 2) • 1 := by
    rw [one_pow, one_smul]
    exact hAA
  have hJ : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      formJ r K * ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((1 : K) ^ 2) • formJ r K := by
    rw [one_pow, one_smul]
    exact mem_statedSp_iff.1 A.2
  have hAA' := linA_mul_self hAA1
  have hTB : ∀ v w, pairedSympForm K r (invSMulOp 1 ((linA Ag :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (invSMulOp 1 ((linA Ag : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = pairedSympForm K r v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  have hAns' : ∀ c : K, ((linA Ag : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  obtain ⟨hPne, hMne⟩ := eigen_ne_bot h2 hl0 hAA' hAns'
  obtain ⟨-, haltP, haltM, hndP, hndM, e, he⟩ :=
    exists_bilin_split_equiv h2 pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      hl0 hAA' hTB
  set Ψ := (spCentEquiv Ag).trans e with hΨ
  have hres : ∀ g : spCent r K Ag, (Ψ g).2 = 1 ↔ ∀ v ∈ VMl Ag 1,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv Ag g)).2 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv Ag g)).2]
    simp only [spCentEquiv_apply]
  have hres' : ∀ g : spCent r K Ag, ((Ψ.trans (MulEquiv.prodComm)) g).2 = 1 ↔ ∀ v ∈ VPl Ag 1,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv Ag g)).1 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv Ag g)).1]
    simp only [spCentEquiv_apply]
  set N₁ := fixSub r K Ag (VMl Ag 1) with hN₁
  set N₂ := fixSub r K Ag (VPl Ag 1) with hN₂
  have hcent : centralizer ({A} : Set (StatedSp r K)) = spCent r K Ag := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_spCent]
    constructor
    · intro h
      have := congrArg (fun u : StatedSp r K =>
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h
      simp only [Subgroup.coe_mul, Units.val_mul] at this
      exact this.symm
    · intro h
      apply statedSp_ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      exact h.symm
  have hsplit : spCent r K Ag ≤ N₁ ⊔ N₂ := by
    intro g hg
    have h1 : (Ψ.symm ((Ψ ⟨g, hg⟩).1, 1) : StatedSp r K) ∈ N₁ :=
      ⟨(Ψ.symm ((Ψ ⟨g, hg⟩).1, 1)).2, (hres _).1 (by rw [MulEquiv.apply_symm_apply])⟩
    have h2' : (Ψ.symm (1, (Ψ ⟨g, hg⟩).2) : StatedSp r K) ∈ N₂ :=
      ⟨(Ψ.symm (1, (Ψ ⟨g, hg⟩).2)).2, (hres' _).1 (by
        change (Ψ (Ψ.symm (1, (Ψ ⟨g, hg⟩).2))).1 = 1
        rw [MulEquiv.apply_symm_apply])⟩
    have hgab : (⟨g, hg⟩ : spCent r K Ag) =
        Ψ.symm ((Ψ ⟨g, hg⟩).1, 1) * Ψ.symm (1, (Ψ ⟨g, hg⟩).2) := by
      apply Ψ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, Prod.mk_mul_mk, mul_one,
        one_mul]
    have := congrArg (fun u : spCent r K Ag => (u : StatedSp r K)) hgab
    simp only [Subgroup.coe_mul] at this
    rw [show g = _ from this]
    exact mul_mem (mem_sup_left h1) (mem_sup_right h2')
  have hZ := scalars_subgroupOf_le_center (H := StatedSp r K)
  have hblock : ∀ {W : Submodule K (Fin r ⊕ Fin r → K)},
      (∀ g ∈ spCent r K Ag, ∀ v ∈ W,
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W) →
      (fixSub r K Ag W).map (QuotientGroup.mk' _) ≤
          centralizer ({QuotientGroup.mk' _ A} : Set (StatedProj (StatedSp r K))) ∧
        (((fixSub r K Ag W).map (QuotientGroup.mk' _)).subgroupOf
          (centralizer ({QuotientGroup.mk' _ A} :
            Set (StatedProj (StatedSp r K))))).IsSubnormal := by
    intro W hW
    refine isSubnormal_map_mk hZ A (by rw [hcent]; exact fixSub_le Ag W) ?_
    intro f hf q hq
    rw [hcent] at hf
    exact conj_mem_fixSub hW hf hq
  have hW₁ : ∀ g ∈ spCent r K Ag, ∀ v ∈ VMl Ag 1,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ VMl Ag 1 :=
    fun g hg v hv => mulVec_mem_VMl hl0 hg hv
  have hW₂ : ∀ g ∈ spCent r K Ag, ∀ v ∈ VPl Ag 1,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ VPl Ag 1 :=
    fun g hg v hv => mulVec_mem_VPl hl0 hg hv
  have hperf : ∀ L : Subgroup (StatedProj (StatedSp r K)),
      L ≤ centralizer ({QuotientGroup.mk' _ A} : Set _) → ⁅L, L⁆ = L →
      L ≤ N₁.map (QuotientGroup.mk' _) ⊔ N₂.map (QuotientGroup.mk' _) := by
    intro L hL hp
    refine (le_map_commutator_of_perfect_mk hZ A hL hp).trans ?_
    rw [← Subgroup.map_sup]
    refine map_mono ((commutator_le_self _).trans ?_)
    rw [hcent]
    exact hsplit
  have hinj : ∀ {W : Submodule K (Fin r ⊕ Fin r → K)}, W ≠ ⊥ →
      Function.Injective ((QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
        (StatedSp r K))).comp (fixSub r K Ag W).subtype) := by
    intro W hWne
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).1 hg
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hgv := g.2.2 v hv
    have hgm : (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • 1 := by
      have e1 : ((GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by rw [hc]; rfl
      rw [← e1, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hgm, smul_mulVec, one_mulVec] at hgv
    have hc1 : (c : K) = 1 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        push Not at h
        exact hv0 (funext h)
      have := congrFun hgv i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      have : ((c : K) - 1) * v i = 0 := by linear_combination this
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hi)
    apply Subtype.ext
    apply statedSp_ext
    rw [hgm, hc1, one_smul]
    rfl
  have hiso : ∀ {W : Submodule K (Fin r ⊕ Fin r → K)}, W ≠ ⊥ →
      (fixSub r K Ag W).map (QuotientGroup.mk' _) ≃* fixSub r K Ag W := fun hWne =>
    ((MonoidHom.ofInjective (hinj hWne)).trans (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, range_subtype]))).symm
  have hB₁ : BlockOK K (N₁.map (QuotientGroup.mk' _)) :=
    blockOK_of_isometryEquiv hK haltP hndP
      (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hPne _ haltP hndP)
      (((hiso hMne).trans (fixSubEquivOfProd Ψ hres)).trans
        (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _))
  have hB₂ : BlockOK K (N₂.map (QuotientGroup.mk' _)) :=
    blockOK_of_isometryEquiv hK haltM hndM
      (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hMne _ haltM hndM)
      (((hiso hPne).trans (fixSubEquivOfProd (Ψ.trans MulEquiv.prodComm) hres')).trans
        (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _))
  exact propCData_false_of_blocks hC (F := K) (hblock hW₁).1 (hblock hW₂).1 (hblock hW₁).2
    (hblock hW₂).2 hperf hB₁ hB₂

end CFSG.ComponentClassification.Burgoyne.C
