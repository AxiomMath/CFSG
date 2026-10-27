module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BBlk
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthMain

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open P58b3 (tBlockP OddGen)
open scoped MatrixGroups

namespace P58b3L

variable {K : Type} [Field K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem projH_inj_of_mem_oIsoBlock {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty)
    {B B' : matrixDerived (oQ (diagGL hw))} (hB : (B : GL (Fin d) K) ∈ oIsoBlock K hw I)
    (hB' : (B' : GL (Fin d) K) ∈ oIsoBlock K hw I) (h : projH _ B = projH _ B') : B = B' := by
  rw [projH_eq_projH_iff] at h
  obtain ⟨c, hc⟩ := mem_subgroupOf.mp h
  have hm : ((B⁻¹ * B' : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) ∈ oIsoBlock K hw I := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem hB) hB'
  obtain ⟨k, hk⟩ := hIc
  have hkk := ((mem_oIsoBlock_iff hw).1 hm).2 k k (Or.inl (Finset.mem_compl.1 hk))
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    ite_eq_left rfl] at hkk
  have h1 : B⁻¹ * B' = 1 := by
    apply Subtype.ext
    rw [← hc, Subgroup.coe_one, show c = 1 from Units.ext hkk, map_one]
  calc B = B * (B⁻¹ * B') := by rw [h1, mul_one]
    _ = B' := mul_inv_cancel_left B B'

theorem eq_one_of_mem_tBlockP_inf_of_odd {I : Finset (Fin d)}
    {r : StatedProj (matrixDerived (oQ (diagGL hw)))} (h₁ : r ∈ tBlockP hw I)
    (h₂ : r ∈ tBlockP hw Iᶜ) (hro : Odd (orderOf r)) : r = 1 := by
  obtain ⟨B, hB, rfl⟩ := h₁
  obtain ⟨B', hB', hBB'⟩ := h₂
  replace hB : (B : GL (Fin d) K) ∈ oIsoBlock K hw I := hB
  replace hB' : (B' : GL (Fin d) K) ∈ oIsoBlock K hw Iᶜ := hB'
  rw [projH_eq_projH_iff] at hBB'
  obtain ⟨c, hc⟩ := mem_subgroupOf.mp hBB'
  have hBe : ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (c : K) • ((B' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    have e : (B : GL (Fin d) K) = (B' : GL (Fin d) K) * GeneralLinearGroup.scalar (Fin d) c := by
      rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [e, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨hBI, hBs⟩ := (mem_oIsoBlock_iff hw).1 hB
  have hB's := ((mem_oIsoBlock_iff hw).1 hB').2
  have hrow : ∀ i ∈ I, ∀ j, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
      if i = j then (c : K) else 0 := by
    intro i hi j
    rw [hBe, Matrix.smul_apply, hB's i j (Or.inl fun h => Finset.mem_compl.1 h hi), smul_eq_mul]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left hij, mul_one]
    · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]
  have hc2 : ∀ i₀ ∈ I, (c : K) * c = 1 := by
    intro i₀ hi₀
    have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 hBI
    have h := congrFun (congrFun hiso i₀) i₀
    rw [coe_diagGL, Matrix.mul_apply] at h
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.diagonal_apply_eq] at h
    have hcol : ∀ l, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) l i₀ =
        if i₀ = l then (c : K) else 0 := by
      intro l
      by_cases hl : l ∈ I
      · rw [hrow l hl i₀]
        by_cases h' : l = i₀
        · rw [ite_eq_left h', ite_eq_left h'.symm]
        · rw [ite_eq_right h', ite_eq_right (Ne.symm h')]
      · have h' : l ≠ i₀ := fun e => hl (e ▸ hi₀)
        rw [hBs l i₀ (Or.inl hl), ite_eq_right h', ite_eq_right (Ne.symm h')]
    rw [Finset.sum_eq_single i₀ (fun l _ hl => by rw [hcol l, ite_eq_right (Ne.symm hl)]; ring)
      (fun h => absurd (Finset.mem_univ _) h), hcol i₀, ite_eq_left rfl] at h
    have h' : (c : K) * c * w i₀ = 1 * w i₀ := by linear_combination h
    exact mul_right_cancel₀ (hw i₀) h'
  have hrow' : ∀ i, ∃ a : K, a * a = 1 ∧
      ∀ k, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i k = if i = k then a else 0 := by
    intro i
    by_cases hi : i ∈ I
    · exact ⟨c, hc2 i hi, hrow i hi⟩
    · exact ⟨1, one_mul 1, fun k => hBs i k (Or.inl hi)⟩
  have hBB : ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    ext i j
    obtain ⟨a, ha, hai⟩ := hrow' i
    rw [Matrix.mul_apply, Finset.sum_eq_single i
      (fun k _ hk => by rw [hai k, ite_eq_right (Ne.symm hk), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), hai i, ite_eq_left rfl, hai j, Matrix.one_apply]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left hij, ha]
    · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]
  have hsq : B * B = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, hBB, Subgroup.coe_one, Units.val_one]))
  have h2 : orderOf (projH _ B) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two, ← map_mul, hsq, map_one])
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hro) dvd_rfl h2)

theorem mem_tBlockP_compl_of_commute' [Finite K] (hK : ringChar K ≠ 2)
    (hker : OKer (oQ (diagGL hw))) {J I : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hI : I = J ∨ I = Jᶜ) (hIc : Iᶜ.Nonempty)
    (hNF : BlockNF w I) (hq : IsQuasisimple (blockP K hw I))
    {r : StatedProj (matrixDerived (oQ (diagGL hw)))}
    (hrx : r ∈ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hrc : ∀ y ∈ blockP K hw I, r * y = y * r) (hro : Odd (orderOf r)) :
    r ∈ tBlockP hw Iᶜ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨B, rfl⟩ := projH_surjective r
  have hBiso : (B : GL (Fin d) K) ∈ matrixIsometries (oQ (diagGL hw)) :=
    matrixDerived_le_isometries _ B.2
  have hκ : oκ _ (linPair (B : GL (Fin d) K) hBiso) =
      conjProjH (matrixDerived (oQ (diagGL hw))) ⟨B, B.2⟩ := oκ_linPair_eq_conj hBiso B.2
  have hfix : ∀ y ∈ blockP K hw I, oκ _ (linPair (B : GL (Fin d) K) hBiso) y = y := by
    intro y hy
    rw [hκ, MonoidHom.comp_apply, MulAut.conj_apply]
    change projH _ B * y * (projH _ B)⁻¹ = y
    rw [hrc y hy, mul_inv_cancel_right]
  have ht : oκ _ (linPair (B : GL (Fin d) K) hBiso) (projH _ ⟨signGL K J, hJ⟩) =
      projH _ ⟨signGL K J, hJ⟩ := by
    rw [hκ, MonoidHom.comp_apply, MulAut.conj_apply]
    change projH _ B * _ * (projH _ B)⁻¹ = _
    rw [mem_centralizer_singleton_iff.mp hrx, mul_inv_cancel_right]
  obtain ⟨-, c, hc⟩ := GSThmB.QPUCl.kappa_scalar_on_block hK hw hker hJ hI hIc hNF hq hfix ht
  simp only [linPair_left] at hc
  have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
    (matrixDerived_le_isometryGroup hw h2 B.2)
  obtain ⟨i₀, hi₀⟩ : I.Nonempty := by
    rcases hNF with ⟨I₀, hI₀, hI₀3, -, -⟩
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < I₀.card)
    exact ⟨a, hI₀ ha⟩
  have hc2 : (c : K) * c = 1 := by
    have h := congrFun (congrFun hiso i₀) i₀
    rw [coe_diagGL, Matrix.mul_apply] at h
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.diagonal_apply_eq] at h
    have hcol : ∀ l, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) l i₀ =
        if i₀ = l then (c : K) else 0 :=
      fun l => (hc i₀ hi₀ l).2
    rw [Finset.sum_eq_single i₀ (fun l _ hl => by rw [hcol l, ite_eq_right (Ne.symm hl)]; ring)
      (fun h => absurd (Finset.mem_univ _) h), hcol i₀, ite_eq_left rfl] at h
    have h' : (c : K) * c * w i₀ = 1 * w i₀ := by linear_combination h
    exact mul_right_cancel₀ (hw i₀) h'
  set m := orderOf (projH _ B) with hm
  have hBm : projH _ (B ^ m) = 1 := by rw [map_pow, hm, pow_orderOf_eq_one]
  obtain ⟨l, hl⟩ := mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hBm)
  have hBmM : (((B ^ m : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ m := by
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
  have hlc : (l : K) = (c : K) ^ m := by
    have h := P58b3.pow_apply_of_isolated
      (B := ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) (fun i hi j => (hc i hi j).1) m
      i₀ hi₀ i₀
    rw [ite_eq_left rfl, ← hBmM, ← hl, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h
    exact h
  have hcm1 : (c : K) ^ m * c = 1 := by
    obtain ⟨k, hk⟩ := hro
    rw [← pow_succ, hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, sq, hc2, one_pow]
  refine ⟨B * B ^ m, ?_, by rw [map_mul, hBm, mul_one]⟩
  show ((B * B ^ m : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) ∈ oIsoBlock K hw Iᶜ
  rw [mem_oIsoBlock_iff]
  refine ⟨matrixDerived_le_isometryGroup hw h2 (B * B ^ m).2, fun i j hij => ?_⟩
  have hM : (((B * B ^ m : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (l : K) • ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [Subgroup.coe_mul, Units.val_mul, ← hl, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  rw [hM, Matrix.smul_apply, smul_eq_mul, hlc]
  rcases hij with hi | hj
  · have hi' : i ∈ I := by simpa using hi
    rw [(hc i hi' j).1]
    by_cases h : i = j
    · rw [ite_eq_left h, ite_eq_left h, hcm1]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  · have hj' : j ∈ I := by simpa using hj
    rw [(hc j hj' i).2]
    by_cases h : j = i
    · rw [ite_eq_left h, ite_eq_left h.symm, hcm1]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero]

theorem le_tBlockP_compl_of_isSubnormal' [Finite K] (hK : ringChar K ≠ 2)
    (hker : OKer (oQ (diagGL hw))) {J I : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hI : I = J ∨ I = Jᶜ) (hIc : Iᶜ.Nonempty)
    (hNF : BlockNF w I) (hq : IsQuasisimple (blockP K hw I))
    {R : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hRx : R ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hR : (R.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal)
    (hRs : Group.IsSolvable R) (hodd : R ≤ closure {y | y ∈ R ∧ Odd (orderOf y)}) :
    R ≤ tBlockP hw Iᶜ := by
  set C := centralizer ({projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw)))} : Set
    (StatedProj (matrixDerived (oQ (diagGL hw))))) with hC
  have hPC : blockP K hw I ≤ C := blockP_le_centralizer hw J I hI hJ
  have hcomp : CFSG.IsComponent ((blockP K hw I).subgroupOf C) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hPC).symm hq,
      isSubnormal_blockP hw hK J I hI hJ⟩
  have hRs' : Group.IsSolvable (R.subgroupOf C) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hRx).toMonoidHom)
      (subgroupOfEquivOfLe hRx).injective
  have hcomm := (LocalCores.component_solvable_centralizer hRs' hR).1 _ hcomp
  have hrc : ∀ r ∈ R, ∀ y ∈ blockP K hw I, r * y = y * r := by
    intro r hr y hy
    have h := Subgroup.commutator_mem_commutator
      (show (⟨y, hPC hy⟩ : ↥C) ∈ (blockP K hw I).subgroupOf C from mem_subgroupOf.mpr hy)
      (show (⟨r, hRx hr⟩ : ↥C) ∈ R.subgroupOf C from mem_subgroupOf.mpr hr)
    rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact (congrArg Subtype.val h).symm
  refine hodd.trans (closure_le _ |>.mpr ?_)
  rintro y ⟨hyR, hyo⟩
  exact mem_tBlockP_compl_of_commute' hw hK hker hJ hI hIc hNF hq (hRx hyR) (hrc y hyR) hyo

theorem exists_central_involution_of_le_tBlockP' [Finite K] (hK : Nat.card K = 3)
    {I : Finset (Fin d)} (hI4 : I.card = 4) (hIc : Iᶜ.Nonempty)
    (hq : ¬ IsQuasisimple (blockP K hw I))
    {H : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))} (hHI : H ≤ tBlockP hw I)
    (hH : (H.subgroupOf (tBlockP hw I)).IsSubnormal) (hodd : OddGen ↥H) {r} (hr : r ∈ H)
    (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) :
    ∃ s ∈ H, (∀ h ∈ H, s * h = h * s) ∧ orderOf s = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  set A := (oIsoBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) with hA
  set M₂ : Subgroup ↥(oIsoBlock K hw I) :=
    (matrixDerived (oQ (diagGL hw))).subgroupOf (oIsoBlock K hw I) with hM₂
  have hM₂n : M₂.Normal := by
    have hΩn : ((matrixDerived (oQ (diagGL hw))).subgroupOf
        (CatalogueBGraphForm.isometryGroup d K (diagGL hw))).Normal := by
      rw [matrixDerived_oQ h2 _ (diagGL_transpose hw), ← Subgroup.map_subtype_commutator,
        show ((commutator ↥(CatalogueBGraphForm.isometryGroup d K (diagGL hw))).map
          (CatalogueBGraphForm.isometryGroup d K (diagGL hw)).subtype).subgroupOf
            (CatalogueBGraphForm.isometryGroup d K (diagGL hw)) =
          commutator ↥(CatalogueBGraphForm.isometryGroup d K (diagGL hw)) from
          Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _]
      infer_instance
    exact normal_subgroupOf_of_le hΩn (matrixDerived_le_isometryGroup hw h2) (oIsoBlock_le hw I)
  have hinjA : Function.Injective ((projH (matrixDerived (oQ (diagGL hw)))).comp A.subtype) :=
    fun x y hxy => Subtype.ext (projH_inj_of_mem_oIsoBlock hw hIc (mem_subgroupOf.mp x.2)
      (mem_subgroupOf.mp y.2) hxy)
  let ψ₁ : ↥A ≃* ↥(tBlockP hw I) := (MonoidHom.ofInjective hinjA).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))
  let ψ₂ : ↥A ≃* ↥(oIsoBlock K hw I ⊓ matrixDerived (oQ (diagGL hw))) :=
    (A.equivMapOfInjective (matrixDerived (oQ (diagGL hw))).subtype
      (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype _ _))
  let ψ₃ : ↥M₂ ≃* ↥(oIsoBlock K hw I ⊓ matrixDerived (oQ (diagGL hw))) :=
    (M₂.equivMapOfInjective _ (oIsoBlock K hw I).subtype_injective).trans
      (MulEquiv.subgroupCongr ((subgroupOf_map_subtype _ _).trans (inf_comm _ _)))
  let ψ : ↥(tBlockP hw I) ≃* ↥M₂ := (ψ₁.symm.trans ψ₂).trans ψ₃.symm
  set H₃ : Subgroup ↥M₂ := (H.subgroupOf (tBlockP hw I)).map ψ.toMonoidHom with hH₃
  have hHe : ↥H ≃* ↥H₃ := (subgroupOfEquivOfLe hHI).symm.trans
    ((H.subgroupOf (tBlockP hw I)).equivMapOfInjective _ ψ.injective)
  obtain ⟨eP⟩ := nonempty_projBlock_equiv hw h2 hIc (le_refl (omegaI hw I))
  rw [← blockP_eq_projBlock] at eP
  have hq' : ¬ IsQuasisimple (Burgoyne.C.omegaR (diagGL (wRes_ne_zero hw I))) := fun h =>
    hq (LocalCores.isQuasisimple_of_mulEquiv eP.symm h)
  set r₀ : ↥(tBlockP hw I) := ⟨r, hHI hr⟩ with hr₀
  have hr₀1 : r₀ ≠ 1 := fun h => hr1 (congrArg Subtype.val h)
  obtain ⟨s₀, hs₀, hs₀c, hs₀2⟩ := P58b3.exists_central_involution_of_normal_four hK hI4
    (diagGL (wRes_ne_zero hw I)) (diagGL_transpose (wRes_ne_zero hw I)) hq'
    (oIsoBlockEquiv hw I).symm (M := M₂) (H := H₃) (hH.map ψ.surjective)
    (hodd.of_surjective (f := hHe.toMonoidHom) hHe.surjective) (r := ψ r₀)
    (Subgroup.mem_map_of_mem ψ.toMonoidHom (mem_subgroupOf.mpr hr))
    (by rw [← map_pow, show r₀ ^ 3 = 1 from Subtype.ext (by simpa using hr3), map_one])
    (fun h => hr₀1 (ψ.injective (h.trans (map_one ψ).symm)))
  obtain ⟨t, ht, rfl⟩ := hs₀
  refine ⟨t, mem_subgroupOf.mp ht, fun h hh => ?_, ?_⟩
  · have hc := hs₀c (ψ ⟨h, hHI hh⟩) ⟨⟨h, hHI hh⟩, mem_subgroupOf.mpr hh, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul] at hc
    exact congrArg Subtype.val (ψ.injective hc)
  · rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ]
    exact hs₀2

end P58b3L

end CFSG.ComponentClassification.HarrisLit.T1
