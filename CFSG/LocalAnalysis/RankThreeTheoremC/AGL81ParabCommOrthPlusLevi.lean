module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferLevi
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

open Matrix QuadraticMap CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise commutatorElement MatrixGroups
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
open CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab
  (normal_eq_top_or_le_center not_isSolvable_of_isQuasisimple)

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

section LeviKer

variable {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ} (ht : t = 0 ∨ t ∈ D) (htm : t + m = r)

@[expose] noncomputable def leviKer : Subgroup ↥(plusFlagStab K r D) :=
  (⨅ b : ↥D, (plusEBlockHom hD b.2).ker) ⊓ (plusResBlockHom hD ht htm).ker

variable {hD ht htm}

theorem mem_leviKer {g : ↥(plusFlagStab K r D)} :
    g ∈ leviKer hD ht htm ↔ (∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb g = 1) ∧
      plusResBlockHom hD ht htm g = 1 := by
  simp only [leviKer, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subtype.forall]

theorem leviKer_normal : (leviKer (K := K) hD ht htm).Normal := by
  haveI h1 : (⨅ b : ↥D, (plusEBlockHom (K := K) hD b.2).ker).Normal :=
    Subgroup.normal_iInf_normal fun b => MonoidHom.normal_ker _
  haveI h2 := MonoidHom.normal_ker (plusResBlockHom (K := K) hD ht htm)
  exact Subgroup.normal_inf_normal _ _

theorem isPGroup_leviKer (hD1 : ∀ d ∈ D, 1 ≤ d) (hDt : ∀ d ∈ D, d ≤ t) :
    IsPGroup 2 (leviKer (K := K) hD ht htm) := by
  have hsup : D.sup id = t := sup_id_eq ht hDt
  refine isPGroup_of_plusBlocks hD hD1 fun g hg => ⟨fun b hb => (mem_leviKer.1 hg).1 b hb,
    fun x hx => ?_⟩
  rw [hsup] at hx ⊢
  exact sub_mem_of_plusResBlockHom_eq_one hD ht htm (mem_leviKer.1 hg).2 hx

end LeviKer

section Normal

variable {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ} (ht : t = 0 ∨ t ∈ D) (htm : t + m = r)
  (R : Subgroup ↥(plusFlagStab K r D)) [R.Normal] (hR : IsPGroup 2 R)

include hR in
theorem le_ker_plusEBlockHom_of_normal (hr : 3 ≤ r) {b : ℕ} (hb : b ∈ D) :
    R ≤ (plusEBlockHom hD hb).ker := by
  have hT : R.map (plusEBlockHom hD hb) = ⊥ := by
    refine Lin.eq_bot_of_isPGroup_of_normalized_range_toGL (hR.map _) ?_
    rintro s hs _ ⟨r', hr', rfl⟩
    obtain ⟨q, hq1, -, -⟩ := exists_plusFlagLevi_of_mem hr hD hb hs
    refine ⟨q * r' * q⁻¹, Subgroup.Normal.conj_mem inferInstance r' hr' q, ?_⟩
    rw [map_mul, map_mul, map_inv, hq1]
  intro r' hr'
  have h : plusEBlockHom hD hb r' ∈ R.map (plusEBlockHom hD hb) := ⟨r', hr', rfl⟩
  rw [hT] at h
  exact h

include hR in
theorem plusResAut_eq_one_of_normal_three (hDt : ∀ d ∈ D, d ≤ t) (hm : 3 ≤ m) :
    ∀ q ∈ R, plusResAut hD ht htm q = 1 := by
  set Em := orthElementaryGroup (quadPlus m K) with hEm
  set T : Subgroup (GLV m K) := R.map (plusResAut hD ht htm) with hT
  have hT2 : IsPGroup 2 T := hR.map _
  have hTO : ∀ t' ∈ T, t' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) := by
    rintro _ ⟨q, -, rfl⟩
    exact plusResAut_mem_orthogonalGroup hD ht htm q
  have hTE : ∀ e ∈ Em, ∀ t' ∈ T, e * t' * e⁻¹ ∈ T := by
    intro e he t' ht'
    obtain ⟨q, hq, rfl⟩ := ht'
    have hqe : plusResExt K htm e ∈ plusFlagStab K r D :=
      plusResExt_mem_plusFlagStab htm hm hDt he
    refine ⟨⟨plusResExt K htm e, hqe⟩ * q * ⟨plusResExt K htm e, hqe⟩⁻¹,
      Subgroup.Normal.conj_mem inferInstance q hq _, ?_⟩
    rw [map_mul, map_mul, map_inv, plusResAut_plusResExt hD ht htm hqe]
  have hcomm : ∀ t' ∈ T, ∀ e ∈ Em, t' * e * t'⁻¹ * e⁻¹ = 1 := by
    intro t' ht' e he
    have hcE : t' * e * t'⁻¹ * e⁻¹ ∈ Em :=
      mul_mem (conj_mem_orthElementaryGroup (hTO t' ht') he) (inv_mem he)
    have hcT : t' * e * t'⁻¹ * e⁻¹ ∈ T := by
      have h1 : e * t'⁻¹ * e⁻¹ ∈ T := hTE e he _ (inv_mem ht')
      have h2 := mul_mem ht' h1
      simpa [mul_assoc] using h2
    let N' : Subgroup ↥Em := T.subgroupOf Em
    haveI hN' : N'.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hTE g.1 g.2 n.1 hn⟩
    have hN'2 : IsPGroup 2 N' := hT2.comap_subtype
    obtain ⟨hQ, hZ⟩ := isQuasisimple_plusElementary (K := K) hm
    rcases normal_eq_top_or_le_center hQ hN' with htop | hc
    · exfalso
      have hP : IsPGroup 2 ↥Em := by
        have := hN'2
        rw [htop] at this
        exact this.of_equiv Subgroup.topEquiv
      haveI : Finite ↥Em := finite_orthElementaryGroup
      haveI := hP.isNilpotent
      exact not_isSolvable_of_isQuasisimple hQ inferInstance
    · have hmem : (⟨_, hcE⟩ : ↥Em) ∈ N' := Subgroup.mem_subgroupOf.2 hcT
      have := hc hmem
      rw [hZ, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
  intro q hq
  have ht1 : plusResAut hD ht htm q ∈ T := ⟨q, hq, rfl⟩
  set t' := plusResAut hD ht htm q with ht'
  have hcommMat : ∀ a b : Fin m ⊕ Fin m, coordIdx a ≠ coordIdx b →
      autMat t' * rpMat K a b = rpMat K a b * autMat t' := by
    intro a b hab
    have h1 := hcomm t' ht1 (rpElt a b 1) (eichler_mem_elementaryGroup _ _ _)
    have h2 : t' * rpElt a b 1 = rpElt a b 1 * t' := commutatorElement_eq_one_iff_mul_comm.1 h1
    have h3 := congrArg autMat h2
    rw [map_mul, map_mul, autMat_rpElt hab, one_smul] at h3
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h3
    exact add_left_cancel h3
  obtain ⟨c, hc⟩ := eq_smul_one_of_commute_rpMat (by omega : 2 ≤ m) _ hcommMat
  have hc1 : c = 1 := by
    refine eq_one_of_smul_isometry (m := m) (by omega) fun v => ?_
    have h4 : t' v = c • v := by
      rw [apply_eq_autMat_mulVec, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← h4]
    exact map_of_mem (hTO t' ht1) v
  apply autMat_injective
  rw [hc, hc1, one_smul, map_one]

include hR in
theorem plusResBlockHom_eq_one_of_normal_two (hr : 3 ≤ r) (hD₂ : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2)
    (hDt : ∀ d ∈ D, d ≤ t) (ht2 : t + 2 = r) :
    ∀ q ∈ R, plusResBlockHom hD ht ht2 q = 1 := by
  have hfam : ∀ j : Fin 2, R ≤ (plusFamHom K hr hD₂ hD ht ht2 j).ker := by
    intro j
    have hT : R.map (plusFamHom K hr hD₂ hD ht ht2 j) = ⊥ := by
      refine Lin.eq_bot_of_isPGroup_of_normalized_range_toGL (hR.map _) ?_
      rintro s hs _ ⟨r', hr', rfl⟩
      obtain ⟨A, rfl⟩ := hs
      obtain ⟨q, hq1⟩ : ∃ q : ↥(plusFlagStab K r D),
          plusFamHom K hr hD₂ hD ht ht2 j q = SpecialLinearGroup.toGL A := by
        fin_cases j
        · have hq := plusResExt_iotaTwo_mem hr ht2 (D := D) hDt A
          exact ⟨⟨_, hq⟩, (plusFamHom_iotaTwo hr hD₂ hD ht ht2 hq).1⟩
        · have hq := plusResExt_iotaOne_mem hr ht2 (D := D) hDt A
          exact ⟨⟨_, hq⟩, (plusFamHom_iotaOne hr hD₂ hD ht ht2 hq).2⟩
      refine ⟨q * r' * q⁻¹, Subgroup.Normal.conj_mem inferInstance r' hr' q, ?_⟩
      rw [map_mul, map_mul, map_inv, hq1]
    intro r' hr'
    have h : plusFamHom K hr hD₂ hD ht ht2 j r' ∈
        R.map (plusFamHom K hr hD₂ hD ht ht2 j) := ⟨r', hr', rfl⟩
    rw [hT] at h
    exact h
  intro q hq
  exact plusResBlockHom_eq_one_of_plusResAut hD ht ht2
    (plusResAut_eq_one_of_plusFamHom hr hD₂ hD ht ht2 (hfam 0 hq) (hfam 1 hq))

include hR in
theorem le_leviKer_of_normal_isPGroup (hr : 3 ≤ r) (hD1 : ∀ d ∈ D, 1 ≤ d)
    (hDt : ∀ d ∈ D, d ≤ t) (hm : m = 0 ∨ 2 ≤ m) : R ≤ leviKer hD ht htm := by
  intro q hq
  refine mem_leviKer.2 ⟨fun b hb => le_ker_plusEBlockHom_of_normal hD R hR hr hb hq, ?_⟩
  rcases hm with rfl | hm2
  · haveI := gl_subsingleton_zero (K := K)
    exact Subsingleton.elim _ _
  · rcases hm2.eq_or_lt with rfl | hm3
    · exact plusResBlockHom_eq_one_of_normal_two hD ht R hR hr
        (fun d hd => ⟨hD1 d hd, by have := hDt d hd; omega⟩) hDt htm q hq
    · exact plusResBlockHom_eq_one_of_plusResAut hD ht htm
        (plusResAut_eq_one_of_normal_three hD ht htm R hR hDt hm3 q hq)

end Normal

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
