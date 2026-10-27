module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSixB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaForms

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem FiveList.lieModel_of_equiv_psl_two {M : Type} [Group M] {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hF : Nat.card F = p ^ e) (hF2 : Nat.card F ≠ 2)
    (hF3 : Nat.card F ≠ 3) (E : M ⧸ center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    StatedLieAdmissible .PSL 2 p e ∧ LieModel (M ⧸ center M) .PSL 2 p e := by
  have hadm : StatedLieAdmissible .PSL 2 p e :=
    ⟨hp, he, le_rfl, fun h => hF2 (hF.trans (Prod.mk.inj h).2),
      fun h => hF3 (hF.trans (Prod.mk.inj h).2)⟩
  exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv E.symm
    (Or.inl ⟨by decide, ⟨hadm, F, inferInstance, inferInstance, hF,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 2 F⟩⟩⟩)⟩

theorem FiveList.five_pow_ne_three (e : ℕ) : 5 ^ e ≠ 3 := by
  intro h
  rcases e with _ | e
  · norm_num at h
  · have : 5 ≤ 5 ^ (e + 1) := Nat.le_self_pow (by omega) 5
    omega

theorem FiveList.odd_five_pow (e : ℕ) : Odd (5 ^ e) := Odd.pow (by decide)

@[expose] def OddFiveOrthHighWittInput : Prop :=
  ∀ (k W : Type) [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (e : ℕ), 1 ≤ e → Nat.card k = 5 ^ e → ∀ Q₀ : QuadraticForm k W,
    Q₀.polarBilin.Nondegenerate →
    (∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0) →
    ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀), IsComponent M →
      ¬ LieModel (M ⧸ center M) .PSL 2 2 2

section HighWittModels

open CFSG.ComponentClassification.CatLeafProof CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.Classical2

theorem FiveList.orthogonal_derived_lieModel_ne_PSL {k W : Type} [Field k] [Finite k]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] {p e n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 2 * n + 1 ∧ 3 ≤ n ∨ Module.finrank k W = 2 * n ∧ 4 ≤ n) :
    IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)) ∧
      ∃ (τ' : StatedLieTag) (n' : ℕ), τ' ≠ .PSL ∧ StatedLieAdmissible τ' n' p e ∧
        Blueprint.LieModel (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀) ⧸
          center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀))) τ' n' p e := by
  have : CharP k p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hk
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq k p]; exact hp2)
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  obtain ⟨hm3, τ', n', htag, hne, hadm, hstated⟩ : 3 ≤ m ∧ ∃ (τ' : StatedLieTag) (n' : ℕ),
      τ' ∈ Blueprint.classicalTags ∧ τ' ≠ .PSL ∧ StatedLieAdmissible τ' n' p e ∧
        StatedClassicalModel (ProjOrthDerived Q₀) τ' n' p e := by
    rcases hdim with ⟨hd, hn⟩ | ⟨hd, hn⟩
    ·
      have hδ1 : δ = 1 := by omega
      have hmn : m = n := by omega
      have H' : HypSplit Q₀ n 1 := by rw [← hmn, ← hδ1]; exact H
      have hα : Q₀ (H'.b (.inr (.inr 0))) ≠ 0 := H'.Q_tail_one_ne_zero
      let u : kˣ := Units.mk0 _ hα
      have hu : (u : k) = Q₀ (H'.b (.inr (.inr 0))) := rfl
      let bk := (H'.scaled u).reindex (HypSplit.oddEquiv n)
      have e1 := projOrthDerivedEquiv (Q₁ := CFSG.LieType.Universal.Spin.quadOdd n k)
        bk.equivFun u⁻¹ (fun w => by
          rw [show (CFSG.LieType.Universal.Spin.quadOdd n k) (bk.equivFun w) =
            StatedQuadOdd n k (bk.equivFun w) from
            congrFun (CFSG.LieType.Universal.Spin.coe_quadOdd n k) _]
          exact H'.displayOdd u hu w)
      exact ⟨by omega, .POmegaOdd, n, by decide, by decide, ⟨hp, he, hn, hp2⟩, ⟨hp, he, hn, hp2⟩, k,
        inferInstance, inferInstance, hk, ⟨e1.trans
          (CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
            (CFSG.LieType.Universal.Spin.coe_quadOdd n k)).some.symm⟩⟩
    · rcases (show δ = 0 ∨ δ = 2 by omega) with hδ0 | hδ2
      ·
        have hmn : m = n := by omega
        have H' : HypSplit Q₀ n 0 := by rw [← hmn, ← hδ0]; exact H
        let bk := H'.b.reindex (HypSplit.plusEquiv n)
        have e1 := projOrthDerivedEquiv (Q₁ := CFSG.LieType.Universal.Spin.quadPlus n k)
          bk.equivFun 1 (fun w => by
            rw [show (CFSG.LieType.Universal.Spin.quadPlus n k) (bk.equivFun w) =
              StatedQuadPlus n k (bk.equivFun w) from
              congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus n k) _, Units.val_one, one_mul]
            exact H'.displayPlus w)
        exact ⟨by omega, .POmegaPlus, n, by decide, by decide, ⟨hp, he, hn⟩, ⟨hp, he, hn⟩, k,
          inferInstance, inferInstance, hk, ⟨e1.trans
            (CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
              (CFSG.LieType.Universal.Spin.coe_quadPlus n k)).some.symm⟩⟩
      ·
        have hmn : m = n - 1 := by omega
        have H' : HypSplit Q₀ (n - 1) 2 := by rw [← hmn, ← hδ2]; exact H
        have hα : Q₀ (H'.b (.inr (.inr 0))) ≠ 0 := H'.Q_tail_two_ne_zero
        let u : kˣ := Units.mk0 _ hα
        have hu : (u : k) = Q₀ (H'.b (.inr (.inr 0))) := rfl
        let t₀ := H'.b (.inr (.inr 0))
        let t₁ := H'.b (.inr (.inr 1))
        let b' : k := ((u⁻¹ : kˣ) : k) * QuadraticMap.polar Q₀ t₀ t₁
        let c' : k := ((u⁻¹ : kˣ) : k) * Q₀ t₁
        have hroot : ∀ r : k, r ^ 2 + b' * r + c' ≠ 0 := by
          intro r hr
          have h1 : Q₀ (∑ j, (![r, 1] : Fin 2 → k) j • H'.b (.inr (.inr j))) = 0 := by
            rw [H'.tail_two]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
            have h2 : (u : k) * (r ^ 2 + b' * r + c') = 0 := by rw [hr, mul_zero]
            have h3 : (u : k) * (r ^ 2 + b' * r + c') =
                r ^ 2 * Q₀ t₀ + 1 ^ 2 * Q₀ t₁ + r * 1 * QuadraticMap.polar Q₀ t₀ t₁ := by
              have h4 : (u : k) * ((u⁻¹ : kˣ) : k) = 1 := Units.mul_inv u
              simp only [b', c']
              rw [hu] at h4 ⊢
              linear_combination (Q₀ t₁ + r * QuadraticMap.polar Q₀ t₀ t₁) * h4
            rw [← h3]
            exact h2
          have h5 := H'.aniso _ h1
          exact one_ne_zero (congrFun h5 1)
        let bk := H'.scaled u
        have e1 := projOrthDerivedEquiv (Q₁ := CFSG.LieType.Universal.Spin.quadMinus n k b' c')
          bk.equivFun u⁻¹ (fun w => by
            rw [show (CFSG.LieType.Universal.Spin.quadMinus n k b' c') (bk.equivFun w) =
              StatedQuadMinus n k b' c' (bk.equivFun w) from
              congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus n k b' c') _]
            exact H'.displayMinus u hu w)
        exact ⟨by omega, .POmegaMinus, n, by decide, by decide, ⟨hp, he, hn⟩, ⟨hp, he, hn⟩, k,
          inferInstance, inferInstance, hk, b', c', hroot, ⟨e1.trans
            (CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
              (CFSG.LieType.Universal.Spin.coe_quadMinus n k b' c')).some.symm⟩⟩
  obtain ⟨T, hT, hTQ⟩ := H.exists_totallySingular_three hm3
  have hq := (CatalogueBOrthogonal.high_Witt_orthogonal_p_components Q₀ h2 hQ₀ hT.ge hTQ).1
  have : IsSimpleGroup (ProjOrthDerived Q₀) :=
    (LieType.Simplicity.fam_classical_converse _ ⟨τ', n', p, e, hstated⟩).2.2
  obtain ⟨eP⟩ := nonempty_centerQuotient_equiv_projOrthDerived Q₀ hq
  exact ⟨hq, τ', n', hne, hadm, LieType.CurtisTits.lieModel_of_mulEquiv eP.symm
    (Or.inl ⟨htag, hstated⟩)⟩

end HighWittModels

section KleinModels

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeafProof.KleinSix
  CFSG.ComponentClassification.CatalogueBOrthogonal CFSG.RankThree.PartOne.KCOrthogonalDescent

theorem FiveList.lieModel_quadPlus_three_component {K : Type} [Field K] [Finite K] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))}
    (hM : CFSG.IsComponent M) :
    StatedLieAdmissible .PSL 4 p e ∧ LieModel (M ⧸ Subgroup.center M) .PSL 4 p e := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hq := derived_quasisimple (quadPlus 3 K) h2 quadPlus_nondegenerate finrank_singularT.ge
    singularT_singular
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  have hmap := derived_map_eq_elementary (quadPlus 3 K) h2 quadPlus_nondegenerate
    finrank_singularT.ge singularT_singular
  have hrange := range_eq_elementaryGroup (K := K) h2
  let eD : commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) ≃*
      (rhoGL (K := K)).range :=
    ((commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))).equivMapOfInjective
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)).subtype
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)).subtype_injective).trans
      (MulEquiv.subgroupCongr (hmap.trans hrange.symm))
  let eM : M ≃* (rhoGL (K := K)).range := (MulEquiv.subgroupCongr hMeq).trans eD
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 4 K (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hrq : CFSG.IsQuasisimple (rhoGL (K := K)).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eD hq
  obtain ⟨eS⟩ := CatLeafProof.nonempty_centerQuotient_equiv_range hSL rhoGL
    (CatLeafProof.ne_bot_of_isQuasisimple hrq)
  let eTot : M ⧸ Subgroup.center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
    (QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)).trans eS.symm
  have hadm : StatedLieAdmissible .PSL 4 p e :=
    ⟨hp, he, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  exact ⟨hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 4 K⟩⟩⟩)⟩

theorem FiveList.lieModel_split_six_component {k W : Type} [Field k] [Finite k]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 6)
    (hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀)} (hM : CFSG.IsComponent M) :
    StatedLieAdmissible .PSL 4 p e ∧ LieModel (M ⧸ Subgroup.center M) .PSL 4 p e := by
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  have hwitt := H.sourceWittIndex_eq hQ₀
  obtain ⟨T, hTdim, hTQ⟩ := hT
  have h3 := CFSG.Blueprint.EvenSource.le_sourceWittIndex (K := k) (V := W) (⇑Q₀) (W := T) hTQ
  have hm : m = 3 := by omega
  have hδ0 : δ = 0 := by omega
  have H' : HypSplit Q₀ 3 0 := by rw [← hm, ← hδ0]; exact H
  let bk := H'.b.reindex (HypSplit.plusEquiv 3)
  have hS : ∀ w, quadPlus 3 k (bk.equivFun w) = ((1 : kˣ) : k) * Q₀ w := fun w => by
    rw [Units.val_one, one_mul, show quadPlus 3 k (bk.equivFun w) =
      StatedQuadPlus 3 k (bk.equivFun w) from congrFun (coe_quadPlus 3 k) _]
    exact H'.displayPlus w
  let eO : TauCeti.QuadraticMap.orthogonalGroup Q₀ ≃*
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k) :=
    ((TauCeti.QuadraticMap.orthogonalGroup Q₀).equivMapOfInjective
      (linConj bk.equivFun).toMonoidHom (linConj bk.equivFun).injective).trans
      (MulEquiv.subgroupCongr (map_orthogonalGroup bk.equivFun 1 hS))
  have hM' := CFSG.LocalCores.isComponent_map_mulEquiv eO hM
  obtain ⟨hadm, hmod⟩ := FiveList.lieModel_quadPlus_three_component hp hp2 he hk hM'
  exact ⟨hadm, FiveList.lieModel_centerQuotient_of_mulEquiv
    (M.equivMapOfInjective eO.toMonoidHom eO.injective).symm hmod⟩

end KleinModels

@[expose] def OddFiveL45SplitInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 5 → ∀ A : GL (Fin 4) K,
    (A : Matrix (Fin 4) (Fin 4) K).transpose = A →
    (∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm A⁻¹ x = 0) →
    orderOf (CatalogueBGraphForm.pureGraphAction 4 K A) = 2 →
      32 ∣ Nat.card (fixedSubgroup (CatalogueBGraphForm.pureGraphAction 4 K A))

section Orth


variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

open LocalAnalysis.ComponentInitial CatalogueBOrthogonal in
theorem eq_one_of_orth_three {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 5 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 3)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 2 2 2) : e = 1 := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact FiveList.odd_five_pow e
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hK3 : Nat.card K ≠ 3 := by rw [hK]; exact FiveList.five_pow_ne_three e
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived hodd hK3 Q hQ hdim
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2) (Or.inr hK3))
    (traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* _))
    (traceZeroSpecialImage_quasisimple hK2 hK3) (hMeq.trans hcomm)
  obtain ⟨hadm, hmod⟩ := FiveList.lieModel_of_equiv_psl_two (by norm_num) he hK hK2 hK3 E
  obtain ⟨-, -, h5⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
  exact eq_one_of_five_pow_eq_five h5

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit in
theorem eq_one_of_orth_split_four {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 5 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 2 2 2) : e = 1 := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact FiveList.odd_five_pow e
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hK3 : Nat.card K ≠ 3 := by rw [hK]; exact FiveList.five_pow_ne_three e
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, hperf, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  have hMD : M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp hM.1.1).symm
      _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  have key : ∀ E : M ⧸ center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, e = 1 := by
    intro E
    obtain ⟨hadm, hmod⟩ := FiveList.lieModel_of_equiv_psl_two (by norm_num) he hK hK2 hK3 E
    obtain ⟨-, -, h5⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
    exact eq_one_of_five_pow_eq_five h5
  rcases CatLeafProof.eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hM hMD with h | h
  · obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inl _ _)) (determinantLeftFactor_quasisimple hK2 hK3)
      h
    exact key E
  · obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inr _ _))
      (determinantRightFactor_quasisimple hK2 hK3) h
    exact key E

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourNonsplit in
theorem false_of_orth_nonsplit_four {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 5 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hno : ¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 2 2 2) : False := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact FiveList.odd_five_pow e
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hns, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_four_derived hodd Q hQ hdim hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  have hcard := extension_card (δ : K)
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hE2 : Nat.card (extension (δ : K)) ≠ 2 := by
    rw [hcard]
    nlinarith
  have hE3 : Nat.card (extension (δ : K)) ≠ 3 := by
    rw [hcard]
    nlinarith
  obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension (δ : K)) le_rfl (Or.inr hE2)
      (Or.inr hE3)) (specialRho (δ : K) h2) (hermitianSpecialImage_quasisimple (δ : K) h2)
    (hMeq.trans hcomm)
  have hE : Nat.card (extension (δ : K)) = 5 ^ (2 * e) := by
    rw [hcard, hK, ← pow_mul, mul_comm]
  obtain ⟨hadm, hmod⟩ := FiveList.lieModel_of_equiv_psl_two (by norm_num) (by omega) hE hE2 hE3 E
  obtain ⟨-, -, h5⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
  have := eq_one_of_five_pow_eq_five h5
  omega

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFive in
theorem false_of_orth_five {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 5 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 5)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 2 2 2) : False := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact FiveList.odd_five_pow e
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q hQ hdim
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e'
    (symplecticKernel_quasisimple hodd) (selfAdjointSymplecticAction h2)
    (selfAdjointSymplecticImage_quasisimple hodd) (hMeq.trans hcomm)
  have hadm : StatedLieAdmissible .PSp 2 5 e := by
    refine ⟨by norm_num, he, le_rfl, fun h => ?_⟩
    have h1 : 5 ^ e = 2 := (Prod.mk.inj h).2
    rw [← hK] at h1
    exact absurd (h1 ▸ hodd) (by decide)
  let eSp := symplecticKernelEquivFin.trans (LieType.Universal.Symplectic.equivStatedSp 2 K)
  let eTot := E.trans (QuotientGroup.congr _ _ eSp (Subgroup.map_center_eq eSp))
  have hmod : LieModel (M ⧸ center M) .PSp 2 5 e :=
    LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
      (Or.inl ⟨by decide,
        LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 K hadm hK⟩)
  obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
  exact absurd h1 (by decide)

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourNonsplit CatalogueBOrthogonalSix in
theorem false_of_orth_nonsplit_six {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 5 ^ e)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 6)
    (hno : ¬ ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 2 2 2) : False := by
  have hp : (5 : ℕ).Prime := by norm_num
  have hodd : Odd (Nat.card K) := by rw [hK]; exact FiveList.odd_five_pow e
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hfact, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_six_derived hodd Q hQ hdim hno
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_eq_map e'
    (sixSpecialUnitary_quasisimple (δ : K) h2) (sixSpecialKappa (δ : K) h2)
    (sixSpecialImage_quasisimple (δ : K) h2) (hMeq.trans hcomm)
  obtain ⟨eU⟩ := exists_six_special_unitary_equiv (δ : K) h2
  have hcardE : Nat.card (extension (δ : K)) = 5 ^ (2 * e) := by
    rw [extension_card, hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData 5 e (extension (δ : K)) := ⟨hp, he, hcardE⟩
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have : CharP (extension (δ : K)) 5 := hU.charP
  have hF : Nat.card (extension (δ : K)) = (5 ^ e) ^ 2 := by
    rw [hcardE, ← pow_mul, mul_comm]
  have hσ2 : (conjugation (δ : K)).toRingEquiv * (conjugation (δ : K)).toRingEquiv = 1 := by
    rw [← pow_two]
    exact conjugation_square (δ : K)
  have hconj : (conjugation (δ : K)).toRingEquiv =
      LieType.BorelTits.unitaryInvolution (extension (δ : K)) 5 e := by
    rcases UnitaryHigher.ringEquiv_eq_refl_or_bar hU hσ2 with h | h
    · exact absurd h (conjugation_ne_one (δ : K) h2)
    · exact RingEquiv.ext fun c =>
        (h c).trans (LieType.BorelTits.unitaryInvolution_apply _ 5 e c).symm
  have hSU : LieType.Universal.Unitary.SUid (conjugation (δ : K)).toRingEquiv 4 =
      StatedSU 4 (5 ^ e) (extension (δ : K)) := by
    rw [hconj]
    exact LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  have hnq : ((4 : ℕ), 5 ^ e) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  obtain ⟨-, hZ⟩ := LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF (by norm_num) hnq
  let eSU := eU.trans (MulEquiv.subgroupCongr hSU)
  let eTot := E.trans ((QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq eSU)).trans
    (QuotientGroup.quotientMulEquivOfEq hZ))
  have hadm : StatedLieAdmissible .PSU 4 5 e := ⟨hp, he, by norm_num, hnq⟩
  have hmod : LieModel (M ⧸ center M) .PSU 4 5 e :=
    LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
      (Or.inl ⟨by decide, ⟨hadm, extension (δ : K), inferInstance, inferInstance, hF,
        ⟨MulEquiv.refl _⟩⟩⟩)
  obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
  exact absurd h1 (by decide)

theorem oddFiveOrthComponentInput_of_highWitt (h : OddFiveOrthHighWittInput) :
    OddFiveOrthComponentInput := by
  intro k W _ _ _ _ _ e he hk Q₀ hQ₀ h3 M hM hMm
  have hodd : Odd (Nat.card k) := by rw [hk]; exact FiveList.odd_five_pow e
  by_cases hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0
  · exact (h k W e he hk Q₀ hQ₀ hT M hM hMm).elim
  · have hle := CatalogueBOddQuadratic.finrank_le_six_of_no_totallySingular_three hodd Q₀ hQ₀ hT
    rcases (show Module.finrank k W = 3 ∨ Module.finrank k W = 4 ∨ Module.finrank k W = 5 ∨
        Module.finrank k W = 6 by omega) with h' | h' | h' | h'
    · exact ⟨eq_one_of_orth_three he hk Q₀ hQ₀ h' hM hMm, Or.inl h'⟩
    · by_cases hS : ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q₀ x = 0
      · exact ⟨eq_one_of_orth_split_four he hk Q₀ hQ₀ h' hS hM hMm, Or.inr h'⟩
      · exact (false_of_orth_nonsplit_four he hk Q₀ hQ₀ h' hS hM hMm).elim
    · exact (false_of_orth_five he hk Q₀ hQ₀ h' hM hMm).elim
    · exact (false_of_orth_nonsplit_six he hk Q₀ hQ₀ h' hT hM hMm).elim

theorem oddFiveOrthHighWittInput_holds : OddFiveOrthHighWittInput := by
  intro k W _ _ _ _ _ e he hk Q₀ hQ₀ hT M hM hMm
  have hp : (5 : ℕ).Prime := by norm_num
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := RankThree.PartOne.KCOrthogonalDescent.exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  have hwitt := H.sourceWittIndex_eq hQ₀
  obtain ⟨T, hTd, hTQ⟩ := hT
  have h3 := CFSG.Blueprint.EvenSource.le_sourceWittIndex (K := k) (V := W) (⇑Q₀) (W := T) hTQ
  by_cases h6 : Module.finrank k W = 6
  · obtain ⟨hadm, hmod⟩ := FiveList.lieModel_split_six_component hp (by norm_num) he hk Q₀ hQ₀
      h6 ⟨T, hTd, hTQ⟩ hM
    obtain ⟨-, h2, -⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
    omega
  obtain ⟨n, hdim⟩ : ∃ n, (Module.finrank k W = 2 * n + 1 ∧ 3 ≤ n) ∨
      (Module.finrank k W = 2 * n ∧ 4 ≤ n) := by
    rcases Nat.even_or_odd (Module.finrank k W) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨r, Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨r, Or.inl ⟨by omega, by omega⟩⟩
  obtain ⟨hq, τ', n', hne, hadm, hlie⟩ :=
    FiveList.orthogonal_derived_lieModel_ne_PSL hp (by norm_num) he hk Q₀ hQ₀ hdim
  have hMeq := CatLeafProof.eq_commutator_of_isComponent hq hM
  have hmod : LieModel (M ⧸ center M) τ' n' 5 e := LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hMeq.symm) (Subgroup.map_center_eq _)) hlie
  obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
  exact hne h1

theorem oddFiveOrthComponentInput_holds : OddFiveOrthComponentInput :=
  oddFiveOrthComponentInput_of_highWitt oddFiveOrthHighWittInput_holds

theorem oddFivePSLGraphInput_of_L45 (h45 : OddFiveL45GraphInput) : OddFivePSLGraphInput :=
  oddFivePSLGraphInput_of_orth oddFiveOrthComponentInput_holds h45

theorem oddFiveSL2ListFamilyInput_PSL_of_L45 (h45 : OddFiveL45GraphInput) :
    OddFiveSL2ListFamilyInput .PSL :=
  oddFiveSL2ListFamilyInput_PSL_of_graph (oddFivePSLGraphInput_of_L45 h45)

open Matrix in
open CatalogueBGraphForm (glGraphAut glTranspose slGraphAut pureGraphAction) in
open CatalogueBLinearHigherB in
theorem oddFiveL45GraphInput_of_split (hsplit : OddFiveL45SplitInput) : OddFiveL45GraphInput := by
  intro K _ _ hK A hA h
  have hp : (5 : ℕ).Prime := by norm_num
  have hK1 : Nat.card K = 5 ^ 1 := by rw [hK, pow_one]
  have : CharP K 5 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp le_rfl hK1
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K 5]
    norm_num
  have hsq2 : pureGraphAction 4 K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  have hform := CatalogueBGraphForm.pureGraph_involution_form_data 4 K (by norm_num) hodd A hsq2
  set Z := center (SpecialLinearGroup (Fin 4) K)
  set ψ := CatalogueBHigherLinearAction.slConjugation 4 K A * slGraphAut 4 K
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : pureGraphAction 4 K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin 4) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact CatalogueBGraphForm.pureGraphAction_mk 4 K A g
  have hfix : ∀ x : GL (Fin 4) K, A * glGraphAut 4 K x * A⁻¹ = x ↔
      glTranspose 4 K x * A⁻¹ * x = A⁻¹ := by
    intro x
    have hT : glGraphAut 4 K x = (glTranspose 4 K x)⁻¹ := (inv_inv _).symm
    rw [hT]
    constructor
    · intro h
      calc glTranspose 4 K x * A⁻¹ * x =
          glTranspose 4 K x * A⁻¹ * (A * (glTranspose 4 K x)⁻¹ * A⁻¹) := by rw [h]
        _ = A⁻¹ := by group
    · intro h
      calc A * (glTranspose 4 K x)⁻¹ * A⁻¹ =
          A * (glTranspose 4 K x)⁻¹ * (glTranspose 4 K x * A⁻¹ * x) := by rw [h]
        _ = x := by group
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup 4 K A⁻¹ ⊓
        CatalogueBGeneralLinear.specialLinearRange 4 K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
        CatalogueBGraphForm.toGL_slGraphAut] at h1
      exact (hfix _).mp h1
    · intro hy
      obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
        CatalogueBGraphForm.toGL_slGraphAut]
      exact (hfix _).mpr hyI
  have h' := h.of_eq heq
  obtain ⟨L, hL, hLm⟩ := h'.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := FiveList.exists_component_glSubgroup ψ hinv _ hmap hL
  have hNm : LieModel (N ⧸ center N) .PSL 2 2 2 := LieType.CurtisTits.lieModel_of_mulEquiv eN hLm
  rcases hform with hsymm | ⟨halt, -⟩
  · have hR := transpose_inv_of_transpose_eq A hsymm
    by_cases hS : ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
        ∀ x ∈ S, matrixQuadraticForm A⁻¹ x = 0
    · exact h.not_dvd (hsplit K hK A hsymm hS hA)
    · let Φ : CatalogueBGraphForm.isometryGroup 4 K A⁻¹ ≃*
          TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹) :=
        (isometryGroupEquiv A⁻¹).symm.trans
          (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
      have hN' := LocalCores.isComponent_map_mulEquiv Φ hN
      have hN'm := FiveList.lieModel_centerQuotient_of_mulEquiv
        (N.equivMapOfInjective Φ.toMonoidHom Φ.injective) hNm
      exact false_of_orth_nonsplit_four le_rfl hK1 (matrixQuadraticForm A⁻¹)
        (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR)
        (by rw [Module.finrank_fin_fun]) hS hN' hN'm
  · have hR := transpose_inv_of_transpose_eq_neg A halt
    have hB := matrixForm_isAlt hodd A⁻¹ hR
    have hnd := matrixForm_nondegenerate A⁻¹
    obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
      (matrixForm A⁻¹) hB hnd
    obtain ⟨eS⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp (matrixForm A⁻¹) hB hnd hdm
    rw [Module.finrank_fin_fun] at hdm
    let Φ := (isometryGroupEquiv A⁻¹).symm.trans eS
    have hN' := LocalCores.isComponent_map_mulEquiv Φ hN
    have hN'm := FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective Φ.toMonoidHom Φ.injective) hNm
    obtain ⟨hadmS, hmodS⟩ := FiveList.lieModel_of_isComponent_statedSp hp (by norm_num) le_rfl
      hK1 (by omega) hN'
    obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hN'm (by norm_num) hadmS hmodS
    exact absurd h1 (by decide)

theorem oddFiveSL2ListFamilyInput_PSL_of_split (hsplit : OddFiveL45SplitInput) :
    OddFiveSL2ListFamilyInput .PSL :=
  oddFiveSL2ListFamilyInput_PSL_of_L45 (oddFiveL45GraphInput_of_split hsplit)

end Orth

end CFSG.SeitzReduction.RankOne
