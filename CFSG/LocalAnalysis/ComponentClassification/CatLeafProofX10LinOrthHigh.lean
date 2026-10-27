module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSixB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaForms
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinLift

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel)
open CFSG.ComponentClassification.CatLeafProof (eq_commutator_of_isComponent
  not_isComponent_of_isSolvable nonempty_centerQuotient_equiv_range ne_bot_of_isQuasisimple
  nonempty_centerQuotient_equiv_projOrthDerived)

@[expose] def orthTuples (d e : ℕ) : Set (StatedLieTag × ℕ × ℕ) :=
  {x | (d = 3 ∧ x = (.PSL, 2, e)) ∨ (d = 4 ∧ (x = (.PSL, 2, e) ∨ x = (.PSL, 2, 2 * e))) ∨
    (d = 5 ∧ x = (.PSp, 2, e)) ∨ (d = 6 ∧ (x = (.PSL, 4, e) ∨ x = (.PSU, 4, e))) ∨
    (7 ≤ d ∧ Odd d ∧ x = (.POmegaOdd, d / 2, e)) ∨
    (8 ≤ d ∧ Even d ∧ (x = (.POmegaPlus, d / 2, e) ∨ x = (.POmegaMinus, d / 2, e)))}

section Six

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatLeafProof.KleinSix
open CFSG.ComponentClassification.CatalogueBOrthogonal

theorem centralModel_quadPlus_three {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))}
    (hM : IsComponent M) : CentralModel p .PSL 4 e M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hq := derived_quasisimple (quadPlus 3 K) h2 quadPlus_nondegenerate finrank_singularT.ge
    singularT_singular
  have hMeq := eq_commutator_of_isComponent hq hM
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
  have hrq : IsQuasisimple (rhoGL (K := K)).range := LocalCores.isQuasisimple_of_mulEquiv eD hq
  obtain ⟨eS⟩ := nonempty_centerQuotient_equiv_range hSL rhoGL (ne_bot_of_isQuasisimple hrq)
  let eTot : M ⧸ Subgroup.center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
    (QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)).trans eS.symm
  have hadm : StatedLieAdmissible .PSL 4 p e :=
    ⟨hp, he, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 4 K⟩⟩⟩)⟩

open CFSG.RankThree.PartOne.KCOrthogonalDescent in
theorem centralModel_orthogonal_split_six {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 6)
    (hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀)} (hM : IsComponent M) :
    CentralModel p .PSL 4 e M := by
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
  have hM' := LocalCores.isComponent_map_mulEquiv eO hM
  exact (centralModel_quadPlus_three hp hp2 he hk hM').of_mulEquiv
    (M.equivMapOfInjective eO.toMonoidHom eO.injective)

end Six

section Derived

open CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.Classical2

theorem centralModel_orthogonal_derived {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {p e n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 2 * n + 1 ∧ 3 ≤ n ∨ Module.finrank k W = 2 * n ∧ 4 ≤ n) :
    IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)) ∧
      ModelIn p (orthTuples (Module.finrank k W) e)
        (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)) := by
  have : CharP k p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hk
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq k p]; exact hp2)
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  obtain ⟨hm3, τ', n', hT, htag, hadm, hstated⟩ : 3 ≤ m ∧ ∃ (τ' : StatedLieTag) (n' : ℕ),
      (τ', n', e) ∈ orthTuples (Module.finrank k W) e ∧ τ' ∈ Blueprint.classicalTags ∧
        StatedLieAdmissible τ' n' p e ∧ StatedClassicalModel (ProjOrthDerived Q₀) τ' n' p e := by
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
      exact ⟨by omega, .POmegaOdd, n,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, ⟨n, by omega⟩,
          by rw [show Module.finrank k W / 2 = n by omega]⟩)))),
        by decide, ⟨hp, he, hn, hp2⟩, ⟨hp, he, hn, hp2⟩, k,
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
        exact ⟨by omega, .POmegaPlus, n,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ⟨n, by omega⟩,
            Or.inl (by rw [show Module.finrank k W / 2 = n by omega])⟩)))),
          by decide, ⟨hp, he, hn⟩, ⟨hp, he, hn⟩, k,
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
        exact ⟨by omega, .POmegaMinus, n,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ⟨n, by omega⟩,
            Or.inr (by rw [show Module.finrank k W / 2 = n by omega])⟩)))),
          by decide, ⟨hp, he, hn⟩, ⟨hp, he, hn⟩, k,
          inferInstance, inferInstance, hk, b', c', hroot, ⟨e1.trans
            (CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
              (CFSG.LieType.Universal.Spin.coe_quadMinus n k b' c')).some.symm⟩⟩
  obtain ⟨T, hT', hTQ⟩ := H.exists_totallySingular_three hm3
  have hq := (CatalogueBOrthogonal.high_Witt_orthogonal_p_components Q₀ h2 hQ₀ hT'.ge hTQ).1
  have : IsSimpleGroup (ProjOrthDerived Q₀) :=
    (LieType.Simplicity.fam_classical_converse _ ⟨τ', n', p, e, hstated⟩).2.2
  obtain ⟨eP⟩ := nonempty_centerQuotient_equiv_projOrthDerived Q₀ hq
  exact ⟨hq, τ', n', e, hT, hadm, LieType.CurtisTits.lieModel_of_mulEquiv eP.symm
    (Or.inl ⟨htag, hstated⟩)⟩

end Derived

theorem orthogonal_component_models {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k W : Type}
    [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W] {e : ℕ}
    (he : 1 ≤ e) (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W)
    (hQ₀ : Q₀.polarBilin.Nondegenerate) (h3 : 3 ≤ Module.finrank k W)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀)} (hM : IsComponent M) :
    ModelIn p (orthTuples (Module.finrank k W) e) M := by
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  by_cases hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0
  · by_cases h6 : Module.finrank k W = 6
    · exact ModelIn.of_centralModel (Or.inr (Or.inr (Or.inr (Or.inl ⟨h6, Or.inl rfl⟩))))
        (centralModel_orthogonal_split_six hp hp2 he hk Q₀ hQ₀ h6 hT hM)
    obtain ⟨m, δ, hδ, ⟨H⟩⟩ := RankThree.PartOne.KCOrthogonalDescent.exists_regular_split Q₀ hQ₀
    have hfin := H.finrank_eq
    have hwitt := H.sourceWittIndex_eq hQ₀
    obtain ⟨T, hTd, hTQ⟩ := hT
    have h3' := CFSG.Blueprint.EvenSource.le_sourceWittIndex (K := k) (V := W) (⇑Q₀) (W := T)
      hTQ
    obtain ⟨n, hdim⟩ : ∃ n, (Module.finrank k W = 2 * n + 1 ∧ 3 ≤ n) ∨
        (Module.finrank k W = 2 * n ∧ 4 ≤ n) := by
      rcases Nat.even_or_odd (Module.finrank k W) with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact ⟨r, Or.inr ⟨by omega, by omega⟩⟩
      · exact ⟨r, Or.inl ⟨by omega, by omega⟩⟩
    obtain ⟨hq, hm⟩ := centralModel_orthogonal_derived hp hp2 he hk Q₀ hQ₀ hdim
    have hMeq := eq_commutator_of_isComponent hq hM
    exact hm.of_mulEquiv (MulEquiv.subgroupCongr hMeq)
  ·
    have hle := CatalogueBOddQuadratic.finrank_le_six_of_no_totallySingular_three hodd Q₀ hQ₀ hT
    rcases (show Module.finrank k W = 3 ∨ Module.finrank k W = 4 ∨ Module.finrank k W = 5 ∨
        Module.finrank k W = 6 by omega) with h | h | h | h
    · exact ModelIn.of_centralModel (Or.inl ⟨h, rfl⟩)
        (centralModel_orthogonal_three hp hp2 he hk Q₀ hQ₀ h hM)
    · by_cases hS : ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q₀ x = 0
      · exact ModelIn.of_centralModel (Or.inr (Or.inl ⟨h, Or.inl rfl⟩))
          (centralModel_orthogonal_split_four hp hp2 he hk Q₀ hQ₀ h hS hM)
      · exact ModelIn.of_centralModel (Or.inr (Or.inl ⟨h, Or.inr rfl⟩))
          (centralModel_orthogonal_nonsplit_four hp hp2 he hk Q₀ hQ₀ h hS hM)
    · exact ModelIn.of_centralModel (Or.inr (Or.inr (Or.inl ⟨h, rfl⟩)))
        (centralModel_orthogonal_five hp hp2 he hk Q₀ hQ₀ h hM)
    · exact ModelIn.of_centralModel (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, Or.inr rfl⟩))))
        (centralModel_orthogonal_nonsplit_six hp hp2 he hk Q₀ hQ₀ h hT hM)

end CFSG.ComponentClassification.CatLeafProof.X10Lin
