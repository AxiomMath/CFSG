module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalComponents
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentAssemble
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentScaled
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.Classical2

theorem nonempty_centerQuotient_equiv_projOrthDerived {k W : Type} [Field k] [AddCommGroup W]
    [Module k W] (Q₀ : QuadraticForm k W)
    (hq : IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)))
    [IsSimpleGroup (ProjOrthDerived Q₀)] :
    Nonempty (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀) ⧸
      center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)) ≃* ProjOrthDerived Q₀) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q₀
  let ι : commutator O ≃* orthDerived Q₀ :=
    ((commutator O).equivMapOfInjective O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [map_commutator_eq, Subgroup.range_subtype]))
  let f₀ : commutator O →* ProjOrthDerived Q₀ :=
    (QuotientGroup.mk' _).comp ι.toMonoidHom
  have hsurj : Function.Surjective f₀ :=
    (QuotientGroup.mk'_surjective _).comp ι.surjective
  have hker : f₀.ker ≤ center (commutator O) := by
    intro x hx
    have hx1 : ι x ∈ (ClassicalGroups.Orthogonal.scalars k W).subgroupOf (orthDerived Q₀) :=
      (QuotientGroup.eq_one_iff _).mp hx
    rw [Subgroup.mem_subgroupOf] at hx1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact (ClassicalGroups.Orthogonal.commute_of_mem_scalars hx1 _).symm
  obtain ⟨e⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hq f₀ hsurj hker
  have hZ : center (ProjOrthDerived Q₀) = ⊥ := by
    rcases (center (ProjOrthDerived Q₀)).normal_of_characteristic.eq_bot_or_eq_top with hc | hc
    · exact hc
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hq
      apply hab
      apply e.injective
      have h1 : ∀ z : ProjOrthDerived Q₀ ⧸ center (ProjOrthDerived Q₀), z = 1 := by
        intro z
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
        exact (QuotientGroup.eq_one_iff y).mpr (hc ▸ Subgroup.mem_top y)
      rw [h1 (e (a * b)), h1 (e (b * a))]
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

theorem orthogonal_derived_lieModel {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {p e n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 2 * n + 1 ∧ 3 ≤ n ∨ Module.finrank k W = 2 * n ∧ 4 ≤ n) :
    IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)) ∧
      ∃ (τ' : StatedLieTag) (n' : ℕ), StatedLieAdmissible τ' n' p e ∧
        Blueprint.LieModel (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀) ⧸
          center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀))) τ' n' p e := by
  have : CharP k p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hk
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq k p]; exact hp2)
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  obtain ⟨hm3, τ', n', htag, hadm, hstated⟩ : 3 ≤ m ∧ ∃ (τ' : StatedLieTag) (n' : ℕ),
      τ' ∈ Blueprint.classicalTags ∧ StatedLieAdmissible τ' n' p e ∧
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
      exact ⟨by omega, .POmegaOdd, n, by decide, ⟨hp, he, hn, hp2⟩, ⟨hp, he, hn, hp2⟩, k,
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
        exact ⟨by omega, .POmegaPlus, n, by decide, ⟨hp, he, hn⟩, ⟨hp, he, hn⟩, k,
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
        exact ⟨by omega, .POmegaMinus, n, by decide, ⟨hp, he, hn⟩, ⟨hp, he, hn⟩, k,
          inferInstance, inferInstance, hk, b', c', hroot, ⟨e1.trans
            (CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
              (CFSG.LieType.Universal.Spin.coe_quadMinus n k b' c')).some.symm⟩⟩
  obtain ⟨T, hT, hTQ⟩ := H.exists_totallySingular_three hm3
  have hq := (CatalogueBOrthogonal.high_Witt_orthogonal_p_components Q₀ h2 hQ₀ hT.ge hTQ).1
  have : IsSimpleGroup (ProjOrthDerived Q₀) :=
    (LieType.Simplicity.fam_classical_converse _ ⟨τ', n', p, e, hstated⟩).2.2
  obtain ⟨eP⟩ := nonempty_centerQuotient_equiv_projOrthDerived Q₀ hq
  exact ⟨hq, τ', n', hadm, LieType.CurtisTits.lieModel_of_mulEquiv eP.symm
    (Or.inl ⟨htag, hstated⟩)⟩

end CFSG.ComponentClassification.CatLeafProof
