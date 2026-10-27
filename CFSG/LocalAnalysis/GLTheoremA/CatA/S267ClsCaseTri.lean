module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsSetup
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutTri
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsTriRankHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcSL2Lift
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaPlus
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseOrth
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Models.Blueprint
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB
open QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData


theorem exists_clsInner_d4_three (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 Q).Valid) {q : ℕ} (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [S.Normal] (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hQq : Q.p = q)
    (e : Nonempty (PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 Q, hv⟩).Group))
    (hB : IsElemAbelian 3 B) (h4 : 3 ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) (hB81 : Nat.card B ≠ 3 ^ 4)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot 3 (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank 3 B) :
    Subgroup.center ↥S = ⊥ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Q.p ^ Q.exponent ∧
        (polarBilin (coordinateQuadPlus 4 K)).Nondegenerate ∧
        (∃ k : ℕ, Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) = 2 ^ k) ∧
        Nonempty (ClsInner 3 S B (matrixDerived (coordinateQuadPlus 4 K))
          (polarBilin (coordinateQuadPlus 4 K))) := by
  classical
  obtain ⟨e⟩ := e
  subst hQq
  set K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 Q, hv⟩) with hKdef
  haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hKc : Nat.card K = Q.p ^ Q.exponent := CFSG.Models.card_fixedField_of
    (TauCeti.LieTypeIndex.characteristic_D 4 Q) (TauCeti.LieTypeIndex.fieldExponent_D 4 Q)
  let e' : PSimple 3 S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 Q hv)
  have hmodel : StatedClassicalModel (PSimple 3 S) .POmegaPlus 4 Q.p Q.exponent :=
    (CFSG.Models.lieModel_D 4 Q hv e).statedClassicalModel (by decide)
  have hK5 : 5 ≤ Nat.card K := by
    rw [hKc]
    have h5 : 5 ≤ Q.p := by
      have := Q.prime_p.two_le
      have hodd := Q.prime_p.odd_of_ne_two hq2
      obtain ⟨k, hk⟩ := hodd
      omega
    exact h5.trans (Nat.le_self_pow Q.exponent_pos.ne' _)
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine BadExc.center_eq_bot_of_multiplier Nat.prime_three hperf hcore e' ?_
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.pomegaPlus_hopfMultiplier
      (n := 4) (by norm_num) hKc (by omega)
    rw [Nat.card_congr eM.toEquiv]
    have hodd : ¬ Even (Q.p ^ Q.exponent) := by
      rw [Nat.not_even_iff_odd]
      exact (Q.prime_p.odd_of_ne_two hq2).pow
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.genericOrders,
      Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, if_neg hodd,
      show Even 4 by decide, if_true]
    norm_num
  have hcard : 3 ^ 5 ≤ Nat.card B := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hB.isPGroup
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [hk] at h4 hB81 ⊢
    have h4' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h4
    have hk4 : k ≠ 4 := fun h => hB81 (by rw [h])
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnot : ¬ (3 ∣ Q.exponent ∧ Nat.card B = 3 ^ 5) := by
    rintro ⟨h3f, hB5⟩
    have hf3 : 3 ≤ Q.exponent := Nat.le_of_dvd Q.exponent_pos h3f
    exact BadExc.false_of_hq_of_lift (r := 6)
      ((BadExc.pRank_le_of_card_le_pow Nat.prime_three hB5.le).trans_lt (by norm_num)) hHq e
      fun X _ _ φ hφ => HqRank.six_le_twoLocalRank_D_field le_rfl Q hv hq2 hf3 φ hφ
  have hBC' : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = 3 := by
    rw [← ModelGen.inf_centMod_eq_inf_centralizer inferInstance hcore]
    exact hBC
  have hBE := ModelGen.forall_transAut_mem_image d4TriRank_holds hZ hq2 hq3 hmodel hKc e' hB
    hBC' hcard hnot
  obtain ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, hsplit⟩ :=
    ModelGen.exists_clsData_orthPlusFour_three hcore hZ hmodel hKc e' hB hBE
  obtain ⟨-, hnd, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinate_model_witness_plus
      hmodel K hKc e'
  have hab :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_model_isometry_abelianization_order_bound
    _ .POmegaPlus (.inr (.inl rfl)) 4 Q.p Q.exponent hmodel K hKc
    (CFSG.LieType.Universal.Spin.quadPlus 4 K) (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K) e'
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (plusIndexEquiv 4) (CFSG.LieType.Universal.Spin.quadPlus 4 K) hab
  refine ⟨hZ, K, inferInstance, inferInstance, hKc, hnd, hab', ?_⟩
  rcases hsplit with hBB | ⟨b, hb, hbN, hBb, hbinf, A, σ, hact, hform, hfix⟩
  · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, 1, 1, RingEquiv.refl K, Or.inl hBB⟩⟩
  · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, b, A, σ,
      Or.inr ⟨hb, hbN, hBb, hbinf, hact, hform, hfix⟩⟩⟩

theorem concl_d4_three_of_orth
    (hOrth : ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q ≠ 2 → q ≠ p → ∀ {Ω : Type} [Group Ω] [Finite Ω]
      {S B : Subgroup Ω} [S.Normal], GLAPPrimeCore p ↥S = ⊥ → Subgroup.center ↥S = ⊥ →
      ∀ {d : TauCeti.ValidLieTypeIndex}, Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      IsElemAbelian p B → p ^ GLATwoLocalRank p Ω ≤ Nat.card B → p ^ 4 ≤ Nat.card B →
      Nat.card ↥(B ⊓ centModSubgroup p S) = p →
      (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
        Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
      ∀ {K : Type} [Field K] [Fintype K] [DecidableEq K] {m : ℕ} (Q : QuadraticForm K (Fin m → K)),
      (polarBilin Q).Nondegenerate → ∀ {Q₀ : TauCeti.PrimePower}, Q₀.p = q →
      Nat.card K = Q₀.card →
      (∃ k : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ k) →
      ((∃ n, 3 ≤ n ∧ d.1 = .B n Q₀ ∧ m = 2 * n + 1) ∨
        (∃ n, 4 ≤ n ∧ d.1 = .D n Q₀ ∧ m = 2 * n ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
        (∃ n, 4 ≤ n ∧ d.1 = .twistedD n Q₀ ∧ m = 2 * n ∧
          ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)) →
      ClsInner p S B (matrixDerived Q) (polarBilin Q) → S267ConcA p S B ∨ S267ConcBCDE p q S B)
    (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 Q).Valid) {q : ℕ}
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [S.Normal]
    (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hQq : Q.p = q)
    (e : Nonempty (PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 Q, hv⟩).Group))
    (hB : IsElemAbelian 3 B) (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B)
    (h4 : 3 ^ 4 ≤ Nat.card B) (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3)
    (hB81 : Nat.card B ≠ 3 ^ 4)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot 3 (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank 3 B) :
    S267ConcA 3 S B ∨ S267ConcBCDE 3 q S B := by
  classical
  obtain ⟨hZ, K, _, _, hKc, hnd, hab, ⟨Dat⟩⟩ :=
    exists_clsInner_d4_three Q hv hq2 hq3 hperf hcore hQq e hB h4 hBC hB81 hHq
  haveI : Fintype K := Fintype.ofFinite K
  subst hQq
  exact hOrth Nat.prime_three (by norm_num) hq2 hq3 hcore hZ e hB hrank h4 hBC hHq
    (coordinateQuadPlus 4 K) hnd rfl (by rw [hKc, TauCeti.PrimePower.card_def]) hab
    (Or.inr (Or.inl ⟨4, le_rfl, rfl, rfl,
      CFSG.ComponentClassification.CatFC.omegaPlus_isPlusType 4 K⟩)) Dat

theorem concl_d4_three (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 Q).Valid) {q : ℕ}
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [S.Normal]
    (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hQq : Q.p = q)
    (e : Nonempty (PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 Q, hv⟩).Group))
    (hB : IsElemAbelian 3 B) (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B)
    (h4 : 3 ^ 4 ≤ Nat.card B) (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3)
    (hB81 : Nat.card B ≠ 3 ^ 4)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot 3 (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank 3 B) :
    S267ConcA 3 S B ∨ S267ConcBCDE 3 q S B :=
  concl_d4_three_of_orth concl_of_clsInner_orth Q hv hq2 hq3 hperf hcore hQq e hB hrank h4 hBC
    hB81 hHq

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
