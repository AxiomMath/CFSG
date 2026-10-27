module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsSetup
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseOrth
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutFieldOrth
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaPlus
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Neg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB
open QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable
  (hGA : GriessAllModelsStatement)

include hGA

theorem badClsAt_B {n : ℕ} {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B n Q).Valid)
    (hn : 3 ≤ n) : BadClsAt ⟨.B n Q, hv⟩ := by
  classical
  intro p q hp hp2 hq hq2 hqp Ω _ _ _ S B hSn hperf hcore hchar he hB _ hrank hB4 hBC _ hHq
  rw [TauCeti.LieTypeIndex.characteristic_B] at hchar
  subst hchar
  obtain ⟨e⟩ := he
  haveI := hSn
  set K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n Q, hv⟩) with hKdef
  haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fintype K := Fintype.ofFinite K
  have hKc : Nat.card K = Q.p ^ Q.exponent := CFSG.Models.card_fixedField_of
    (TauCeti.LieTypeIndex.characteristic_B n Q) (TauCeti.LieTypeIndex.fieldExponent_B n Q)
  let e' : PSimple p S ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) :=
    e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n Q hv hq2
      hn)
  have hmodel : StatedClassicalModel (PSimple p S) .POmegaOdd n Q.p Q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd n Q hv hq2 hn e
  have hZ : Subgroup.center ↥S = ⊥ := ModelGen.center_eq_bot_of_classical hGA hp hp2 hperf hcore
    hmodel hqp.symm (fun h => by cases h) (fun h => by cases h)
  obtain ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, hsplit⟩ :=
    ModelGen.exists_clsData_orthOdd hp hp2 hcore hZ hmodel hKc e' hB
  obtain ⟨-, hnd, -, -⟩ := coordinate_model_witness_odd hmodel K hKc e'
  have hab :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_model_isometry_abelianization_order_bound
    _ .POmegaOdd (.inl rfl) n Q.p Q.exponent hmodel K hKc
    (CFSG.LieType.Universal.Spin.quadOdd n K) (CFSG.LieType.Universal.Spin.coe_quadOdd n K) e'
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (oddIndexEquiv n) (CFSG.LieType.Universal.Spin.quadOdd n K) hab
  obtain ⟨Dat⟩ : Nonempty (ClsInner p S B (matrixDerived (coordinateQuadOdd n K))
      (polarBilin (coordinateQuadOdd n K))) := by
    rcases hsplit with hBB | ⟨b, hb, hbN, hBb, hbinf, A, σ, hact, hform, hfix⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, 1, 1, RingEquiv.refl K, Or.inl hBB⟩⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, b, A, σ,
        Or.inr ⟨hb, hbN, hBb, hbinf, hact, hform, hfix⟩⟩⟩
  exact concl_of_clsInner_orth hp hp2 hq2 hqp hcore hZ ⟨e⟩ hB hrank hB4 hBC hHq
    (coordinateQuadOdd n K) hnd rfl
    (by rw [hKc, TauCeti.PrimePower.card_def]) hab' (Or.inl ⟨n, hn, rfl, rfl⟩) Dat

theorem badClsAt_D {n : ℕ} {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.D n Q).Valid)
    (hn : 5 ≤ n) : BadClsAt ⟨.D n Q, hv⟩ := by
  classical
  intro p q hp hp2 hq hq2 hqp Ω _ _ _ S B hSn hperf hcore hchar he hB _ hrank hB4 hBC _ hHq
  rw [TauCeti.LieTypeIndex.characteristic_D] at hchar
  subst hchar
  obtain ⟨e⟩ := he
  haveI := hSn
  set K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D n Q, hv⟩) with hKdef
  haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fintype K := Fintype.ofFinite K
  have hKc : Nat.card K = Q.p ^ Q.exponent := CFSG.Models.card_fixedField_of
    (TauCeti.LieTypeIndex.characteristic_D n Q) (TauCeti.LieTypeIndex.fieldExponent_D n Q)
  let e' : PSimple p S ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) :=
    e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n Q hv)
  have hmodel : StatedClassicalModel (PSimple p S) .POmegaPlus n Q.p Q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD n Q hv e
  have hZ : Subgroup.center ↥S = ⊥ := ModelGen.center_eq_bot_of_classical hGA hp hp2 hperf hcore
    hmodel hqp.symm (fun h => by cases h) (fun h => by cases h)
  obtain ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, hsplit⟩ :=
    ModelGen.exists_clsData_orthPlus hp hp2 hcore hZ hn hmodel hKc e' hB
  obtain ⟨-, hnd, -, -⟩ := coordinate_model_witness_plus hmodel K hKc e'
  have hab :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_model_isometry_abelianization_order_bound
    _ .POmegaPlus (.inr (.inl rfl)) n Q.p Q.exponent hmodel K hKc
    (CFSG.LieType.Universal.Spin.quadPlus n K) (CFSG.LieType.Universal.Spin.coe_quadPlus n K) e'
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (plusIndexEquiv n) (CFSG.LieType.Universal.Spin.quadPlus n K) hab
  obtain ⟨Dat⟩ : Nonempty (ClsInner p S B (matrixDerived (coordinateQuadPlus n K))
      (polarBilin (coordinateQuadPlus n K))) := by
    rcases hsplit with hBB | ⟨b, hb, hbN, hBb, hbinf, A, σ, hact, hform, hfix⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, 1, 1, RingEquiv.refl K, Or.inl hBB⟩⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, b, A, σ,
        Or.inr ⟨hb, hbN, hBb, hbinf, hact, hform, hfix⟩⟩⟩
  exact concl_of_clsInner_orth hp hp2 hq2 hqp hcore hZ ⟨e⟩ hB hrank hB4 hBC hHq
    (coordinateQuadPlus n K) hnd rfl
    (by rw [hKc, TauCeti.PrimePower.card_def]) hab'
    (Or.inr (Or.inl ⟨n, by omega, rfl, rfl,
      CFSG.ComponentClassification.CatFC.omegaPlus_isPlusType n K⟩)) Dat

theorem badClsAt_twistedD {n : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD n Q).Valid) : BadClsAt ⟨.twistedD n Q, hv⟩ := by
  classical
  intro p q hp hp2 hq hq2 hqp Ω _ _ _ S B hSn hperf hcore hchar he hB _ hrank hB4 hBC _ hHq
  rw [TauCeti.LieTypeIndex.characteristic_twistedD] at hchar
  subst hchar
  obtain ⟨e⟩ := he
  haveI := hSn
  have hn : 4 ≤ n := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hn1 : 1 ≤ n := by omega
  set K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD n Q, hv⟩) with hKdef
  haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fintype K := Fintype.ofFinite K
  have hKc : Nat.card K = Q.p ^ Q.exponent := CFSG.Models.card_fixedField_of
    (TauCeti.LieTypeIndex.characteristic_twistedD n Q)
    (TauCeti.LieTypeIndex.fieldExponent_twistedD n Q)
  obtain ⟨b₀, c₀, hirr, ⟨e₀⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      n Q hv
  let e' : PSimple p S ≃* StatedProj (StatedOmega (StatedQuadMinus n K b₀ c₀)) := e.trans e₀
  have hmodel : StatedClassicalModel (PSimple p S) .POmegaMinus n Q.p Q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD n Q hv e
  have hZ : Subgroup.center ↥S = ⊥ := ModelGen.center_eq_bot_of_classical hGA hp hp2 hperf hcore
    hmodel hqp.symm (fun h => by cases h) (fun h => by cases h)
  obtain ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, hsplit⟩ :=
    ModelGen.exists_clsData_orthMinus hp hp2 hcore hZ hn1 hmodel hKc b₀ c₀ hirr e' hB
  obtain ⟨-, hnd, -, -⟩ := coordinate_model_witness_minus hmodel K hKc b₀ c₀ hirr e'
  have hab :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_model_isometry_abelianization_order_bound
    _ .POmegaMinus (.inr (.inr rfl)) n Q.p Q.exponent hmodel K hKc b₀ c₀ hirr
    (CFSG.LieType.Universal.Spin.quadMinus n K b₀ c₀)
    (CFSG.LieType.Universal.Spin.coe_quadMinus n K b₀ c₀) e'
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (minusIndexEquiv n hn1) (CFSG.LieType.Universal.Spin.quadMinus n K b₀ c₀) hab
  obtain ⟨Dat⟩ : Nonempty (ClsInner p S B (matrixDerived (coordinateQuadMinus n K hn1 b₀ c₀))
      (polarBilin (coordinateQuadMinus n K hn1 b₀ c₀))) := by
    rcases hsplit with hBB | ⟨b, hb, hbN, hBb, hbinf, A, σ, hact, hform, hfix⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, 1, 1, RingEquiv.refl K, Or.inl hBB⟩⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, b, A, σ,
        Or.inr ⟨hb, hbN, hBb, hbinf, hact, hform, hfix⟩⟩⟩
  exact concl_of_clsInner_orth hp hp2 hq2 hqp hcore hZ ⟨e⟩ hB hrank hB4 hBC hHq
    (coordinateQuadMinus n K hn1 b₀ c₀)
    hnd rfl (by rw [hKc, TauCeti.PrimePower.card_def]) hab'
    (Or.inr (Or.inr ⟨n, hn, rfl, rfl,
      CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus n hn1
        hirr⟩)) Dat

theorem badClsAt_D_four_of_ne_three {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D 4 Q).Valid) :
    ∀ (p q : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → q.Prime → q ≠ 2 → q ≠ p →
      ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
        ∀ (S B : Subgroup Ω), S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
          (⟨.D 4 Q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = q →
          Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 Q, hv⟩).Group) →
          IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
          p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
          ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
          (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
            Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
              GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
          S267ConcA p S B ∨ S267ConcBCDE p q S B := by
  classical
  intro p q hp hp2 hp3 hq hq2 hqp Ω _ _ _ S B hSn hperf hcore hchar he hB _ hrank hB4 hBC _ hHq
  rw [TauCeti.LieTypeIndex.characteristic_D] at hchar
  subst hchar
  obtain ⟨e⟩ := he
  haveI := hSn
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact absurd (h ▸ hp) (by norm_num)
    · exact h
  set K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 Q, hv⟩) with hKdef
  haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fintype K := Fintype.ofFinite K
  have hKc : Nat.card K = Q.p ^ Q.exponent := CFSG.Models.card_fixedField_of
    (TauCeti.LieTypeIndex.characteristic_D 4 Q) (TauCeti.LieTypeIndex.fieldExponent_D 4 Q)
  let e' : PSimple p S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 Q hv)
  have hmodel : StatedClassicalModel (PSimple p S) .POmegaPlus 4 Q.p Q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 Q hv e
  have hZ : Subgroup.center ↥S = ⊥ := ModelGen.center_eq_bot_of_classical hGA hp hp2 hperf hcore
    hmodel hqp.symm (fun h => by cases h) (fun h => by cases h)
  obtain ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, hsplit⟩ :=
    ModelGen.exists_clsData_orthPlusFour hp hp5 hcore hZ hmodel hKc e' hB
  obtain ⟨-, hnd, -, -⟩ := coordinate_model_witness_plus hmodel K hKc e'
  have hab :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_model_isometry_abelianization_order_bound
    _ .POmegaPlus (.inr (.inl rfl)) 4 Q.p Q.exponent hmodel K hKc
    (CFSG.LieType.Universal.Spin.quadPlus 4 K) (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K) e'
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (plusIndexEquiv 4) (CFSG.LieType.Universal.Spin.quadPlus 4 K) hab
  obtain ⟨Dat⟩ : Nonempty (ClsInner p S B (matrixDerived (coordinateQuadPlus 4 K))
      (polarBilin (coordinateQuadPlus 4 K))) := by
    rcases hsplit with hBB | ⟨b, hb, hbN, hBb, hbinf, A, σ, hact, hform, hfix⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, 1, 1, RingEquiv.refl K, Or.inl hBB⟩⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, b, A, σ,
        Or.inr ⟨hb, hbN, hBb, hbinf, hact, hform, hfix⟩⟩⟩
  exact concl_of_clsInner_orth hp hp2 hq2 hqp hcore hZ ⟨e⟩ hB hrank hB4 hBC hHq
    (coordinateQuadPlus 4 K) hnd rfl
    (by rw [hKc, TauCeti.PrimePower.card_def]) hab'
    (Or.inr (Or.inl ⟨4, le_rfl, rfl, rfl,
      CFSG.ComponentClassification.CatFC.omegaPlus_isPlusType 4 K⟩)) Dat

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
