module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneFullCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneProducts
public import CFSG.RankThree.PartOne.K133C.InnerPlane
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThreeFamilies
public import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalNaturalCommonDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S11.TwoActionWiring
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import Certificates.Certificate119
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank

section Model

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem isLocallyBalancedAbs_projOrth (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hCL : CommonLayerCentralizerTrivial (ProjOrthDerived Q) p)
    (hO : OutStructure.OutPChain p (ProjOrthDerived Q)) :
    IsLocallyBalancedAbs p 3 (ProjOrthDerived Q) := by
  intro D hD hcard H hH hDH
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj := conj_injective_of_center_eq_bot_orth hcenter
  obtain ⟨P, hPD, hPI, hPc⟩ := K133C.exists_inner_plane hp hO
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p D).2 hD) hcard
  set E₁ : Subgroup (ProjOrthDerived Q) :=
    P.comap (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) with hE₁
  have hmap : E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) = P :=
    Subgroup.map_comap_eq_self hPI
  have hE₁el : IsElemAbelian p E₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have h2 : MulAut.conj (a : ProjOrthDerived Q) * MulAut.conj (b : ProjOrthDerived Q) =
          MulAut.conj (b : ProjOrthDerived Q) * MulAut.conj (a : ProjOrthDerived Q) :=
        congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hPD a.2⟩ ⟨_, hPD b.2⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact h2
    · rw [map_pow, map_one]
      exact hD.2 _ (hPD hx)
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hPc]
  have hbot := localDeltaIn_eq_bot_projOrth hQ hT hp hp3 hpl hCL E₁ hE₁el hE₁c hH
  rw [hmap] at hbot
  exact le_bot_iff.1 ((localDeltaIn_antitone H hPD).trans hbot.le)

end Model

section Field

theorem card_fixedField_validIndex_orth (d : TauCeti.ValidLieTypeIndex) (r : ℕ)
    (q : TauCeti.PrimePower) (hd : d.1 = .B r q ∨ d.1 = .D r q ∨ d.1 = .twistedD r q) :
    Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d) = q.p ^ q.exponent := by
  obtain ⟨d, hv⟩ := d
  rw [TauCeti.ValidLieTypeIndex.card_fixedField,
    TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
  rcases hd with h | h | h
  · change d = _ at h
    subst h
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  · change d = _ at h
    subst h
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  · change d = _ at h
    subst h
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]

end Field

section B

open CFSG.RankThree.PartTwo.Census CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin in
@[expose] def regimeBOrth (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r ∧ 3 < p

open CFSG.RankThree.PartTwo.Census CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne.KCOrthogonal in
theorem crossCharFamAt_B_orth : CrossCharFamAt .B regimeBOrth := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, hq2, hr, hp3⟩
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.B r q, hv⟩ r q (Or.inl rfl)
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hpl : p ≠ ringChar F := by rw [hring]; exact hpq
  have h2 : (2 : F) ≠ 0 := by
    have : CharP F q.p := ringChar.of_eq hring
    intro h
    have : q.p ∣ 2 := (CharP.cast_eq_zero_iff F q.p 2).mp (by exact_mod_cast h)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (n := r) (K := F) h2 hr
  let e₁ := Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq2 hr
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadOdd r F)
  let e : Cat ⟨.B r q, hv⟩ ≃* ProjOrthDerived (quadOdd r F) := e₁.trans e₂
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Cat ⟨.B r q, hv⟩) .POmegaOdd r
      q.p q.exponent :=
    statedClassicalModel_typeB_odd r q hv hq2 hr (MulEquiv.refl _)
  have hCLm : CommonLayerCentralizerTrivial
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
        (coordinateQuadOdd r F)) p :=
    orthogonal_inner_plane_local_components_full_automorphism_centralizer (Cat ⟨.B r q, hv⟩)
      .POmegaOdd (Or.inl rfl) r q.p q.exponent p hmodel hp hp3 hpq F hcard e₁
  have hCL : CommonLayerCentralizerTrivial (ProjOrthDerived (quadOdd r F)) p :=
    CommonLayerCentralizerTrivial.of_mulEquiv
      ((KCOrthogonalD4.bridgeEquiv (coordinateQuadOdd r F) (by omega)).trans
        (KCOrthogonalDescent.projOrthDerivedEquiv (coordinateOddIsometry r F).symm.toLinearEquiv 1
          fun v => by
            rw [Units.val_one, one_mul]
            exact (coordinateOddIsometry r F).symm.map_app v)) hCLm
  have hO : OutStructure.OutPChain p (ProjOrthDerived (quadOdd r F)) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.outPNice_POmegaOdd_of_ne_two hp hp2
      (statedClassicalModel_typeB_odd r q hv hq2 hr e.symm)).toChain
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_projOrth hQ hT hp hp3 hpl hCL hO)

end B

end CFSG.HardMathSupport.Timmesfeld.CrossChar
