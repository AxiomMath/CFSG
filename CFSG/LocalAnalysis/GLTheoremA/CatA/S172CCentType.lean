module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentUni
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Unit
import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountOmega
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4Gen
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFix
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthPlus
import CFSG.Adapters.CatalogueFieldBridges.Linear
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X

section Field

theorem exists_natCard_eq_two_pow (F : Type) [Field F] [Finite F] [CharP F 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card F = 2 ^ f := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

end Field

section Perp

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem nondeg_comp_polarPerp (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {W : Submodule F V}
    (hW : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate) :
    (QuadraticMap.polarBilin (Q.comp (polarPerp Q W).subtype)).Nondegenerate := by
  rw [polarBilin_comp_subtype_cent]
  refine (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
    (B := QuadraticMap.polarBilin Q) (W := polarPerp Q W) (isRefl_polarBilin Q)).mpr ?_
  have horth : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (polarPerp Q W) = W := by
    unfold polarPerp
    exact LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q) W
  rw [horth]
  exact (isCompl_polarPerp hW).symm

private noncomputable def isPlusType_comp_polarPerp_iff_aux1 {W : Submodule F V}
    (hW : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate) :
    Q.IsometryEquiv ((Q.comp W.subtype).prod (Q.comp (polarPerp Q W).subtype)) where
  toLinearEquiv :=
    (Submodule.prodEquivOfIsCompl W (polarPerp Q W) (isCompl_polarPerp hW)).symm
  map_app' v := by
    obtain ⟨⟨x, y⟩, rfl⟩ :=
      (Submodule.prodEquivOfIsCompl W (polarPerp Q W) (isCompl_polarPerp hW)).surjective v
    have h : ((Submodule.prodEquivOfIsCompl W (polarPerp Q W) (isCompl_polarPerp hW) (x, y) : V))
        = (x : V) + (y : V) := Submodule.coe_prodEquivOfIsCompl' ..
    change ((Q.comp W.subtype).prod (Q.comp (polarPerp Q W).subtype))
      ((Submodule.prodEquivOfIsCompl W (polarPerp Q W) (isCompl_polarPerp hW)).symm
        ((Submodule.prodEquivOfIsCompl W (polarPerp Q W) (isCompl_polarPerp hW)) (x, y))) = _
    rw [LinearEquiv.symm_apply_apply, h, QuadraticMap.map_add Q (x : V) (y : V),
      (mem_polarPerp_iff (x := (y : V))).1 y.2 x x.2, add_zero]
    rfl

theorem isPlusType_comp_polarPerp_iff (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 2 ≤ n) {W : Submodule F V}
    (hW : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate) (hW2 : Module.finrank F W = 2)
    (hWm : ¬ IsPlusType (Q.comp W.subtype)) :
    IsPlusType (Q.comp (polarPerp Q W).subtype) ↔ ¬ IsPlusType Q := by
  have hWp : (QuadraticMap.polarBilin (Q.comp (polarPerp Q W).subtype)).Nondegenerate :=
    nondeg_comp_polarPerp hQ hW
  have hdimWp : Module.finrank F (polarPerp Q W) = 2 * (n - 1) := by
    rw [finrank_polarPerp hQ W, hdim, hW2]
    omega
  have hprod := CFSG.RankThree.PartOne.K159.isPlusType_prod_iff (K := F) (V₁ := W)
    (V₂ := polarPerp Q W) (Q₁ := Q.comp W.subtype)
    (Q₂ := Q.comp (polarPerp Q W).subtype) hW hWp (d₁ := 1) (d₂ := n - 1)
    (le_refl 1) (by omega) (by omega) hdimWp
  have hiso := CFSG.GroupTheory.WeirSylow.isPlusType_congr
    (isPlusType_comp_polarPerp_iff_aux1 (Q := Q) hW)
  have hpq : (IsPlusType (Q.comp W.subtype) ↔
      IsPlusType (Q.comp (polarPerp Q W).subtype)) ↔
      ¬ IsPlusType (Q.comp (polarPerp Q W).subtype) := by
    constructor
    · intro h h2; exact hWm (h.mpr h2)
    · intro h2; exact ⟨fun h1 => absurd h1 hWm, fun h1 => absurd h1 h2⟩
  have hA : IsPlusType Q ↔ ¬ IsPlusType (Q.comp (polarPerp Q W).subtype) :=
    hiso.trans (hprod.trans hpq)
  constructor
  · intro h2 h1; exact (hA.mp h1) h2
  · intro h1
    by_contra h2
    exact h1 (hA.mpr h2)

end Perp

section TotallySingular

variable {F : Type} [Field F] [Finite F] [CharP F 2] {W : Type} [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] {R : QuadraticForm F W}

theorem exists_threeSingular (hR : (QuadraticMap.polarBilin R).Nondegenerate) {m : ℕ}
    (hdim : Module.finrank F W = 2 * m) (hm : (IsPlusType R ∧ 3 ≤ m) ∨ (¬ IsPlusType R ∧ 4 ≤ m)) :
    ∃ T : Submodule F W, Module.finrank F T = 3 ∧ ∀ u ∈ T, R u = 0 := by
  rcases hm with ⟨hplus, hm3⟩ | ⟨hminus, hm4⟩
  · by_cases hm3' : m = 3
    · subst hm3'
      obtain ⟨S, hS, hSs⟩ := hplus
      refine ⟨S, ?_, hSs⟩
      rw [hdim] at hS
      omega
    · exact CFSG.RankThree.PartOne.exists_threeSingular_of_dim R hR (by omega) hdim
  · exact CFSG.RankThree.PartOne.exists_threeSingular_of_dim R hR hm4 hdim

end TotallySingular

section Bridge

variable {F : Type} [Field F] [Finite F] [CharP F 2] {W : Type} [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] {R : QuadraticForm F W}

private theorem nonempty_pSimple_top_orthDerived_mulEquiv_aux1
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) {m : ℕ} (hm : 3 ≤ m)
    (hdim : Module.finrank F W = 2 * m)
    (hT : ∃ T : Submodule F W, Module.finrank F T = 3 ∧ ∀ u ∈ T, R u = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    p ∣ Nat.card ↥(orthDerived R) := by
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT
  have hq : p ∣ Nat.card F ^ 2 - 1 := by
    have hfac : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      simpa using Nat.sq_sub_sq (Nat.card F) 1
    rw [hfac]
    exact hpq.mul_right _
  have h2m : 2 ≤ m := by omega
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega : 1 ≤ m)
  by_cases hplus : IsPlusType R
  · have hdim' : Module.finrank F W = 2 * (m - 1 + 1) := by rw [hm1]; exact hdim
    have hcard : Nat.card ↥(orthDerived R) = CFSG.Open.ordD m (Nat.card F) := by
      rw [CFSG.StandardType.card_orthDerived_eq_ordD R hR hdim' hΩ hplus, hm1]
    rw [hcard]
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e.prime_dvd_orderD (n := m) h2m hq
  · have hdim' : Module.finrank F W = 2 * (m - 1 + 1) := by rw [hm1]; exact hdim
    have hcard : Nat.card ↥(orthDerived R) = CFSG.Open.ordTwistedD m (Nat.card F) := by
      rw [CFSG.StandardType.card_orthDerived_eq_ordTwistedD R hR hdim' hΩ hplus, hm1]
    rw [hcard]
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e.prime_dvd_orderTwistedD (n := m) h2m hq

theorem nonempty_pSimple_top_orthDerived_mulEquiv (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {m : ℕ} (hm : 3 ≤ m) (hdim : Module.finrank F W = 2 * m)
    (hT : ∃ T : Submodule F W, Module.finrank F T = 3 ∧ ∀ u ∈ T, R u = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    Nonempty (PSimple p (⊤ : Subgroup ↥(orthDerived R)) ≃* ↥(orthDerived R)) := by
  haveI : Finite W := Module.finite_of_finite F
  haveI : Finite (W ≃ₗ[F] W) :=
    Finite.of_injective (fun e : W ≃ₗ[F] W => (e : W → W))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Nontrivial W := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have hZ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT
  have hq := CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT
  let e : (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) ≃* ↥(orthDerived R) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  haveI hsimple : IsSimpleGroup ↥(orthDerived R) := by
    haveI : IsSimpleGroup (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) := hq.2.1
    exact e.symm.isSimpleGroup
  have hncR : ∃ x y : ↥(orthDerived R), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨e a, e b, fun h => hab (by simpa using congrArg e.symm h)⟩
  have hdvd := nonempty_pSimple_top_orthDerived_mulEquiv_aux1 hR hm hdim hT hp hp2 hpq
  haveI : IsSimpleGroup ↥(⊤ : Subgroup ↥(orthDerived R)) := Subgroup.topEquiv.isSimpleGroup
  have hnc : ∃ x y : ↥(⊤ : Subgroup ↥(orthDerived R)), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hncR
    exact ⟨Subgroup.topEquiv.symm x, Subgroup.topEquiv.symm y,
      fun h => hxy (by simpa using congrArg Subgroup.topEquiv h)⟩
  have hdvdK : p ∣ Nat.card ↥(⊤ : Subgroup ↥(orthDerived R)) := by
    rwa [Subgroup.card_top]
  obtain ⟨e₀⟩ := CFSG.LocalAnalysis.GLTheoremA.rf4_pSimple_equiv_of_simple hp
    (⊤ : Subgroup ↥(orthDerived R)) hnc hdvdK
  exact ⟨e₀.trans Subgroup.topEquiv⟩

private theorem catalogIs_orthDerived_plus_aux1
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) {m : ℕ} (hm : 4 ≤ m)
    (hdim : Module.finrank F W = 2 * m) (hplus : IsPlusType R) :
    catalogIs ↥(orthDerived R) (isOmPA m (Nat.card F)) := by
  obtain ⟨f, hf1, hf⟩ := exists_natCard_eq_two_pow F
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hv : (TauCeti.LieTypeIndex.D m q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩
  obtain ⟨e⟩ := nonempty_isometry_quadPlus hR hdim hplus
  obtain ⟨hnd, _hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := m) (by omega)
  have : Inhabited (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have : Nontrivial (Fin m ⊕ Fin m → F) := Pi.nontrivial
  let E2 : ↥(orthDerived (CFSG.LieType.Universal.Spin.quadPlus m F)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus m F)) :=
    (MulEquiv.ofBijective (CFSG.RankThree.PartOne.piOrth (CFSG.LieType.Universal.Spin.quadPlus m F))
        ⟨CFSG.RankThree.PartOne.piOrth_injective hnd, CFSG.RankThree.PartOne.piOrth_surjective⟩).trans
      (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadPlus (n := m) (K := F))).symm
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.D m q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hFO : Nat.card F =
      TauCeti.ValidLieTypeIndex.fieldOrder ⟨TauCeti.LieTypeIndex.D m q, hv⟩ := by
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.D m q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_D m q
    have he : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.D m q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_D m q
    rw [TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hc, he]
    exact hf
  obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField
    ⟨TauCeti.LieTypeIndex.D m q, hv⟩ F hFO
  let E3 : StatedProj (StatedOmega (StatedQuadPlus m F)) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D m q, hv⟩).Group :=
    (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
          (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid m q hv).symm
  refine ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D m q, hv⟩, ?_, ?_⟩
  · left
    show m = m ∧ q.card = Nat.card F
    exact ⟨rfl, by rw [TauCeti.PrimePower.card_def]; exact hf.symm⟩
  · exact ⟨(CFSG.RankThree.PartOne.orthDerivedEquiv e).trans (E2.trans E3)⟩

private theorem catalogIs_orthDerived_plus_aux3 :
    catalogIs (StatedSL 4 F) (isLnA 4 (Nat.card F)) := by
  obtain ⟨f, hf1, hf⟩ := exists_natCard_eq_two_pow F
  rcases (show f = 1 ∨ 2 ≤ f by omega) with hf1' | hf2
  · have hcard2 : Nat.card F = 2 := by rw [hf, hf1']; norm_num
    obtain ⟨eA8⟩ :=
      CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_four_mulEquiv_alternating_eight
        (k := F) hcard2
    let e1 : StatedSL 4 F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) F :=
      (CFSG.RankThree.PartOne.statedSL4EquivStatedProj (F := F)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 F).symm
    have h8 : 5 ≤ 8 := by norm_num
    let i8 : TauCeti.CFSGIndex := TauCeti.CFSGIndex.alternating 8 h8
    refine ⟨i8, ?_,
      ⟨e1.trans ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        4 F).trans eA8)⟩⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hcard2, rfl⟩)))
  · let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
    have hq2 : q.card ≠ 2 := by
      rw [TauCeti.PrimePower.card_def]
      intro h
      have hle : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      rw [h] at hle
      norm_num at hle
    have hvA : (TauCeti.LieTypeIndex.A 3 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      refine ⟨⟨by omega, by intro h; omega⟩, ?_⟩
      intro h
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hq⟩
      · omega
      · omega
      · exact absurd hq hq2
    let e1 : StatedSL 4 F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) F :=
      (CFSG.RankThree.PartOne.statedSL4EquivStatedProj (F := F)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 F).symm
    let e2 : Matrix.ProjectiveSpecialLinearGroup (Fin 4) F ≃*
        (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 3 q, hvA⟩).Group :=
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        4 F).trans
        (CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.catEquivProjectiveSL
          (m := 3) (k := F) (ℓ := 2) (e := f) Nat.prime_two hf1 hf hvA).symm
    refine ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 3 q, hvA⟩, Or.inl ?_,
      ⟨e1.trans e2⟩⟩
    show 3 + 1 = 4 ∧ q.card = Nat.card F
    exact ⟨rfl, by rw [TauCeti.PrimePower.card_def]; exact hf.symm⟩

private theorem catalogIs_orthDerived_plus_aux2
    (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hdim : Module.finrank F W = 2 * 3) (hplus : IsPlusType R) :
    catalogIs ↥(orthDerived R) (isOmPA 3 (Nat.card F)) := by
  obtain ⟨U, hU, hUs⟩ := hplus
  have hU3 : Module.finrank F U = 3 := by omega
  have hts : ∃ U : Submodule F W, Module.finrank F U = 3 ∧ ∀ u ∈ U, R u = 0 := ⟨U, hU3, hUs⟩
  have hdim6 : Module.finrank F W = 6 := by omega
  obtain ⟨κ⟩ := CFSG.LocalAnalysis.WeakClosure81.kleinCommutatorOrthogonalSix R hR hdim6 hts
  let eK : ↥(orthDerived R) ≃* StatedSL 4 F :=
    (CFSG.RankThree.PartOne.orthDerivedEquivCommutator R).symm.trans κ
  obtain ⟨i, hi, ⟨eS⟩⟩ := catalogIs_orthDerived_plus_aux3 (F := F)
  exact ⟨i, Or.inr ⟨rfl, hi⟩, ⟨eK.trans eS⟩⟩

theorem catalogIs_orthDerived_plus (hR : (QuadraticMap.polarBilin R).Nondegenerate) {m : ℕ} (hm : 3 ≤ m)
    (hdim : Module.finrank F W = 2 * m) (hplus : IsPlusType R) :
    catalogIs ↥(orthDerived R) (isOmPA m (Nat.card F)) := by
  rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | hm4
  · exact catalogIs_orthDerived_plus_aux2 hR hdim hplus
  · exact catalogIs_orthDerived_plus_aux1 hR hm4 hdim hplus

private theorem catalogIs_orthDerived_minus_aux1 {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 4 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    catalogIs (StatedProj (StatedOmega (StatedQuadMinus m K b c))) (isOmMA m (Nat.card K)) := by
  obtain ⟨f, hf1, hcard⟩ := exists_natCard_eq_two_pow K
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hp : q.p = 2 := rfl
  have hv : (TauCeti.LieTypeIndex.twistedD m q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj m q hv hp
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField
    ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩ K (by
      change Nat.card K = (TauCeti.LieTypeIndex.twistedD m q).fieldOrder
      rw [TauCeti.LieTypeIndex.fieldOrder_twistedD, TauCeti.PrimePower.card_def]
      exact hcard)
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := m) (by omega)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
  let e1 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := m) (b := b) (c := c) φ rfl rfl))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  refine ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩, ?_,
    ⟨(e1.trans e2).trans eT.symm⟩⟩
  left
  show m = m ∧ q.card = Nat.card K
  rw [TauCeti.PrimePower.card_def]
  exact ⟨rfl, hcard.symm⟩

theorem catalogIs_orthDerived_minus (hR : (QuadraticMap.polarBilin R).Nondegenerate) {m : ℕ} (hm : 4 ≤ m)
    (hdim : Module.finrank F W = 2 * m) (hminus : ¬ IsPlusType R) :
    catalogIs ↥(orthDerived R) (isOmMA m (Nat.card F)) := by
  obtain ⟨b', c', hirr'⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic F
  obtain ⟨eiso⟩ := nonempty_isometry_of_not_isPlusType hR (by omega) hdim hminus hirr'
  obtain ⟨i, hi, ⟨e⟩⟩ := catalogIs_orthDerived_minus_aux1 (K := F) hm hirr'
  exact ⟨i, hi, ⟨(CFSG.RankThree.PartOne.orthDerivedEquiv eiso).trans
    ((CFSG.LocalAnalysis.GLTheoremA.S172C.nonempty_statedProjOmegaMinus_equiv_orthDerived hm
      hirr').some.symm.trans e)⟩⟩

theorem catalogIs_pSimple_top_orthDerived_plus (hR : (QuadraticMap.polarBilin R).Nondegenerate) {m : ℕ}
    (hm : 3 ≤ m) (hdim : Module.finrank F W = 2 * m) (hplus : IsPlusType R) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    catalogIs (PSimple p (⊤ : Subgroup ↥(orthDerived R))) (isOmPA m (Nat.card F)) := by
  obtain ⟨e⟩ := nonempty_pSimple_top_orthDerived_mulEquiv hR hm hdim
    (exists_threeSingular hR hdim (Or.inl ⟨hplus, hm⟩)) hp hp2 hpq
  exact (catalogIs_congr e).2 (catalogIs_orthDerived_plus hR hm hdim hplus)

theorem catalogIs_pSimple_top_orthDerived_minus (hR : (QuadraticMap.polarBilin R).Nondegenerate) {m : ℕ}
    (hm : 4 ≤ m) (hdim : Module.finrank F W = 2 * m) (hminus : ¬ IsPlusType R) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    catalogIs (PSimple p (⊤ : Subgroup ↥(orthDerived R))) (isOmMA m (Nat.card F)) := by
  obtain ⟨e⟩ := nonempty_pSimple_top_orthDerived_mulEquiv hR (by omega) hdim
    (exists_threeSingular hR hdim (Or.inr ⟨hminus, hm⟩)) hp hp2 hpq
  exact (catalogIs_congr e).2 (catalogIs_orthDerived_minus hR hm hdim hminus)

end Bridge

section Transport

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem catalogIs_pSimple_supportedFixedDerived {x : ↥(orthDerived Q)}
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[F] V)) {Q₁ : TauCeti.CFSGIndex → Prop}
    (h : catalogIs (PSimple p (⊤ : Subgroup
      ↥(orthDerived (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype)))) Q₁) :
    catalogIs (PSimple p ((supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q))) Q₁ := by
  let e : ↥((supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) ≃*
      ↥(⊤ : Subgroup ↥(orthDerived (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype))) :=
    (Subgroup.subgroupOfEquivOfLe hx.supportedFixedDerived_le_orthDerived).trans
      ((supportedFixedDerivedEquiv hx).trans Subgroup.topEquiv.symm)
  exact (S172B.Cent.catalogIs_pSimple_congr_mulEquiv e p Q₁).2 h

private theorem catalogIs_pSimple_specialBlock_aux1 {F : Type} [Field F] [Finite F] [CharP F 2]
    {h : F[X]} (hdeg : h.natDegree = 2) [Fact (Irreducible h)] {d ℓ f : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
    (hcard : Nat.card F = ℓ ^ f) : d = 1 := by
  haveI : Module.Finite F (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite
  have hE : Nat.card (AdjoinRoot h) = (Nat.card F) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F),
      (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have hpow : ℓ ^ (2 * (f * d)) = ℓ ^ (2 * f) := by
    rw [← hU.card, hE, hcard, ← pow_mul, Nat.mul_comm f 2]
  have h2 : 2 * (f * d) = 2 * f := Nat.pow_right_injective hU.prime.two_le hpow
  have h3 : f * d = f := Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hf : 0 < f := by have := hU.one_le; omega
  exact Nat.eq_of_mul_eq_mul_left hf (by simpa using h3)

theorem catalogIs_pSimple_specialBlock (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : ↥(orthDerived Q)} (hx : orderOf x = p)
    {h : F[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1) {m : ℕ}
    (hm : primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap h = m)
    (hm4 : 4 ≤ m ∨ ((m = 2 ∨ m = 3) ∧ 4 ≤ Nat.card F)) :
    catalogIs (PSimple p ((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)))
      (isUnA m (Nat.card F)) := by
  have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
  have hx' : OddOrderIsometry Q p (x : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp hpl hQ x hx
  have hself : h = reciprocalPolynomial h :=
    (hx'.reciprocal_eq_of_dvd_card_succ hp hpq hh hne).symm
  have hdeg : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx' hp hp2 hpq hh hne
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨d, ℓ, f, hU, B, hd0, hcard, hBs, hBl, hrange⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.orth2_exists_unitary_model hx'
      (hp.odd_of_ne_two hp2) hh hne hself
  have hd1 : d = 1 := catalogIs_pSimple_specialBlock_aux1 hdeg hU hcard
  have hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h) :=
    isQuasisimple_specialBlock_of_multiplicity hp hp2 hpq hx' hh hne hm hm4
  have hleΩ : specialBlock Q (x : V ≃ₗ[F] V) h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans fun _ hg => (Subgroup.mem_inf.mp hg).1)
  let φ : ↥((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ≃*
      ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
    (Subgroup.subgroupOfEquivOfLe hleΩ).trans
      ((MonoidHom.ofInjective (hx'.specialBlockGL_injective hh)).trans
        (MulEquiv.subgroupCongr hrange))
  refine (S172B.Cent.catalogIs_pSimple_congr_mulEquiv φ p (isUnA m (Nat.card F))).2 ?_
  have hdim : finrank (AdjoinRoot h)
      (primaryComponent (x : V ≃ₗ[F] V).toLinearMap h) = m := by
    simpa [primaryMultiplicity] using hm
  have hk : 4 ≤ m ∨ ((m = 2 ∨ m = 3) ∧ 4 ≤ ℓ ^ (f * d)) := by
    rcases hm4 with h4 | ⟨h23, h4⟩
    · exact Or.inl h4
    · exact Or.inr ⟨h23, by rw [hd1, Nat.mul_one, ← hcard]; exact h4⟩
  have hpq' : p ∣ ℓ ^ (f * d) + 1 := by rw [hd1, Nat.mul_one, ← hcard]; exact hpq
  have hres := catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen hU hBs hBl hdim hk hp hp2 hpq'
  simpa [hd1, Nat.mul_one, hcard] using hres

end Transport

section Arith

theorem false_of_catalogIs_isUnA_isOmPA (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S]
    {m f : ℕ} (hf : 1 ≤ f) (h1 : catalogIs S (isUnA m (2 ^ f))) (h2 : catalogIs S (isOmPA m (2 ^ f))) :
    False := by
  obtain ⟨-, -, hu⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isUnA hb hf h1
  obtain ⟨hm3, hv⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isOmPA hb hf h2
  rw [hv] at hu
  have : 0 < f * (m * (m - 1)) := Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  omega

theorem false_of_catalogIs_isUnA_isOmMA (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S]
    {m f : ℕ} (hf : 1 ≤ f) (h1 : catalogIs S (isUnA m (2 ^ f))) (h2 : catalogIs S (isOmMA m (2 ^ f))) :
    False := by
  obtain ⟨-, -, hu⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isUnA hb hf h1
  obtain ⟨hm3, hv⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isOmMA hb hf h2
  rw [hv] at hu
  have : 0 < f * (m * (m - 1)) := Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  omega

end Arith

section Top

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

private theorem card_pSimple_glaLayer_top_orthDerived_aux1 {G : Type} [Group G]
    (h : CFSG.IsQuasisimple G) : CFSG.Open.IsQuasisimple G :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem card_pSimple_glaLayer_top_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) :
    Nat.card (PSimple p (GLALayer (⊤ : Subgroup ↥(orthDerived Q)))) = Nat.card ↥(orthDerived Q) := by
  have hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ u ∈ T, Q u = 0 := by
    by_cases hplus : IsPlusType Q
    · exact exists_threeSingular hQ hdim (Or.inl ⟨hplus, by omega⟩)
    · exact exists_threeSingular hQ hdim (Or.inr ⟨hplus, by omega⟩)
  have hq : CFSG.IsQuasisimple ↥(orthDerived Q) := isQuasisimple_orthDerived hQ hT
  have hqOpen : CFSG.Open.IsQuasisimple ↥(orthDerived Q) :=
    card_pSimple_glaLayer_top_orthDerived_aux1 hq
  have hcomp : IsComponentOf (⊤ : Subgroup ↥(orthDerived Q)) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv) hqOpen⟩
  have hLayer : GLALayer (⊤ : Subgroup ↥(orthDerived Q)) = ⊤ := by
    rw [show GLALayer (⊤ : Subgroup ↥(orthDerived Q)) =
      sSup {K | IsComponentOf K (⊤ : Subgroup ↥(orthDerived Q))} from rfl]
    exact le_antisymm (sSup_le fun K _ => le_top) (le_sSup hcomp)
  rw [hLayer]
  obtain ⟨e⟩ := nonempty_pSimple_top_orthDerived_mulEquiv hQ (by omega) hdim hT hp hp2 hpq
  exact Nat.card_congr e.toEquiv

theorem v2_card_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n f : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hf : Nat.card F = 2 ^ f) (hf1 : 1 ≤ f) :
    padicValNat 2 (Nat.card ↥(orthDerived Q)) = f * (n * (n - 1)) := by
  have hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ u ∈ T, Q u = 0 := by
    by_cases hplus : IsPlusType Q
    · exact exists_threeSingular hQ hdim (Or.inl ⟨hplus, by omega⟩)
    · exact exists_threeSingular hQ hdim (Or.inr ⟨hplus, by omega⟩)
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  have hdim' : Module.finrank F V = 2 * ((n - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]; exact hdim
  by_cases hplus : IsPlusType Q
  · have hcard : Nat.card ↥(orthDerived Q) = CFSG.Open.orderD n (2 ^ f) := by
      have h := CFSG.StandardType.card_orthDerived_eq_ordD (K := F) (W := V) Q hQ
        (m := n - 1) hdim' hΩ hplus
      rw [show n - 1 + 1 = n by omega] at h
      rw [h, hf]
      rfl
    obtain ⟨m', hm', hmul⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S172.orderD_two_pow (n := n) (f := f) (by omega) hf1
    have hfinal : padicValNat 2 (CFSG.Open.orderD n (2 ^ f)) = f * (n * (n - 1)) :=
      CFSG.LocalAnalysis.GLTheoremA.S172.v2_of_odd_mul hm' hmul
    rw [hcard, hfinal]
  · have hcard : Nat.card ↥(orthDerived Q) = CFSG.Open.orderTwistedD n (2 ^ f) := by
      have h := CFSG.StandardType.card_orthDerived_eq_ordTwistedD (K := F) (W := V) Q hQ
        (m := n - 1) hdim' hΩ hplus
      rw [show n - 1 + 1 = n by omega] at h
      rw [h, hf]
      rfl
    obtain ⟨m', hm', hmul⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S172.orderTwistedD_two_pow (n := n) (f := f) (by omega) hf1
    have hfinal : padicValNat 2 (CFSG.Open.orderTwistedD n (2 ^ f)) = f * (n * (n - 1)) :=
      CFSG.LocalAnalysis.GLTheoremA.S172.v2_of_odd_mul hm' hmul
    rw [hcard, hfinal]

theorem not_layerIs_top_isUnA (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n f : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hf : Nat.card F = 2 ^ f) (hf1 : 1 ≤ f)
    (hb : CatDistinct.OrderBridge) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    ¬ LayerIs p (⊤ : Subgroup ↥(orthDerived Q)) (isUnA (n - 1) (Nat.card F)) := by
  intro hL
  have hcard := card_pSimple_glaLayer_top_orthDerived hQ hdim hn hp hp2 hpq
  have hv := v2_card_orthDerived hQ hdim hn hf hf1
  rw [hf] at hL
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite (PSimple p (GLALayer (⊤ : Subgroup ↥(orthDerived Q)))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  obtain ⟨-, -, hu⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isUnA hb hf1 hL.2
  rw [hcard, hv] at hu
  have h1 : n * (n - 1) * 2 = (n - 1) * (n - 1 - 1) := by
    have : f * (n * (n - 1)) * 2 = f * ((n - 1) * (n - 1 - 1)) := by linarith
    have hf0 : 0 < f := hf1
    exact Nat.eq_of_mul_eq_mul_left hf0 (by linarith)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 3 - 1 = k + 2 by omega] at h1
  nlinarith

end Top

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
