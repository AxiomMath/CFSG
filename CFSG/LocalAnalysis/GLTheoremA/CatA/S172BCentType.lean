module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountOmega
import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubCore
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCFinal
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X

section Minus

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

private theorem not_isPlusType_comp_perpPlane_aux1
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {p : V × V} (hp : MinusPair Q p.1 p.2) :
    4 ≤ finrank (ZMod 2) V := by
  obtain ⟨W, hW, hWs⟩ := hplus
  have h2 : 2 ≤ finrank (ZMod 2) V := by
    have hle := Submodule.finrank_le (planeSpan p)
    rw [hp.finrank_planeSpan] at hle
    omega
  have hne2 : finrank (ZMod 2) V ≠ 2 := by
    intro hV2
    have htopA : planeSpan p = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hp.finrank_planeSpan, hV2]
    have hW1 : finrank (ZMod 2) W = 1 := by omega
    have hWne : W ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hW1
      omega
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hwA : w ∈ planeSpan p := by rw [htopA]; trivial
    have h1 := Q_eq_one_of_mem_planeSpan hp hwA hw0
    rw [hWs w hw] at h1
    exact zero_ne_one h1
  omega

theorem not_isPlusType_comp_perpPlane (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {p : V × V} (hp : MinusPair Q p.1 p.2) :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpPlane Q p).subtype) := by
  have hplus' := hplus
  obtain ⟨W, hW, -⟩ := hplus'
  have hdimV : 4 ≤ finrank (ZMod 2) V :=
    not_isPlusType_comp_perpPlane_aux1 hplus hp
  have hframe : IsFrame Q [p] :=
    IsFrame.cons hp (fun q hq => absurd hq (List.not_mem_nil)) IsFrame.nil
  have hWsp : Wspan [p] = planeSpan p := by rw [Wspan_cons, Wspan_nil, sup_bot_eq]
  have hP : perpL Q [p] = perpPlane Q p := by rw [perpL, perpPlane, hWsp]
  have hcompl := hframe.isCompl
  have htop : planeSpan p ⊔ perpPlane Q p = ⊤ := by rw [← hWsp, ← hP]; exact hcompl.sup_eq_top
  have hdisj : Disjoint (planeSpan p) (perpPlane Q p) := by
    rw [← hWsp, ← hP]; exact hcompl.disjoint
  have horthAB : ∀ a ∈ planeSpan p, ∀ b ∈ perpPlane Q p, polar Q a b = 0 := by
    intro a ha b hb
    obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p a).1 ha
    obtain ⟨h1, h2⟩ := (mem_perpPlane_iff p b).1 hb
    rw [polar_add_left, polar_smul_left, polar_smul_left, h1, h2]
    simp
  have hBnd : (QuadraticMap.polarBilin (Q.comp (perpPlane Q p).subtype)).Nondegenerate := by
    refine nondeg_comp_subtype (fun x hx hxy => ?_)
    refine hQ.1 x (fun y => ?_)
    rw [QuadraticMap.polarBilin_apply_apply]
    have hy : y ∈ planeSpan p ⊔ perpPlane Q p := by rw [htop]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    have hxa : polar Q x a = 0 := by
      obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p a).1 ha
      obtain ⟨h1, h2⟩ := (mem_perpPlane_iff' p x).1 hx
      rw [polar_add_right, polar_smul_right, polar_smul_right, h1, h2]
      simp
    rw [polar_add_right, hxa, hxy b hb, add_zero]
  have htopForm : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (planeSpan p ⊔ perpPlane Q p).subtype) :=
    (CFSG.GroupTheory.WeirSylow.isPlusType_congr
      (Q := Q.comp (planeSpan p ⊔ perpPlane Q p).subtype) (Q' := Q)
      { toLinearEquiv := LinearEquiv.ofTop (planeSpan p ⊔ perpPlane Q p) htop
        map_app' := fun m => rfl }).2 hplus
  have hiff := (isPlusType_sup_iff hdisj horthAB (nondeg_planeSpan hp) hBnd
      (d₁ := 1) (d₂ := finrank (ZMod 2) W - 1) (le_refl 1) (by omega)
      (hp.finrank_planeSpan) (by rw [finrank_perpPlane hQ hp]; omega)).1 htopForm
  exact fun hB => not_isPlusType_planeSpan hp (hiff.mpr hB)

end Minus

section Bridge

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {R : QuadraticForm (ZMod 2) W}

private theorem catalogIs_pSimple_top_orthDerived_minus_aux1
    (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {m : ℕ} (hm : 4 ≤ m) (hdim : finrank (ZMod 2) W = 2 * m) :
    Nonempty (PSimple 3 (⊤ : Subgroup ↥(orthDerived R)) ≃* ↥(orthDerived R)) := by
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank (ZMod 2) W)
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  haveI : Finite (W ≃ₗ[ZMod 2] W) := finite_linearEquiv
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim R hR hm hdim
  have hZ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT
  have hq := CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT
  haveI hsimple : IsSimpleGroup (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) := hq.2.1
  let e : (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) ≃* ↥(orthDerived R) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup ↥(orthDerived R) := e.symm.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hq.2.2
  have hncR : ∃ x y : ↥(orthDerived R), x * y ≠ y * x :=
    ⟨e a, e b, fun h => hab (by simpa using congrArg e.symm h)⟩
  obtain ⟨u, v, huv⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.exists_minusPair R hR
    (by omega : 3 ≤ finrank (ZMod 2) W)
  have hmem : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.rot R u v ∈ orthDerived R :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.rot_mem_commutator huv
  have hne : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.rot R u v ≠ 1 := by
    intro h1
    have h2 : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.rot R u v u = u := by
      rw [h1, LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]
    rw [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.rot_apply_left huv] at h2
    have huv' : u ≠ v := by
      intro huv_eq
      have := huv.ab
      rw [huv_eq, huv.bb] at this
      exact zero_ne_one this
    exact huv' h2.symm
  have hord : orderOf (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.rot R u v) = 3 :=
    orderOf_eq_prime (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.rot_pow_three huv) hne
  have hdvd0 : 3 ∣ Nat.card ↥(orthDerived R) := by
    have h := Subgroup.orderOf_dvd_natCard (orthDerived R) hmem
    rwa [hord] at h
  have hnc : ∃ x y : ↥(⊤ : Subgroup ↥(orthDerived R)), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hncR
    exact ⟨Subgroup.topEquiv.symm x, Subgroup.topEquiv.symm y,
      fun h => hxy (by simpa using congrArg Subgroup.topEquiv h)⟩
  have hdvd : 3 ∣ Nat.card ↥(⊤ : Subgroup ↥(orthDerived R)) := by
    rwa [Subgroup.card_top]
  haveI : IsSimpleGroup ↥(⊤ : Subgroup ↥(orthDerived R)) := Subgroup.topEquiv.isSimpleGroup
  exact ⟨(CFSG.LocalAnalysis.GLTheoremA.H1429Sub.pSimple_equiv_self (T := ↥(orthDerived R))
    (J := ⊤) inferInstance hnc hdvd).trans Subgroup.topEquiv⟩

private theorem catalogIs_pSimple_top_orthDerived_minus_aux2
    (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {m : ℕ} (hm : 4 ≤ m) (hdim : finrank (ZMod 2) W = 2 * m)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType R)
    (q : TauCeti.PrimePower) (hp : q.p = 2) (hexp : q.exponent = 1)
    (hv : (TauCeti.LieTypeIndex.twistedD m q).Valid) :
    Nonempty (↥(orthDerived R) ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩) := by
  obtain ⟨b, c, hirr, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj m q hv hp
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fintype ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩) :=
    Fintype.ofFinite _
  have hK' : Fintype.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩) = 2 := by
    rw [← Nat.card_eq_fintype_card, TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_twistedD, TauCeti.LieTypeIndex.fieldExponent_twistedD,
      hp, hexp]
    norm_num
  let σ : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩) ≃+* ZMod 2 :=
    (ZMod.ringEquivOfPrime _ Nat.prime_two hK').symm
  have hZ2 : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hirrZ : ∀ s : ZMod 2, s ^ 2 + σ b * s + σ c ≠ 0 := by
    intro s hs
    apply hirr (σ.symm s)
    apply σ.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  obtain ⟨eiso⟩ :=
    CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType hR (by omega) hdim hminus hirrZ
  let e1 : StatedProj (StatedOmega (StatedQuadMinus m ↥(TauCeti.ValidLieTypeIndex.fixedField
        ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩) b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus m (ZMod 2) (σ b) (σ c))) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr σ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp σ rfl rfl v))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars σ)
  let e2 : StatedProj (StatedOmega (StatedQuadMinus m (ZMod 2) (σ b) (σ c))) ≃*
      StatedOmega (StatedQuadMinus m (ZMod 2) (σ b) (σ c)) :=
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.omStatedProjEquivOfCardTwo hZ2
      (StatedOmega (StatedQuadMinus m (ZMod 2) (σ b) (σ c)))).symm
  let e3 : StatedOmega (StatedQuadMinus m (ZMod 2) (σ b) (σ c)) ≃*
      ↥(orthDerived (CFSG.LieType.Universal.Spin.quadMinus m (ZMod 2) (σ b) (σ c))) :=
    CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
      (CFSG.LieType.Universal.Spin.quadMinus m (ZMod 2) (σ b) (σ c))
      (CFSG.LieType.Universal.Spin.coe_quadMinus m (ZMod 2) (σ b) (σ c))
  exact ⟨(CFSG.RankThree.PartOne.orthDerivedEquiv eiso).trans
    (e3.symm.trans (e2.symm.trans (e1.symm.trans φ.symm)))⟩

theorem catalogIs_pSimple_top_orthDerived_minus (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {m : ℕ} (hm : 4 ≤ m) (hdim : finrank (ZMod 2) W = 2 * m)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType R) :
    catalogIs (PSimple 3 (⊤ : Subgroup ↥(orthDerived R))) (isOmMA m 2) := by
  obtain ⟨e₁⟩ := catalogIs_pSimple_top_orthDerived_minus_aux1 hR hm hdim
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hp : q.p = 2 := rfl
  have hexp : q.exponent = 1 := rfl
  have hv : (TauCeti.LieTypeIndex.twistedD m q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩
  obtain ⟨e₂⟩ := catalogIs_pSimple_top_orthDerived_minus_aux2 hR hm hdim hminus q hp hexp hv
  refine ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD m q, hv⟩, ?_, ⟨e₁.trans e₂⟩⟩
  left
  show m = m ∧ q.card = 2
  exact ⟨rfl, by rw [TauCeti.PrimePower.card_def, hp, hexp]; norm_num⟩

end Bridge

section Transport

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem catalogIs_pSimple_supportedFixedDerived_minus
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : ↥(orthDerived Q)} (hx3 : orderOf x = 3)
    {m : ℕ} (hm : 4 ≤ m) (hdim : finrank (ZMod 2) (fixedSpace (x : V ≃ₗ[ZMod 2] V)) = 2 * m)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (x : V ≃ₗ[ZMod 2] V)).subtype)) :
    catalogIs (PSimple 3 ((supportedFixedDerived Q (x : V ≃ₗ[ZMod 2] V)).subgroupOf
      (orthDerived Q))) (isOmMA m 2) := by
  have hpl : (3 : ℕ) ≠ ringChar (ZMod 2) := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  have hx := oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3
  have h1 := catalogIs_pSimple_top_orthDerived_minus hx.polarBilin_fixed_nondegenerate hm hdim hminus
  let e : ↥((supportedFixedDerived Q (x : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q)) ≃*
      ↥(⊤ : Subgroup ↥(orthDerived (Q.comp (fixedSpace (x : V ≃ₗ[ZMod 2] V)).subtype))) :=
    (Subgroup.subgroupOfEquivOfLe hx.supportedFixedDerived_le_orthDerived).trans
      ((supportedFixedDerivedEquiv hx).trans Subgroup.topEquiv.symm)
  exact (catalogIs_pSimple_congr_mulEquiv e 3 _).2 h1

end Transport

section Arith

theorem false_of_catalogIs_isUnA_isOmMA (hb : CatDistinct.OrderBridge) {S : Type} [Group S]
    [Finite S] {m : ℕ} (h1 : catalogIs S (isUnA m 2)) (h2 : catalogIs S (isOmMA m 2)) : False := by
  obtain ⟨-, -, hu⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isUnA (f := 1) hb le_rfl h1
  obtain ⟨hm3, hv⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isOmMA (f := 1) hb le_rfl h2
  rw [hv] at hu
  have : 0 < m * (m - 1) := Nat.mul_pos (by omega) (by omega)
  omega

end Arith

section Top

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

private theorem card_pSimple_glaLayer_top_orthDerived_aux1 {Q : Type} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem card_pSimple_glaLayer_top_orthDerived_aux2 {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Nontrivial V] (H : Subgroup (V ≃ₗ[ZMod 2] V)) :
    (CFSG.ClassicalGroups.Orthogonal.scalars (ZMod 2) V).subgroupOf H = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  rw [Subgroup.mem_bot]
  obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.1 hg
  have hc1 : c = 1 := by
    rcases CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.zmod_two_cases c with h | h
    · exfalso
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have h0 : (g : V ≃ₗ[ZMod 2] V) v = 0 := by rw [hc v, h, zero_smul]
      exact hv ((g : V ≃ₗ[ZMod 2] V).injective (by rw [h0, map_zero]))
    · exact h
  apply Subtype.ext
  ext v
  rw [hc v, hc1]
  simp

private theorem card_pSimple_glaLayer_top_orthDerived_aux3 {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hcenter : Subgroup.center G = ⊥) (h3 : 3 ∣ Nat.card G) :
    Nat.card (PSimple 3 (⊤ : Subgroup G)) = Nat.card G := by
  have hcenterK : Subgroup.center ↥(⊤ : Subgroup G) = ⊥ := by
    have h1 := Subgroup.map_center_eq (Subgroup.topEquiv (G := G))
    rw [hcenter] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.topEquiv (G := G)).injective).1 h1
  have hsimpleK : IsSimpleGroup ↥(⊤ : Subgroup G) := by
    haveI := hsimple
    exact (Subgroup.topEquiv (G := G)).isSimpleGroup
  have hdvdK : 3 ∣ Nat.card ↥(⊤ : Subgroup G) := by
    rw [Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv]
    exact h3
  have hcoreK : GLAPPrimeCore 3 ↥(⊤ : Subgroup G) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥(⊤ : Subgroup G)) with h | h
    · exact h
    · exfalso
      have hc := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
        Nat.prime_three ↥(⊤ : Subgroup G)
      rw [h, Subgroup.card_top] at hc
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc hdvdK
  let ePQ : PQuot 3 (⊤ : Subgroup G) ≃* ↥(⊤ : Subgroup G) :=
    (QuotientGroup.quotientMulEquivOfEq hcoreK).trans QuotientGroup.quotientBot
  have hZP : Subgroup.center (PQuot 3 (⊤ : Subgroup G)) = ⊥ := by
    have h1 := Subgroup.map_center_eq ePQ
    rw [hcenterK] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ ePQ.injective).1 h1
  let ePS : PSimple 3 (⊤ : Subgroup G) ≃* ↥(⊤ : Subgroup G) :=
    (QuotientGroup.quotientMulEquivOfEq hZP).trans (QuotientGroup.quotientBot.trans ePQ)
  calc Nat.card (PSimple 3 (⊤ : Subgroup G))
      = Nat.card ↥(⊤ : Subgroup G) := Nat.card_congr ePS.toEquiv
    _ = Nat.card G := Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv

private theorem card_pSimple_glaLayer_top_orthDerived_aux4
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hn : 4 ≤ n) :
    3 ∣ Nat.card ↥(orthDerived Q) := by
  obtain ⟨a, b, hab⟩ := exists_minusPair Q hQ (by omega)
  let r : ↥(orthDerived Q) := ⟨rot Q a b, rot_mem_commutator hab⟩
  have hr3 : r ^ 3 = 1 := Subtype.ext (rot_pow_three hab)
  have hr1 : r ≠ 1 := by
    intro h
    have h2 := congrArg (fun g : ↥(orthDerived Q) => (g : V ≃ₗ[ZMod 2] V) a) h
    simp only [Subtype.coe_mk, OneMemClass.coe_one, LinearEquiv.coe_one, id_eq] at h2
    rw [rot_apply_left hab] at h2
    exact hab.ne h2.symm
  have hord : orderOf r = 3 := orderOf_eq_prime hr3 hr1
  have hdvd := orderOf_dvd_natCard r
  rwa [hord] at hdvd

theorem card_pSimple_glaLayer_top_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 4 ≤ n) :
    Nat.card (PSimple 3 (GLALayer (⊤ : Subgroup ↥(orthDerived Q)))) =
      Nat.card ↥(orthDerived Q) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  have hT : ∃ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 3 ∧ ∀ u ∈ U, Q u = 0 :=
    CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hn hdim
  have hq : CFSG.IsQuasisimple ↥(orthDerived Q) := isQuasisimple_orthDerived hQ hT
  have hqOpen : CFSG.Open.IsQuasisimple ↥(orthDerived Q) :=
    card_pSimple_glaLayer_top_orthDerived_aux1 hq
  have hscal := card_pSimple_glaLayer_top_orthDerived_aux2 (V := V) (orthDerived Q)
  have hcenter : Subgroup.center ↥(orthDerived Q) = ⊥ := by
    obtain ⟨-, hc, -, -, -, -, -, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
    rw [hc, hscal]
  have hsimple : IsSimpleGroup ↥(orthDerived Q) := by
    haveI := hq.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hcomp : IsComponentOf (⊤ : Subgroup ↥(orthDerived Q)) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv) hqOpen⟩
  have hLayer : GLALayer (⊤ : Subgroup ↥(orthDerived Q)) = ⊤ := by
    rw [show GLALayer (⊤ : Subgroup ↥(orthDerived Q)) =
      sSup {K | IsComponentOf K (⊤ : Subgroup ↥(orthDerived Q))} from rfl]
    exact le_antisymm (sSup_le fun K _ => le_top) (le_sSup hcomp)
  rw [hLayer]
  exact card_pSimple_glaLayer_top_orthDerived_aux3 hsimple hcenter
    (card_pSimple_glaLayer_top_orthDerived_aux4 hQ hdim hn)

theorem v2_card_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hn : 4 ≤ n) : padicValNat 2 (Nat.card ↥(orthDerived Q)) = n * (n - 1) := by
  have hT : ∃ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 3 ∧ ∀ u ∈ U, Q u = 0 :=
    CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hn hdim
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  have hcard : Nat.card ↥(orthDerived Q) = CFSG.Open.orderD n 2 := by
    have h := CFSG.StandardType.card_orthDerived_eq_ordD (K := ZMod 2) (W := V) Q hQ
      (m := n - 1) (by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]; exact hdim) hΩ hplus
    rw [show n - 1 + 1 = n by omega] at h
    rw [h, show Nat.card (ZMod 2) = 2 by rw [Nat.card_eq_fintype_card, ZMod.card]]
    rfl
  obtain ⟨m', hm', hmul⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S172.orderD_two_pow (n := n) (f := 1) (by omega) le_rfl
  have hfinal : padicValNat 2 (CFSG.Open.orderD n 2) = n * (n - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.S172.v2_of_odd_mul hm' (by simpa using hmul)
  rw [hcard, hfinal]

theorem not_layerIs_top_isUnA (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hn : 5 ≤ n) (hb : CatDistinct.OrderBridge) :
    ¬ LayerIs 3 (⊤ : Subgroup ↥(orthDerived Q)) (isUnA (n - 1) 2) := by
  intro hL
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hcard := card_pSimple_glaLayer_top_orthDerived hQ hdim (by omega)
  have hv := v2_card_orthDerived hQ hdim hplus (by omega)
  obtain ⟨-, -, hu⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isUnA (f := 1) hb le_rfl hL.2
  rw [hcard, hv] at hu
  have h1 : n * (n - 1) * 2 = (n - 1) * (n - 1 - 1) := by
    rw [mul_comm] at hu
    simpa [mul_comm, mul_assoc, mul_left_comm] using hu
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 4 - 1 = k + 3 by omega] at h1
  nlinarith

end Top

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end

