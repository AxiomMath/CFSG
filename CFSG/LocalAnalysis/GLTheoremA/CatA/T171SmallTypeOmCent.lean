module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentPlanar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentKey
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentPos
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankSiegel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankTorus
public import CFSG.LocalAnalysis.AGLEmbedding.TimmesfeldRouteAux
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenWeir
public import CFSG.GroupTheory.WeirSylow.Orthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCMax
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCType
public import CFSG.Assembly.OpenBridges
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TStdCovDiag
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem centralizer_layer_eq_rot_plus_five (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} (hF : FrameOf Q Bb 4 l)
    {p : V × V} (hp : p ∈ l) {y : ↥(orthDerived Q)} (hyB : y ∈ Bb)
    (hyrot : (y : V ≃ₗ[ZMod 2] V) = rot Q p.1 p.2) :
    Bb ⊓ Subgroup.centralizer
        (GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl := hF.isFrame
  have hpp := hl.pair p hp
  have hyt : (y : V ≃ₗ[ZMod 2] V) ∈ torus Q l := by
    rw [hyrot]; exact rot_mem_torus hp
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := torus_pow_three hl _ hyt
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hy1 : y ≠ 1 := by
    intro h
    apply rot_ne_one hpp
    rw [← hyrot, h]
    rfl
  have hy3 : orderOf y = 3 := orderOf_eq_prime (Subtype.ext (by simpa using hy3')) hy1
  have hyfix : fixedSpace (y : V ≃ₗ[ZMod 2] V) = perpPlane Q p := by
    rw [hyrot]
    exact fixedSpace_eq_perpPlane hl hp (rot_mem_torus hp)
      (by rw [rot_apply_left hpp]; exact hpp.ne.symm)
      (fun q hq hne => rot_apply_left_of_ne hl hp hq (Ne.symm hne))
  have hyfin : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * 4 := by
    rw [hyfix, finrank_perpPlane hQ hpp, hdim]
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype) := by
    rw [hyfix]
    exact not_isPlusType_comp_perpPlane hQ hplus hpp
  obtain ⟨hlayer, -⟩ := layerIs_centralizer_planar hQ hy3 (m := 4) (by norm_num) (by omega)
    hyfin hminus
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    (oddOrderIsometry_three hQ hyO hy3').supportedFixedDerived_le_orthDerived
  rw [hlayer]
  apply le_antisymm
  · intro b hb'
    obtain ⟨hbBb, hbc⟩ := Subgroup.mem_inf.1 hb'
    have hbt : (b : V ≃ₗ[ZMod 2] V) ∈ torus Q l := hF.mem_torus hbBb
    have hbcy : b ∈ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (torus_commute hl hbt hyt).eq)
    have hschur := apply_eq_of_commute_supportedFixedDerived hQ hyO hy3'
      (by rw [hyfin]; norm_num)
      (mem_isometryCentralizer_of_mem_centralizer hbcy) (fun g hg => by
        have hgm : (⟨g, hAΩ hg⟩ : ↥(orthDerived Q)) ∈
            (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) :=
          Subgroup.mem_subgroupOf.2 hg
        exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hbc _ hgm)).symm)
    have hmem := mem_zpowers_rot_of_fixes_perpPlane hl hp hbt (fun w hw => hschur w (by
      rw [hyfix]
      exact hw))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, hyrot]
    exact hk
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨hyB, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hgc : g ∈ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) :=
      mem_centralizer_of_mem_isometryCentralizer
        (supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.1 hg))
    exact Subgroup.mem_centralizer_singleton_iff.1 hgc

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem card_eq_three_pow_four_of_smallModel_plus_five
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 5)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {Bb : Subgroup ↥(orthDerived Q)}
    (h : SmallModel ↥(orthDerived Q) Bb) : Nat.card Bb = 3 ^ 4 := by
  have hLift := CFSG.LocalAnalysis.GLTheoremA.S172B.liftableRank_orthDerived hQ hdim hplus (by norm_num) (by norm_num)
  obtain ⟨-, e, t, T, hEel, hEcard, -, -, hT2, hT1, hEnorm⟩ := hLift
  let E : Subgroup ↥(orthDerived Q) := Subgroup.closure (Set.range e)
  have hTwo : TwoLocal E := ⟨T, hT2, hT1, hEnorm⟩
  have hle := h.max E hEel hTwo
  rw [hEcard] at hle
  have hge : 3 ^ 4 ≤ Nat.card Bb := by simpa using hle
  have hle' : Nat.card Bb ≤ 3 ^ 4 := by simpa using h.card_le
  omega

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem not_smallOrd_layer_rot_plus_five (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} (hF : FrameOf Q Bb 4 l)
    {p : V × V} (hp : p ∈ l) {y : ↥(orthDerived Q)} (hyB : y ∈ Bb)
    (hyrot : (y : V ≃ₗ[ZMod 2] V) = rot Q p.1 p.2) :
    ¬ HStdExcl.SmallOrd (GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl := hF.isFrame
  have hpp := hl.pair p hp
  have hyt : (y : V ≃ₗ[ZMod 2] V) ∈ torus Q l := by
    rw [hyrot]; exact rot_mem_torus hp
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := torus_pow_three hl _ hyt
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hy1 : y ≠ 1 := by
    intro h
    apply rot_ne_one hpp
    rw [← hyrot, h]
    rfl
  have hy3 : orderOf y = 3 := orderOf_eq_prime (Subtype.ext (by simpa using hy3')) hy1
  have hyfix : fixedSpace (y : V ≃ₗ[ZMod 2] V) = perpPlane Q p := by
    rw [hyrot]
    exact fixedSpace_eq_perpPlane hl hp (rot_mem_torus hp)
      (by rw [rot_apply_left hpp]; exact hpp.ne.symm)
      (fun q hq hne => rot_apply_left_of_ne hl hp hq (Ne.symm hne))
  have hyfin : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * 4 := by
    rw [hyfix, finrank_perpPlane hQ hpp, hdim]
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype) := by
    rw [hyfix]
    exact not_isPlusType_comp_perpPlane hQ hplus hpp
  obtain ⟨hlayer, -⟩ := layerIs_centralizer_planar hQ hy3 (m := 4) (by norm_num) (by omega)
    hyfin hminus
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    (oddOrderIsometry_three hQ hyO hy3').supportedFixedDerived_le_orthDerived
  have hx := oddOrderIsometry_three hQ hyO hy3'
  let W := fixedSpace (y : V ≃ₗ[ZMod 2] V)
  have hWdim : finrank (ZMod 2) W = 2 * 4 := hyfin
  have hWminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp W.subtype) := hminus
  have hcardW : Nat.card ↥(orthDerived (Q.comp W.subtype)) = CFSG.Open.ordTwistedD 4 2 :=
    card_orthDerived_minus_eight hx.polarBilin_fixed_nondegenerate hWdim hWminus
  have hcardA : Nat.card ↥(supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)) =
      Nat.card ↥(orthDerived (Q.comp W.subtype)) :=
    Nat.card_congr (restrictDerivedEquiv hx).toEquiv
  have hcardLayer : Nat.card ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) =
      Nat.card ↥(orthDerived (Q.comp W.subtype)) := by
    rw [hlayer]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAΩ).toEquiv]
    exact hcardA
  have hT : ∃ U : Submodule (ZMod 2) W, finrank (ZMod 2) U = 3 ∧
      ∀ u ∈ U, (Q.comp W.subtype) u = 0 := by
    haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    exact CFSG.StandardType.OrthRestOdd.exists_totallySingular_three
      (R := Q.comp W.subtype) hx.polarBilin_fixed_nondegenerate (by omega)
  have hcenterW : Subgroup.center ↥(orthDerived (Q.comp W.subtype)) = ⊥ := by
    haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    exact CFSG.RankThree.PartOne.center_orthDerived_eq_bot
      hx.polarBilin_fixed_nondegenerate hT
  have hcenterA : Subgroup.center ↥(supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)) = ⊥ :=
    CFSG.AGLEmbedding.center_eq_bot_of_mulEquiv (restrictDerivedEquiv hx) hcenterW
  have hcenterLayer : Subgroup.center ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) = ⊥ := by
    rw [hlayer]
    exact CFSG.AGLEmbedding.center_eq_bot_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hAΩ) hcenterA
  intro hs
  unfold HStdExcl.SmallOrd at hs
  have hquot : Nat.card (↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) ⧸
      Subgroup.center ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))))) =
      Nat.card ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcenterLayer).trans
      QuotientGroup.quotientBot).toEquiv
  rw [hquot, hcardLayer, hcardW] at hs
  rw [CFSG.Open.ordTwistedD] at hs
  have hprod : (∏ x ∈ Finset.Icc 1 3, (2 ^ (2 * x) - 1)) = 2835 := by decide
  rw [hprod] at hs
  norm_num at hs

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem stdAt_rot_plus_five (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} (hF : FrameOf Q Bb 4 l)
    {p : V × V} (hp : p ∈ l) {y : ↥(orthDerived Q)} (hyB : y ∈ Bb)
    (hyrot : (y : V ≃ₗ[ZMod 2] V) = rot Q p.1 p.2) : StdAt Bb y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl := hF.isFrame
  have hpp := hl.pair p hp
  have hyt : (y : V ≃ₗ[ZMod 2] V) ∈ torus Q l := by
    rw [hyrot]; exact rot_mem_torus hp
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := torus_pow_three hl _ hyt
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hy1 : y ≠ 1 := by
    intro h
    apply rot_ne_one hpp
    rw [← hyrot, h]
    rfl
  have hy3 : orderOf y = 3 := orderOf_eq_prime (Subtype.ext (by simpa using hy3')) hy1
  have hyfix : fixedSpace (y : V ≃ₗ[ZMod 2] V) = perpPlane Q p := by
    rw [hyrot]
    exact fixedSpace_eq_perpPlane hl hp (rot_mem_torus hp)
      (by rw [rot_apply_left hpp]; exact hpp.ne.symm)
      (fun q hq hne => rot_apply_left_of_ne hl hp hq (Ne.symm hne))
  have hyfin : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * 4 := by
    rw [hyfix, finrank_perpPlane hQ hpp, hdim]
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype) := by
    rw [hyfix]
    exact not_isPlusType_comp_perpPlane hQ hplus hpp
  obtain ⟨-, hcomp⟩ := layerIs_centralizer_planar hQ hy3 (m := 4) (by norm_num) (by omega)
    hyfin hminus
  exact ⟨hcomp.1, centralizer_layer_eq_rot_plus_five hQ hdim hplus hF hp hyB hyrot⟩

theorem noSmallModel_plus_five (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    NoSmallModel ↥(orthDerived Q) := by
  intro Bb h
  have hcard := card_eq_three_pow_four_of_smallModel_plus_five hQ hdim hplus h
  have hLift := CFSG.LocalAnalysis.GLTheoremA.S172B.liftableRank_orthDerived hQ hdim hplus
    (by norm_num) (by norm_num)
  obtain ⟨l, hF⟩ := exists_frame_of_card hQ hLift.1 h.elem hcard
  have hne : l ≠ [] := by
    intro hnil
    have := hF.length_eq
    rw [hnil] at this
    simp at this
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil l hne
  obtain ⟨y, hyB, hyrot⟩ := hF.exists_mem_rot hp
  have hy1 : y ≠ 1 := by
    intro h1
    apply rot_ne_one (hF.isFrame.pair p hp)
    rw [← hyrot, h1]
    rfl
  exact not_smallOrd_layer_rot_plus_five hQ hdim hplus hF hp hyB hyrot
    (h.small y hyB hy1 (stdAt_rot_plus_five hQ hdim hplus hF hp hyB hyrot))

end CFSG.LocalAnalysis.GLTheoremA.T171S

end


public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem isPlusType_comp_perpPlane_of_minus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) {p : V × V} (hp : MinusPair Q p.1 p.2) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpPlane Q p).subtype) := by
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
  have htopForm : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (planeSpan p ⊔ perpPlane Q p).subtype) := by
    intro hplus
    exact hminus ((CFSG.GroupTheory.WeirSylow.isPlusType_congr
      (Q := Q.comp (planeSpan p ⊔ perpPlane Q p).subtype) (Q' := Q)
      { toLinearEquiv := LinearEquiv.ofTop (planeSpan p ⊔ perpPlane Q p) htop
        map_app' := fun x => rfl }).1 hplus)
  have hiff := isPlusType_sup_iff hdisj horthAB (nondeg_planeSpan hp) hBnd
    (d₁ := 1) (d₂ := 3) (by norm_num) (by norm_num) (hp.finrank_planeSpan)
    (by rw [finrank_perpPlane hQ hp, hdim])
  have hA : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (planeSpan p).subtype) :=
    not_isPlusType_planeSpan hp
  have hnot : ¬ (CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (planeSpan p).subtype) ↔
      CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpPlane Q p).subtype)) :=
    fun h => htopForm (hiff.mpr h)
  by_contra hB
  exact hnot ⟨fun hA' => absurd hA' hA, fun hB' => absurd hB' hB⟩

theorem card_le_three_pow_three_orthDerived_minus_eight
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (E : Subgroup ↥(orthDerived Q)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 3 := by
  have hEO : E.map (orthDerived Q).subtype ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.map_subtype_le E).trans (Subgroup.commutator_le_self _)
  have hE' : IsElemAbelian 3 (E.map (orthDerived Q).subtype) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  obtain ⟨l, hl, hEl⟩ := exists_frame_top hQ hEO hE'
  have hlen : l.length ≤ 3 := by
    by_contra hlt
    have h4 : 4 ≤ l.length := by omega
    have hle : 2 * l.length ≤ 2 * 4 := by
      rw [← hdim, ← hl.finrank_Wspan]
      exact Submodule.finrank_le _
    have hlen4 : l.length = 4 := by omega
    have hplusW : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (Wspan l).subtype) := by
      rw [isPlusType_Wspan_iff hl, hlen4]
      norm_num
    have htop : Wspan l = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hl.finrank_Wspan, hdim, hlen4]
    have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
      (CFSG.GroupTheory.WeirSylow.isPlusType_congr
        (Q := Q.comp (Wspan l).subtype) (Q' := Q)
        { toLinearEquiv := LinearEquiv.ofTop (Wspan l) htop
          map_app' := fun x => rfl }).1 hplusW
    exact hminus hplus
  calc Nat.card E = Nat.card (E.map (orthDerived Q).subtype) := by
        rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective]
    _ ≤ Nat.card (torus Q l) := Subgroup.card_le_of_le hEl
    _ = 3 ^ l.length := card_torus hl
    _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hlen

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem card_eq_three_pow_three_of_smallModel_minus_four
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) {Bb : Subgroup ↥(orthDerived Q)}
    (h : SmallModel ↥(orthDerived Q) Bb) : Nat.card Bb = 3 ^ 3 := by
  have hle := card_le_three_pow_three_orthDerived_minus_eight hQ hdim hminus Bb h.elem
  have hge : 3 ^ 3 ≤ Nat.card Bb := by simpa using h.card_ge
  omega

theorem layer_eq_rot_minus_four (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 4) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} (hF : FrameOf Q Bb 3 l)
    {p : V × V} (hp : p ∈ l) {y : ↥(orthDerived Q)} (hyB : y ∈ Bb)
    (hyrot : (y : V ≃ₗ[ZMod 2] V) = rot Q p.1 p.2) :
    GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) =
        (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) ∧
      IsComponentOf ((supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q))
        (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl := hF.isFrame
  have hpp := hl.pair p hp
  have hyt : (y : V ≃ₗ[ZMod 2] V) ∈ torus Q l := by
    rw [hyrot]; exact rot_mem_torus hp
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := torus_pow_three hl _ hyt
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hy1 : y ≠ 1 := by
    intro h
    apply rot_ne_one hpp
    rw [← hyrot, h]
    rfl
  have hy3 : orderOf y = 3 := orderOf_eq_prime (Subtype.ext (by simpa using hy3')) hy1
  have hyfix : fixedSpace (y : V ≃ₗ[ZMod 2] V) = perpPlane Q p := by
    rw [hyrot]
    exact fixedSpace_eq_perpPlane hl hp (rot_mem_torus hp)
      (by rw [rot_apply_left hpp]; exact hpp.ne.symm)
      (fun q hq hne => rot_apply_left_of_ne hl hp hq (Ne.symm hne))
  have hyfin : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * 3 := by
    rw [hyfix, finrank_perpPlane hQ hpp, hdim]
  have hx := oddOrderIsometry_three hQ hyO hy3'
  have hplusW : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype) := by
    rw [hyfix]
    exact isPlusType_comp_perpPlane_of_minus hQ hdim hminus hpp
  have hT : ∃ U : Submodule (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)),
      finrank (ZMod 2) U = 3 ∧ ∀ u ∈ U,
        (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype) u = 0 := by
    obtain ⟨U, hU, hU0⟩ := hplusW
    refine ⟨U, ?_, hU0⟩
    have h3 : 2 * finrank (ZMod 2) U = 6 := by
      rw [hU, hyfin]
    have h3' : 2 * finrank (ZMod 2) U = 2 * 3 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h3'
  have hAq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)) :=
    hx.isQuasisimple_supportedFixedDerived hT
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived
  set D : Subgroup ↥(orthDerived Q) :=
    (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) with hD
  have hDq : CFSG.IsQuasisimple ↥D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAΩ).symm hAq
  have hDC : D ≤ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) := fun g hg =>
    mem_centralizer_of_mem_isometryCentralizer
      (supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.1 hg))
  have hcomm := commutator_centralizer_le_supportedFixedDerived hQ hy3
    (by rw [hyfin]; omega)
  exact glaLayer_eq_of_commutator_le hDC hcomm hDq

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem centralizer_layer_eq_rot_minus_four (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 4) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} (hF : FrameOf Q Bb 3 l)
    {p : V × V} (hp : p ∈ l) {y : ↥(orthDerived Q)} (hyB : y ∈ Bb)
    (hyrot : (y : V ≃ₗ[ZMod 2] V) = rot Q p.1 p.2) :
    Bb ⊓ Subgroup.centralizer
        (GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl := hF.isFrame
  have hpp := hl.pair p hp
  have hyt : (y : V ≃ₗ[ZMod 2] V) ∈ torus Q l := by
    rw [hyrot]; exact rot_mem_torus hp
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := torus_pow_three hl _ hyt
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hy1 : y ≠ 1 := by
    intro h
    apply rot_ne_one hpp
    rw [← hyrot, h]
    rfl
  have hy3 : orderOf y = 3 := orderOf_eq_prime (Subtype.ext (by simpa using hy3')) hy1
  have hyfix : fixedSpace (y : V ≃ₗ[ZMod 2] V) = perpPlane Q p := by
    rw [hyrot]
    exact fixedSpace_eq_perpPlane hl hp (rot_mem_torus hp)
      (by rw [rot_apply_left hpp]; exact hpp.ne.symm)
      (fun q hq hne => rot_apply_left_of_ne hl hp hq (Ne.symm hne))
  have hyfin : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * 3 := by
    rw [hyfix, finrank_perpPlane hQ hpp, hdim]
  have hlayer := (layer_eq_rot_minus_four hQ hdim hminus hF hp hyB hyrot).1
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    (oddOrderIsometry_three hQ hyO hy3').supportedFixedDerived_le_orthDerived
  rw [hlayer]
  apply le_antisymm
  · intro b hb'
    obtain ⟨hbBb, hbc⟩ := Subgroup.mem_inf.1 hb'
    have hbt : (b : V ≃ₗ[ZMod 2] V) ∈ torus Q l := hF.mem_torus hbBb
    have hbcy : b ∈ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (torus_commute hl hbt hyt).eq)
    have hschur := apply_eq_of_commute_supportedFixedDerived hQ hyO hy3'
      (by rw [hyfin]; omega)
      (mem_isometryCentralizer_of_mem_centralizer hbcy) (fun g hg => by
        have hgm : (⟨g, hAΩ hg⟩ : ↥(orthDerived Q)) ∈
            (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) :=
          Subgroup.mem_subgroupOf.2 hg
        exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hbc _ hgm)).symm)
    have hmem := mem_zpowers_rot_of_fixes_perpPlane hl hp hbt (fun w hw => hschur w (by
      rw [hyfix]
      exact hw))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, hyrot]
    exact hk
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨hyB, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hgc : g ∈ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) :=
      mem_centralizer_of_mem_isometryCentralizer
        (supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.1 hg))
    exact Subgroup.mem_centralizer_singleton_iff.1 hgc

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem not_smallOrd_layer_rot_minus_four (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 4) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} (hF : FrameOf Q Bb 3 l)
    {p : V × V} (hp : p ∈ l) {y : ↥(orthDerived Q)} (hyB : y ∈ Bb)
    (hyrot : (y : V ≃ₗ[ZMod 2] V) = rot Q p.1 p.2) :
    ¬ HStdExcl.SmallOrd (GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl := hF.isFrame
  have hpp := hl.pair p hp
  have hyt : (y : V ≃ₗ[ZMod 2] V) ∈ torus Q l := by
    rw [hyrot]; exact rot_mem_torus hp
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := torus_pow_three hl _ hyt
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hy1 : y ≠ 1 := by
    intro h
    apply rot_ne_one hpp
    rw [← hyrot, h]
    rfl
  have hy3 : orderOf y = 3 := orderOf_eq_prime (Subtype.ext (by simpa using hy3')) hy1
  have hyfix : fixedSpace (y : V ≃ₗ[ZMod 2] V) = perpPlane Q p := by
    rw [hyrot]
    exact fixedSpace_eq_perpPlane hl hp (rot_mem_torus hp)
      (by rw [rot_apply_left hpp]; exact hpp.ne.symm)
      (fun q hq hne => rot_apply_left_of_ne hl hp hq (Ne.symm hne))
  have hyfin : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * 3 := by
    rw [hyfix, finrank_perpPlane hQ hpp, hdim]
  have hplusW : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype) := by
    rw [hyfix]
    exact isPlusType_comp_perpPlane_of_minus hQ hdim hminus hpp
  have hlayer := (layer_eq_rot_minus_four hQ hdim hminus hF hp hyB hyrot).1
  have hx := oddOrderIsometry_three hQ hyO hy3'
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived
  let W := fixedSpace (y : V ≃ₗ[ZMod 2] V)
  have hWdim : finrank (ZMod 2) W = 2 * 3 := hyfin
  have hcardW : Nat.card ↥(orthDerived (Q.comp W.subtype)) = 20160 :=
    card_orthDerived_plus_six hx.polarBilin_fixed_nondegenerate hWdim hplusW
  have hcardA : Nat.card ↥(supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)) =
      Nat.card ↥(orthDerived (Q.comp W.subtype)) :=
    Nat.card_congr (restrictDerivedEquiv hx).toEquiv
  have hcardLayer : Nat.card ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) =
      Nat.card ↥(orthDerived (Q.comp W.subtype)) := by
    rw [hlayer]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAΩ).toEquiv]
    exact hcardA
  have hT : ∃ U : Submodule (ZMod 2) W, finrank (ZMod 2) U = 3 ∧
      ∀ u ∈ U, (Q.comp W.subtype) u = 0 := by
    obtain ⟨U, hU, hU0⟩ := hplusW
    refine ⟨U, ?_, hU0⟩
    have h3 : 2 * finrank (ZMod 2) U = 6 := by
      rw [hU, hyfin]
    have h3' : 2 * finrank (ZMod 2) U = 2 * 3 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h3'
  have hcenterW : Subgroup.center ↥(orthDerived (Q.comp W.subtype)) = ⊥ := by
    haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    exact CFSG.RankThree.PartOne.center_orthDerived_eq_bot
      hx.polarBilin_fixed_nondegenerate hT
  have hcenterA : Subgroup.center ↥(supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)) = ⊥ :=
    CFSG.AGLEmbedding.center_eq_bot_of_mulEquiv (restrictDerivedEquiv hx) hcenterW
  have hcenterLayer : Subgroup.center ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) = ⊥ := by
    rw [hlayer]
    exact CFSG.AGLEmbedding.center_eq_bot_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hAΩ) hcenterA
  intro hs
  unfold HStdExcl.SmallOrd at hs
  have hquot : Nat.card (↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) ⧸
      Subgroup.center ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))))) =
      Nat.card ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcenterLayer).trans
      QuotientGroup.quotientBot).toEquiv
  rw [hquot, hcardLayer, hcardW] at hs
  norm_num at hs

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem stdAt_rot_minus_four (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 4) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} (hF : FrameOf Q Bb 3 l)
    {p : V × V} (hp : p ∈ l) {y : ↥(orthDerived Q)} (hyB : y ∈ Bb)
    (hyrot : (y : V ≃ₗ[ZMod 2] V) = rot Q p.1 p.2) : StdAt Bb y := by
  refine ⟨?_, centralizer_layer_eq_rot_minus_four hQ hdim hminus hF hp hyB hyrot⟩
  rw [(layer_eq_rot_minus_four hQ hdim hminus hF hp hyB hyrot).1]
  exact (layer_eq_rot_minus_four hQ hdim hminus hF hp hyB hyrot).2

theorem noSmallModel_minus_four (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 4) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    NoSmallModel ↥(orthDerived Q) := by
  intro Bb h
  have hcard := card_eq_three_pow_three_of_smallModel_minus_four hQ hdim hminus h
  obtain ⟨l, hF⟩ := exists_frame_of_card (n := 4) hQ
    (card_le_three_pow_three_orthDerived_minus_eight hQ hdim hminus) h.elem hcard
  have hne : l ≠ [] := by
    intro hnil
    have := hF.length_eq
    rw [hnil] at this
    simp at this
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil l hne
  obtain ⟨y, hyB, hyrot⟩ := hF.exists_mem_rot hp
  have hy1 : y ≠ 1 := by
    intro h1
    apply rot_ne_one (hF.isFrame.pair p hp)
    rw [← hyrot, h1]
    rfl
  exact not_smallOrd_layer_rot_minus_four hQ hdim hminus hF hp hyB hyrot
    (h.small y hyB hy1 (stdAt_rot_minus_four hQ hdim hminus hF hp hyB hyrot))

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
