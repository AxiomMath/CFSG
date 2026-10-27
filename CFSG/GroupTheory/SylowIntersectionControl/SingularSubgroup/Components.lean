module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.ModuleSetting
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLemma44
public import CFSG.GroupTheory.SylowIntersectionControl.GomiBender
public import CFSG.GroupTheory.SylowIntersectionControl.GomiBenderSL2
import CFSG.GroupTheory.SpecialLinearTwoAlternating
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeOffender
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L6Gen
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedBender
import CFSG.GroupTheory.SubgroupOfLattice
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2V1
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129d
import CFSG.Quasithin.Background.G64Case1Pre
import CFSG.Quasithin.Background.B53FFJImage
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.GroupTheory.SylowIntersectionControl.Regular
import CFSG.GroupTheory.ConjTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBLTwo
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SylowIntersectionControl.Quotient
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedStronglyEmbedded
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2Conj

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open scoped IsMulCommutative

section Module

variable {W : Type} [CommGroup W]

structure IsGomiStepE (Y Sb Lb : Subgroup (MulAut W)) : Prop where
  le : Lb ≤ Y
  mem_or : ((gomiPstar0Set Y).Nonempty ∧ Lb ∈ gomiNSet Y) ∨
    (gomiPstar0Set Y = ∅ ∧ Lb ≤ gomiGstar1 Y ∧
      CFSG.IsComponent (Lb.subgroupOf (gomiGstar1 Y)))
  commute : ∀ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom ≠ Lb →
    ∀ a ∈ Lb, ∀ b ∈ Lb.map (MulAut.conj y).toMonoidHom, a * b = b * a
  sup_eq : (⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom) ⊔ Sb = Y
  type : IsSLn ↥Lb 2 1 ∨ GomiHyp43Type ↥Lb

@[expose] def IsGomiStepF (Sb Lb : Subgroup (MulAut W)) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ IsSLn ↥Lb 2 m) ∨
    (IsGomiChevTwo ↥Lb ∧
      (IsGomiL3 (↥Lb ⧸ Subgroup.center ↥Lb) ∨ IsGomiSp4 (↥Lb ⧸ Subgroup.center ↥Lb)) ∧
      IsGomiParabolicSwap Sb Lb) ∨
    ∃ m : ℕ, 3 ≤ m ∧ IsAlt ↥Lb (2 ^ m + 1)

@[expose] def IsGomiStepG (Lb : Subgroup (MulAut W)) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ IsSLn ↥Lb 2 m ∧ BinaryNaturalSL Lb (commV Lb) (gomiWXKer Lb) 2 m) ∨
    ∃ m : ℕ, 2 ≤ m ∧ IsAlt ↥Lb (2 ^ m + 1) ∧
      (FFModel.altDn (2 ^ m + 1)).Realizes Lb (commV Lb) (gomiWXKer Lb)

end Module

namespace GomiThm45Counterexample

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

theorem pset_nonempty (h : GomiThm45Counterexample c G S) :
    (Pset (autOn G (gomiV G))).Nonempty := by
  by_contra hne
  have hne' : Pset (autOn G (gomiV G)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun A hA => hne ⟨A, hA⟩
  apply not_thompsonJ_le_centralizer h
  have hV : CFSG.Open.IsElemAbelian 2 (gomiV G) := (gomiV_moduleSetting G).1
  have hVS : gomiV G ≤ S :=
    (CFSG.Quasithin.A4.omegaOneCenterOf_le (pCoreOf 2 G)).trans
      (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf)
  have hVG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  rw [thompsonJ]
  refine iSup₂_le fun A hA => ?_
  by_contra hAc
  have hAG : A ≤ G := hA.1.trans h.isSylowTwoOf.1
  have hmem : autOn A (gomiV G) ∈ Pset (autOn G (gomiV G)) :=
    CFSG.AGLEmbedding.AscTenThree.isFFStarOffender_autOn_of_isMaxElemAbelian
      (H := G) (V := gomiV G) (S := S) (A := A) hV hVS hVG hAG hA hAc
  exact (Set.eq_empty_iff_forall_notMem.mp hne') _ hmem

private theorem pCore_eq_bot_of_isComponent_g45e
    {Lb Y : Subgroup (MulAut ↥(gomiV G))}
    (hO2 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O2Trivial Y)
    (hLY : Lb ≤ Y) (hcomp : CFSG.IsComponent (Lb.subgroupOf Y)) :
    CFSG.pCore 2 ↥Lb = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpcY : CFSG.Open.pCoreOf 2 Y = ⊥ := by
    by_contra hne
    refine hne (hO2 (CFSG.Open.pCoreOf 2 Y) (CFSG.openPCoreOf_le 2 Y) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y))
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.openPCoreOf_le 2 Y)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hLbY : CFSG.Open.IsSubnormal Lb Y :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hLY).mpr hcomp.2
  have hpcLb : CFSG.Open.IsSubnormal (CFSG.Open.pCoreOf 2 Lb) Lb :=
    CFSG.Open.IsSubnormal.step (CFSG.LieType.BorelTits.pCoreOf_le 2 Lb)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 Lb)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lb))
      (CFSG.Open.IsSubnormal.refl Lb)
  have hsn : CFSG.Open.IsSubnormal (CFSG.Open.pCoreOf 2 Lb) Y :=
    CFSG.Open.IsSubnormal.trans hpcLb hLbY
  have hp : IsPGroup 2 (CFSG.Open.pCoreOf 2 Lb) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lb
  have hle : CFSG.Open.pCoreOf 2 Lb ≤ CFSG.Open.pCoreOf 2 Y :=
    CFSG.Quasithin.F6.le_pCoreOf_of_isSubnormal hsn hp
  have hbot : CFSG.Open.pCoreOf 2 Lb = ⊥ :=
    le_bot_iff.mp (hle.trans (le_of_eq hpcY))
  rw [← CFSG.openPCoreOf_subgroupOf 2 Lb, hbot, Subgroup.bot_subgroupOf]

private theorem iSup_conj_sup_eq_of_even_g45e
    (h : GomiThm45Counterexample c G S) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hLY : Lb ≤ autOn G (gomiV G)) (heven : Even (Nat.card Lb)) :
    (⨆ y ∈ autOn G (gomiV G), Lb.map (MulAut.conj y).toMonoidHom) ⊔
      autOn S (gomiV G) = autOn G (gomiV G) := by
  set Y := autOn G (gomiV G)
  set N : Subgroup (MulAut ↥(gomiV G)) :=
    ⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom with hN
  have hNY : N ≤ Y := by
    refine iSup₂_le fun y hy => ?_
    rintro z ⟨l, hl, rfl⟩
    change y * (l : MulAut ↥(gomiV G)) * y⁻¹ ∈ Y
    exact Y.mul_mem (Y.mul_mem hy (hLY hl)) (Y.inv_mem hy)
  have hNnorm : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr
      (le_normalizer_iSup_map_conj Y Lb)
  have hLbN : Lb ≤ N := by
    refine le_iSup₂_of_le (f := fun y (_ : y ∈ Y) =>
      Lb.map (MulAut.conj y).toMonoidHom) (1 : MulAut ↥(gomiV G)) (one_mem Y) ?_
    change Lb ≤ Subgroup.map (MonoidHom.id (MulAut ↥(gomiV G))) Lb
    rw [Subgroup.map_id]
  have h2 : 2 ∣ Nat.card N :=
    (even_iff_two_dvd.mp heven).trans (Subgroup.card_dvd_of_le hLbN)
  simpa [hN] using sup_autOn_eq h hNY hNnorm h2

private theorem exists_isGomiStepE_of_pstar0_g45e
    (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    (h0 : (gomiPstar0Set (autOn G (gomiV G))).Nonempty) :
    ∃ Lb : Subgroup (MulAut ↥(gomiV G)),
      IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb := by
  set Y := autOn G (gomiV G)
  set Sb := autOn S (gomiV G)
  obtain ⟨A, hA⟩ := h0
  have h0' : (gomiPstar0Set Y).Nonempty := ⟨A, hA⟩
  set Lb : Subgroup (MulAut ↥(gomiV G)) := gomiOrbitSpan Y A with hLb
  have hNmem : Lb ∈ gomiNSet Y := ⟨A, hA, hLb⟩
  have hLbY : Lb ≤ Y := le_of_mem_gomiNSet hNmem
  have hO2 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O2Trivial
      (gomiGstar0 Y) :=
    o2Trivial_of_normal (o2Trivial_autOn h) (gomiGstar0_le Y) (gomiGstar0_subgroupOf_normal Y)
  obtain ⟨⟨hSL, -, hpair, -⟩, -⟩ :=
    h31 ↥(gomiV G)
      (fun w => Subtype.ext (by simpa using (gomiV_moduleSetting G).1.2 w w.2)) Y h0' hO2
  have htype : IsSLn ↥Lb 2 1 := hSL Lb hNmem
  have heven : Even (Nat.card Lb) := by
    rw [card_eq_of_isSLn_two htype]
    decide
  refine ⟨Lb, hLbY, Or.inl ⟨h0', hNmem⟩, ?_, ?_, Or.inl htype⟩
  · intro y hy hne a ha b hb
    exact hpair hNmem (map_conj_mem_gomiNSet hNmem hy) (Ne.symm hne) a ha b hb
  · exact iSup_conj_sup_eq_of_even_g45e h hLbY heven

private theorem exists_component_gomiGstar1_g45e
    (h : GomiThm45Counterexample c G S) (h33 : GomiFact33)
    (h0 : gomiPstar0Set (autOn G (gomiV G)) = ∅) :
    ∃ K : Subgroup ↥(gomiGstar1 (autOn G (gomiV G))), CFSG.IsComponent K := by
  set Y := autOn G (gomiV G)
  have hW : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (gomiV_moduleSetting G).1.2 w w.2)
  have hPstar : (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet Y).Nonempty := by
    obtain ⟨A, hA⟩ := pset_nonempty h
    obtain ⟨B, hB, -⟩ := exists_mem_pstarSet_le (Y := Y) hA
    exact ⟨B, hB⟩
  have hPstar1 : (gomiPstar1Set Y).Nonempty := by
    obtain ⟨B, hB⟩ := hPstar
    refine ⟨B, ?_⟩
    simpa [gomiPstar1Set, h0] using hB
  have hO2 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O2Trivial
      (gomiGstar1 Y) :=
    o2Trivial_of_normal (o2Trivial_autOn h) (gomiGstar1_le Y) (gomiGstar1_subgroupOf_normal Y)
  have hLayer : CFSG.layer ↥(gomiGstar1 Y) ≠ ⊥ :=
    (h33 ↥(gomiV G) hW Y hPstar1 hO2).1
  exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2.exists_isComponent_of_layer_ne_bot hLayer

private theorem component_basic_g45e
    (h : GomiThm45Counterexample c G S)
    {K : Subgroup ↥(gomiGstar1 (autOn G (gomiV G)))} (hKcomp : CFSG.IsComponent K) :
    ∃ Lb : Subgroup (MulAut ↥(gomiV G)),
      Lb ≤ gomiGstar1 (autOn G (gomiV G)) ∧
        CFSG.IsComponent (Lb.subgroupOf (gomiGstar1 (autOn G (gomiV G)))) ∧
        Lb ≤ autOn G (gomiV G) ∧
        CFSG.IsComponent (Lb.subgroupOf (autOn G (gomiV G))) ∧
        CFSG.pCore 2 ↥Lb = ⊥ ∧ Even (Nat.card ↥Lb) := by
  set Lb : Subgroup (MulAut ↥(gomiV G)) :=
    K.map (gomiGstar1 (autOn G (gomiV G))).subtype with hLb
  have hLbX : Lb ≤ gomiGstar1 (autOn G (gomiV G)) := by
    rw [hLb]
    exact Subgroup.map_subtype_le K
  have hsub : Lb.subgroupOf (gomiGstar1 (autOn G (gomiV G))) = K := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subgroupOf_eq_of_le hLbX, hLb]
  have hLbCompX : CFSG.IsComponent
      (Lb.subgroupOf (gomiGstar1 (autOn G (gomiV G)))) := by
    rw [hsub]
    exact hKcomp
  have hLbY : Lb ≤ autOn G (gomiV G) :=
    hLbX.trans (gomiGstar1_le (autOn G (gomiV G)))
  have hXnormal : ((gomiGstar1 (autOn G (gomiV G))).subgroupOf (autOn G (gomiV G))).Normal :=
    gomiGstar1_subgroupOf_normal _
  have hLbCompY : CFSG.IsComponent (Lb.subgroupOf (autOn G (gomiV G))) :=
    isComponent_subgroupOf_of_normal hLbX (gomiGstar1_le (autOn G (gomiV G)))
      hXnormal hLbCompX
  have hLq : CFSG.IsQuasisimple ↥Lb :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hLbY)).mp hLbCompY.1
  have hOpen : CFSG.Open.IsQuasisimple ↥Lb :=
    (CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native
      (G := ↥Lb)).1 hLq
  have hEven : Even (Nat.card ↥Lb) :=
    CFSG.ComponentClassification.AschbacherKnownGroup.Lemma38.even_card_of_isQuasisimple hOpen
  have hpc : CFSG.pCore 2 ↥Lb = ⊥ :=
    pCore_eq_bot_of_isComponent_g45e (o2Trivial_autOn h) hLbY hLbCompY
  exact ⟨Lb, hLbX, hLbCompX, hLbY, hLbCompY, hpc, hEven⟩

omit [Finite Ω] in
private theorem component_commutator_ne_bot_g45e
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hLbX : Lb ≤ gomiGstar1 (autOn G (gomiV G)))
    (hLbY : Lb ≤ autOn G (gomiV G))
    (hcomp : CFSG.IsComponent (Lb.subgroupOf (autOn G (gomiV G)))) :
    ⁅Lb, ffJ (autOn G (gomiV G))⁆ ≠ ⊥ := by
  set Y := autOn G (gomiV G)
  have hLq : CFSG.IsQuasisimple ↥Lb :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hLbY)).mp hcomp.1
  have hLbJ : Lb ≤ ffJ Y :=
    hLbX.trans ((gomiGstar1_le_sSup_pstarSet Y).trans (sSup_pstarSet_le_ffJ Y))
  have hLb_ne_bot : Lb ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot Lb).mp (CFSG.LocalCores.isQuasisimple_nontrivial hLq)
  have hLL : ⁅Lb, Lb⁆ = Lb := by
    have : Group.IsPerfect ↥Lb := hLq.1
    exact Subgroup.commutator_eq_self
  intro hbot
  have hle : Lb ≤ ⊥ := by
    rw [← hLL]
    exact (Subgroup.commutator_mono le_rfl hLbJ).trans (le_of_eq hbot)
  exact hLb_ne_bot (le_bot_iff.mp hle)

private theorem exists_isGomiStepE_of_pstar0_eq_empty_g45e
    (h : GomiThm45Counterexample c G S) (h33 : GomiFact33) (h44 : GomiLemma44)
    (h0 : gomiPstar0Set (autOn G (gomiV G)) = ∅) :
    ∃ Lb : Subgroup (MulAut ↥(gomiV G)),
      IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb := by
  set Y := autOn G (gomiV G)
  set Sb := autOn S (gomiV G)
  obtain ⟨K, hKcomp⟩ := exists_component_gomiGstar1_g45e h h33 h0
  obtain ⟨Lb, hLbX, hLbCompX, hLbY, hLbCompY, hpc, hEven⟩ := component_basic_g45e h hKcomp
  have hJ := component_commutator_ne_bot_g45e hLbX hLbY hLbCompY
  have hW : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (gomiV_moduleSetting G).1.2 w w.2)
  have hYsec : CFSG.SignalizerFunctorTheorem.IsSectionOf ↥Y ↥G := by
    obtain ⟨-, φ, hφ, -⟩ :=
      gomi_moduleSetting (gomiV_moduleSetting G).1 (gomiV_moduleSetting G).2
    refine ⟨⊤, φ.comp Subgroup.topEquiv.toMonoidHom, ?_⟩
    intro y
    obtain ⟨g, hg⟩ := hφ y
    exact ⟨Subgroup.topEquiv.symm g, by simp [hg]⟩
  have htype : GomiHyp43Type ↥Lb :=
    h44 G h.hyp43 ↥(gomiV G) hW Y hYsec Lb hLbY hLbCompY hpc hJ
  refine ⟨Lb, hLbY, Or.inr ⟨h0, hLbX, hLbCompX⟩, ?_, ?_, Or.inr htype⟩
  · intro y hy hne a ha b hb
    have hyN : y ∈ Subgroup.normalizer (gomiGstar1 Y : Set (MulAut ↥(gomiV G))) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (gomiGstar1_le Y)).mp
        (gomiGstar1_subgroupOf_normal Y) hy
    have hLyX : Lb.map (MulAut.conj y).toMonoidHom ≤ gomiGstar1 Y := by
      have hXy : (gomiGstar1 Y).map (MulAut.conj y).toMonoidHom = gomiGstar1 Y :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN
      exact (Subgroup.map_mono hLbX).trans (le_of_eq hXy)
    have hLyComp : CFSG.IsComponent
        ((Lb.map (MulAut.conj y).toMonoidHom).subgroupOf (gomiGstar1 Y)) :=
      isComponent_map_conj_subgroupOf hyN hLbX hLbCompX
    exact commute_of_isComponent_subgroupOf hLbX hLyX hLbCompX hLyComp (Ne.symm hne) a ha b hb
  · exact iSup_conj_sup_eq_of_even_g45e h hLbY hEven

theorem exists_isGomiStepE (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    (h33 : GomiFact33) (h44 : GomiLemma44) :
    ∃ Lb : Subgroup (MulAut ↥(gomiV G)),
      IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb := by
  by_cases h0 : (gomiPstar0Set (autOn G (gomiV G))).Nonempty
  · exact exists_isGomiStepE_of_pstar0_g45e h h31 h0
  · have h0' : gomiPstar0Set (autOn G (gomiV G)) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun A hA => h0 ⟨A, hA⟩
    exact exists_isGomiStepE_of_pstar0_eq_empty_g45e h h33 h44 h0'

private theorem isPIsolatedOver_top_bot_g45f1 {V : Type} [Group V] [Finite (MulAut V)]
    {Y : Subgroup (MulAut V)} (hiso : IsPIsolatedOver 2 Y ⊥) :
    IsPIsolatedOver 2 (⊤ : Subgroup ↥Y) ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (isPIsolatedOver_subgroupOf_iff (p := 2) (H := (⊥ : Subgroup (MulAut V)))
    (K := Y) (K' := Y) bot_le le_rfl).mpr hiso
  simpa only [Subgroup.subgroupOf_self, Subgroup.bot_subgroupOf] using h

private theorem commutator_eq_bot_of_conj_g45f1 {V : Type} [Group V]
    {Y Lb : Subgroup (MulAut V)} (hLY : Lb ≤ Y)
    (hcomm : ∀ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom ≠ Lb →
      ∀ a ∈ Lb, ∀ b ∈ Lb.map (MulAut.conj y).toMonoidHom, a * b = b * a) :
    ∀ g : ↥Y, (Lb.subgroupOf Y).map (MulAut.conj g).toMonoidHom ≠ Lb.subgroupOf Y →
      ⁅(Lb.subgroupOf Y),
        (Lb.subgroupOf Y).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  intro g hg
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
  intro a ha
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro b hb
  have hg' : Lb.map (MulAut.conj (g : MulAut V)).toMonoidHom ≠ Lb := by
    intro heq
    apply hg
    apply Subgroup.map_injective Y.subtype_injective
    rw [CFSG.map_subgroupOf_map_conj_eq hLY g, heq,
      Subgroup.map_subgroupOf_eq_of_le hLY]
  have hb' : (b : MulAut V) ∈ Lb.map (MulAut.conj (g : MulAut V)).toMonoidHom := by
    rw [← CFSG.map_subgroupOf_map_conj_eq hLY g]
    exact Subgroup.mem_map_of_mem Y.subtype hb
  exact (Subtype.ext
    (hcomm (g : MulAut V) g.2 hg' (a : MulAut V) ha (b : MulAut V) hb')).symm

private theorem isPGroup_quotient_normalClosure_g45f1 {V : Type} [Group V]
    {Y Sb Lb : Subgroup (MulAut V)} (hLY : Lb ≤ Y) (hSb_le : Sb ≤ Y)
    (hSb2 : IsPGroup 2 Sb)
    (hsup : (⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom) ⊔ Sb = Y) :
    IsPGroup 2 (↥Y ⧸ Subgroup.normalClosure (Lb.subgroupOf Y : Set ↥Y)) := by
  let NC : Subgroup ↥Y := Subgroup.normalClosure (Lb.subgroupOf Y : Set ↥Y)
  have hA_le : (⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom) ≤ Y := by
    refine iSup_le fun y => iSup_le fun hy => ?_
    rw [← CFSG.map_subgroupOf_map_conj_eq hLY (⟨y, hy⟩ : ↥Y)]
    exact Subgroup.map_subtype_le _
  have hconj_le : ∀ g : ↥Y, (Lb.subgroupOf Y).map (MulAut.conj g).toMonoidHom ≤ NC := by
    intro g
    rintro x ⟨l, hl, rfl⟩
    change g * l * g⁻¹ ∈ NC
    exact (Subgroup.normalClosure_normal (s := (Lb.subgroupOf Y : Set ↥Y))).conj_mem l
      (Subgroup.subset_normalClosure hl) g
  have hsup_le : (⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom) ≤ NC.map Y.subtype := by
    refine iSup_le fun y => iSup_le fun hy => ?_
    rw [← CFSG.map_subgroupOf_map_conj_eq hLY (⟨y, hy⟩ : ↥Y)]
    exact Subgroup.map_mono (hconj_le ⟨y, hy⟩)
  have hle_sub : (⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom).subgroupOf Y ≤ NC :=
    (CFSG.subgroupOf_le_iff_le_map_subtype hA_le).mpr hsup_le
  have hsupY : (⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom).subgroupOf Y ⊔
      Sb.subgroupOf Y = ⊤ := by
    have h := congrArg (fun K : Subgroup (MulAut V) => K.subgroupOf Y) hsup
    rwa [Subgroup.subgroupOf_sup hA_le hSb_le, Subgroup.subgroupOf_self] at h
  have htop : NC ⊔ Sb.subgroupOf Y = ⊤ :=
    le_antisymm le_top (hsupY ▸ sup_le_sup_right hle_sub _)
  have hSb2sub : IsPGroup 2 ↥(Sb.subgroupOf Y) :=
    hSb2.of_equiv (Subgroup.subgroupOfEquivOfLe hSb_le).symm
  have hNCmap : NC.map (QuotientGroup.mk' NC) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hmap_top : (Sb.subgroupOf Y).map (QuotientGroup.mk' NC) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' NC)) htop
    rw [Subgroup.map_sup, hNCmap, bot_sup_eq, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective NC)] at h
    exact h
  have hf : Function.Surjective ((QuotientGroup.mk' NC).comp (Sb.subgroupOf Y).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective NC q
    have hx : (QuotientGroup.mk' NC) x ∈
        (Sb.subgroupOf Y).map (QuotientGroup.mk' NC) := by
      rw [hmap_top]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨s, hs⟩, by simpa using hsm⟩
  exact IsPGroup.of_surjective hSb2sub _ hf

private theorem eq_bot_of_normal_isPGroup_two_g45f1 {V : Type} [Group V]
    {Y : Subgroup (MulAut V)}
    (hO : ∀ P : Subgroup (MulAut V), P ≤ Y → (P.subgroupOf Y).Normal →
      IsPGroup 2 P → P = ⊥)
    {K : Subgroup ↥Y} (hKN : K.Normal) (hK2 : IsPGroup 2 K) : K = ⊥ := by
  let P : Subgroup (MulAut V) := K.map Y.subtype
  have hPle : P ≤ Y := Subgroup.map_subtype_le _
  have hPK : P.subgroupOf Y = K := by
    ext x
    constructor
    · rintro ⟨k, hk, hkx⟩
      have hkx' : k = x := Subtype.ext hkx
      rwa [hkx'] at hk
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem Y.subtype hx)
  have hPN : (P.subgroupOf Y).Normal := by
    rw [hPK]
    exact hKN
  have hPbot : P = ⊥ := hO P hPle hPN (hK2.map Y.subtype)
  rw [← hPK, hPbot, Subgroup.bot_subgroupOf]

private theorem exists_not_commute_statedSL_two_g45f1 (K : Type) [Field K] :
    ∃ a b : ↥(StatedSL 2 K), a * b ≠ b * a := by
  let A : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let B : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hAB : A * B ≠ B * A := by
    intro h
    have hentry := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
      (M : Matrix (Fin 2) (Fin 2) K) 0 0) h
    have h1 : ((A * B : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 0 0 = 1 + 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      simp [A, B]
    have h2 : ((B * A : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      simp [A, B]
    rw [h1, h2] at hentry
    have h10 : (1 : K) = 0 := by
      refine add_left_cancel (a := (1 : K)) (b := 1) (c := 0) ?_
      rw [add_zero]
      exact hentry
    exact one_ne_zero h10
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  refine ⟨e A, e B, ?_⟩
  intro h
  apply hAB
  have h' : e (A * B) = e (B * A) := by simpa only [map_mul] using h
  exact e.injective h'

private theorem card_eq_six_and_exists_not_commute_of_isSLn_two_one_g45f1
    {X : Type} [Group X] (h : IsSLn X 2 1) :
    Nat.card X = 6 ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨f⟩⟩ := h
  let : Field K := hKf
  have : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨a, b, hab⟩ := exists_not_commute_statedSL_two_g45f1 K
  refine ⟨?_, ⟨f.symm a, f.symm b, ?_⟩⟩
  · rw [Nat.card_congr f.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two K, hK2]
    norm_num
  · intro hcomm
    apply hab
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg f hcomm

private theorem isQuasisimple_and_odd_center_of_gomiHyp43Type_g45f1
    {K : Type} [Group K] [Finite K] (h : GomiHyp43Type K) :
    CFSG.IsQuasisimple K ∧ Odd (Nat.card (Subgroup.center K)) := by
  rcases h with hChev | ⟨n, hn7, ⟨e⟩⟩
  · exact ⟨hChev.1.1, CFSG.Quasithin.A36A.odd_card_center hChev.1.2.1⟩
  · have hn5 : 5 ≤ n := by omega
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn5)
    have hnc : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have hcomm : IsMulCommutative (alternatingGroup (Fin n)) :=
        ⟨⟨fun a b => hcon a b⟩⟩
      have h3 := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin n)).1 hcomm
      simp at h3
      omega
    obtain ⟨hqAlt, hZalt⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc
    have hqK : CFSG.IsQuasisimple K :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqAlt
    have hZK : Subgroup.center K = ⊥ := by
      have hmap : Subgroup.map (e : K →* alternatingGroup (Fin n))
          (Subgroup.center K) = ⊥ := by
        rw [Subgroup.map_center_eq e, hZalt]
      exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center K) e.injective).mp hmap
    refine ⟨hqK, ?_⟩
    rw [hZK, Subgroup.card_bot]
    exact odd_one

private theorem eq_of_isSLn_two_one_case_g45f1 {V : Type} [Group V] [Finite (MulAut V)]
    {Y Lb : Subgroup (MulAut V)} (hB : GomiBender)
    (hX : IsPIsolatedOver 2 (⊤ : Subgroup ↥Y) ⊥)
    (hcomm : ∀ g : ↥Y, (Lb.subgroupOf Y).map (MulAut.conj g).toMonoidHom ≠ Lb.subgroupOf Y →
      ⁅(Lb.subgroupOf Y),
        (Lb.subgroupOf Y).map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hq : IsPGroup 2 (↥Y ⧸ Subgroup.normalClosure (Lb.subgroupOf Y : Set ↥Y)))
    (hO : ∀ K : Subgroup ↥Y, K.Normal → IsPGroup 2 K → K = ⊥) (hLY : Lb ≤ Y)
    (hSL : IsSLn ↥Lb 2 1) : Lb = Y := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨f⟩⟩ := hSL
  let : Field K := hKf
  have : Finite K := hKfin
  have hSLL : IsSLn ↥(Lb.subgroupOf Y) 2 1 :=
    ⟨K, hKf, hKfin, hKcard, ⟨(Subgroup.subgroupOfEquivOfLe hLY).trans f⟩⟩
  obtain ⟨hcard, hnc⟩ := card_eq_six_and_exists_not_commute_of_isSLn_two_one_g45f1 hSLL
  obtain ⟨hLtop, -⟩ := eq_top_of_isPIsolatedOver hB hX hcomm hq hO (Or.inl ⟨hcard, hnc⟩)
  exact le_antisymm hLY (Subgroup.subgroupOf_eq_top.mp hLtop)

private theorem exists_isSLn_of_gomiHyp43Type_case_g45f1 {V : Type} [Group V]
    [Finite (MulAut V)] {Y Lb : Subgroup (MulAut V)} (hB : GomiBender)
    (hBSL : GomiBenderSL2) (hX : IsPIsolatedOver 2 (⊤ : Subgroup ↥Y) ⊥)
    (hcomm : ∀ g : ↥Y, (Lb.subgroupOf Y).map (MulAut.conj g).toMonoidHom ≠ Lb.subgroupOf Y →
      ⁅(Lb.subgroupOf Y),
        (Lb.subgroupOf Y).map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hq : IsPGroup 2 (↥Y ⧸ Subgroup.normalClosure (Lb.subgroupOf Y : Set ↥Y)))
    (hO : ∀ K : Subgroup ↥Y, K.Normal → IsPGroup 2 K → K = ⊥) (hLY : Lb ≤ Y)
    (hType : GomiHyp43Type ↥Lb) :
    Lb = Y ∧ ∃ m : ℕ, 1 ≤ m ∧ IsSLn ↥Lb 2 m := by
  have htype : CFSG.IsQuasisimple ↥(Lb.subgroupOf Y) ∧
      Odd (Nat.card (Subgroup.center ↥(Lb.subgroupOf Y))) := by
    obtain ⟨hqLb, hZb⟩ := isQuasisimple_and_odd_center_of_gomiHyp43Type_g45f1 hType
    let e : ↥(Lb.subgroupOf Y) ≃* ↥Lb := Subgroup.subgroupOfEquivOfLe hLY
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqLb, ?_⟩
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hZb
  obtain ⟨hLtop, hBend⟩ :=
    eq_top_of_isPIsolatedOver hB hX hcomm hq hO (Or.inr htype)
  have hLbY : Lb = Y := le_antisymm hLY (Subgroup.subgroupOf_eq_top.mp hLtop)
  have hBendLb : CFSG.Open.fusionIsBenderGroup (↥Lb ⧸ Subgroup.center ↥Lb) := by
    rw [hLbY]
    exact hBend htype.1
  obtain ⟨m, hm, hmSL⟩ := hBSL ↥Lb hType hBendLb
  exact ⟨hLbY, m, by omega, hmSL⟩

theorem eq_of_isPIsolatedOver (h : GomiThm45Counterexample c G S) (hB : GomiBender)
    (hBSL : GomiBenderSL2) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hiso : IsPIsolatedOver 2 (autOn G (gomiV G)) ⊥) :
    Lb = autOn G (gomiV G) ∧ ∃ m : ℕ, 1 ≤ m ∧ IsSLn ↥Lb 2 m := by
  let Y : Subgroup (MulAut ↥(gomiV G)) := autOn G (gomiV G)
  let Sb : Subgroup (MulAut ↥(gomiV G)) := autOn S (gomiV G)
  have hLY : Lb ≤ Y := hL.le
  have hSb_le : Sb ≤ Y := h.isSylowIn_autOn.1
  have hSb2 : IsPGroup 2 Sb := h.isSylowIn_autOn.2.1
  have hX : IsPIsolatedOver 2 (⊤ : Subgroup ↥Y) ⊥ :=
    isPIsolatedOver_top_bot_g45f1 hiso
  have hcomm := commutator_eq_bot_of_conj_g45f1 hLY hL.commute
  have hq : IsPGroup 2 (↥Y ⧸ Subgroup.normalClosure ((Lb.subgroupOf Y) : Set ↥Y)) :=
    isPGroup_quotient_normalClosure_g45f1 hLY hSb_le hSb2 hL.sup_eq
  have hO : ∀ K : Subgroup ↥Y, K.Normal → IsPGroup 2 K → K = ⊥ := fun K hKN hK2 =>
    eq_bot_of_normal_isPGroup_two_g45f1 (o2Trivial_autOn h) hKN hK2
  rcases hL.type with hSL | hType
  · have hLbY := eq_of_isSLn_two_one_case_g45f1 hB hX hcomm hq hO hLY hSL
    exact ⟨hLbY, 1, le_rfl, hSL⟩
  · exact exists_isSLn_of_gomiHyp43Type_case_g45f1 hB hBSL hX hcomm hq hO hLY hType

private theorem exists_isSLn_of_isGomiL2_g45f2 {K : Type} [Group K] [Finite K]
    (hK : IsGomiChevTwo K) (h : IsGomiL2 (K ⧸ Subgroup.center K)) :
    ∃ m : ℕ, 2 ≤ m ∧ IsSLn K 2 m := by
  rcases nonempty_mulEquiv_of_isGomiL2 hK.1 hK.2.1 h with ⟨⟨e5⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · obtain ⟨e45⟩ := CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5
    exact ⟨2, le_rfl, GaloisField 2 2, inferInstance, inferInstance,
      GaloisField.card 2 2 (by norm_num), ⟨e5.trans (e45.symm.trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 _))⟩⟩
  · exact ⟨m, by omega, GaloisField 2 m, inferInstance, inferInstance,
      GaloisField.card 2 m (by omega),
      ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 _)⟩⟩

private theorem gomiHyp21_subgroupOf_g45f2a {V : Type} [Group V]
    {Y Sb Lb : Subgroup (MulAut V)}
    (hLY : Lb ≤ Y) (hSb_le : Sb ≤ Y) (hSb2 : IsPGroup 2 Sb)
    (hcomm : ∀ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom ≠ Lb →
      ∀ a ∈ Lb, ∀ b ∈ Lb.map (MulAut.conj y).toMonoidHom, a * b = b * a)
    (hsup : (⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom) ⊔ Sb = Y)
    (hq : CFSG.IsQuasisimple ↥Lb) :
    GomiHyp21 (Lb.subgroupOf Y) where
  commute := commutator_eq_bot_of_conj_g45f1 hLY hcomm
  isPGroup_quotient := isPGroup_quotient_normalClosure_g45f1 hLY hSb_le hSb2 hsup
  quasisimple := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hLY).symm hq

private theorem exists_sylow_not_parabolicSwap_g45f2a {V : Type} [Group V]
    {Y Sb Lb : Subgroup (MulAut V)}
    (hSbY : Sb ≤ Y) (hSb2 : IsPGroup 2 Sb)
    (hSbindex : ¬ 2 ∣ (Sb.subgroupOf Y).index)
    (hLY : Lb ≤ Y) (hNoSwap : ¬ IsGomiParabolicSwap Sb Lb) :
    ∃ S : Sylow 2 ↥Y,
      ¬ IsGomiParabolicSwap (S : Subgroup ↥Y) (Lb.subgroupOf Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSb2sub : IsPGroup 2 (Sb.subgroupOf Y) :=
    hSb2.of_equiv (Subgroup.subgroupOfEquivOfLe hSbY).symm
  let S : Sylow 2 ↥Y := hSb2sub.toSylow hSbindex
  refine ⟨S, ?_⟩
  rw [IsPGroup.toSylow_coe hSb2sub hSbindex]
  intro hswap
  have hm := IsGomiParabolicSwap.map_subtype (H := Y) hswap
  rw [Subgroup.map_subgroupOf_eq_of_le hSbY, Subgroup.map_subgroupOf_eq_of_le hLY] at hm
  exact hNoSwap hm

private theorem exists_oddIndex_of_isGomiChevTwo_g45f2a {V : Type} [CommGroup V]
    [Finite (MulAut V)] {Y Sb Lb : Subgroup (MulAut V)} (h22 : GomiFact22)
    (hLY : Lb ≤ Y) (hSbY : Sb ≤ Y) (hSb2 : IsPGroup 2 Sb)
    (hSbindex : ¬ 2 ∣ (Sb.subgroupOf Y).index)
    (hHyp : GomiHyp21 (Lb.subgroupOf Y)) (hChev : IsGomiChevTwo ↥Lb)
    (hU3 : ¬ IsGomiU3 (↥Lb ⧸ Subgroup.center ↥Lb))
    (hSz : ¬ IsGomiSz (↥Lb ⧸ Subgroup.center ↥Lb))
    (hF : ¬ IsGomiStepF Sb Lb)
    (H : Subgroup ↥Y) (hH : H ≠ ⊥) (hH2 : IsPGroup 2 H)
    (hHiso : IsPIsolatedOver 2 (Subgroup.normalizer (H : Set ↥Y)) H) :
    ∃ N : Subgroup ↥Y, H ≤ N ∧ N ≤ Subgroup.normalizer (H : Set ↥Y) ∧
      (N.subgroupOf (Subgroup.normalizer (H : Set ↥Y))).IsSubnormal ∧
      2 ∣ H.relIndex N ∧ ∃ M : Subgroup ↥Y, M ≠ ⊤ ∧ Odd M.index ∧ N ≤ M := by
  let eL : ↥(Lb.subgroupOf Y) ≃* ↥Lb := Subgroup.subgroupOfEquivOfLe hLY
  let qe : (↥(Lb.subgroupOf Y) ⧸ Subgroup.center ↥(Lb.subgroupOf Y)) ≃*
      (↥Lb ⧸ Subgroup.center ↥Lb) := QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)
  have hnot : ¬ (IsGomiL2 (↥(Lb.subgroupOf Y) ⧸ Subgroup.center ↥(Lb.subgroupOf Y)) ∨
      IsGomiU3 (↥(Lb.subgroupOf Y) ⧸ Subgroup.center ↥(Lb.subgroupOf Y)) ∨
      IsGomiSz (↥(Lb.subgroupOf Y) ⧸ Subgroup.center ↥(Lb.subgroupOf Y))) := by
    rintro (h2 | h3 | hsz)
    · obtain ⟨m, hm, hmSL⟩ := exists_isSLn_of_isGomiL2_g45f2 hChev (h2.of_mulEquiv qe)
      exact hF (Or.inl ⟨m, by omega, hmSL⟩)
    · exact hU3 (h3.of_mulEquiv qe)
    · exact hSz (hsz.of_mulEquiv qe)
  have hswap : (IsGomiL3 (↥(Lb.subgroupOf Y) ⧸ Subgroup.center ↥(Lb.subgroupOf Y)) ∨
      IsGomiSp4 (↥(Lb.subgroupOf Y) ⧸ Subgroup.center ↥(Lb.subgroupOf Y))) →
      ∃ S : Sylow 2 ↥Y,
        ¬ IsGomiParabolicSwap (S : Subgroup ↥Y) (Lb.subgroupOf Y) := by
    intro hLS
    have hLSb : IsGomiL3 (↥Lb ⧸ Subgroup.center ↥Lb) ∨
        IsGomiSp4 (↥Lb ⧸ Subgroup.center ↥Lb) := by
      rcases hLS with h | h
      · exact Or.inl (h.of_mulEquiv qe)
      · exact Or.inr (h.of_mulEquiv qe)
    have hNoSwap : ¬ IsGomiParabolicSwap Sb Lb := fun hs =>
      hF (Or.inr (Or.inl ⟨hChev, hLSb, hs⟩))
    exact exists_sylow_not_parabolicSwap_g45f2a hSbY hSb2 hSbindex hLY hNoSwap
  have hChevL : IsGomiChevTwo ↥(Lb.subgroupOf Y) :=
    IsGomiChevTwo.of_mulEquiv eL.symm hChev
  obtain ⟨M, hMne, hModd, ⟨K, hHK, hKN, hKsub, hKind, hKM⟩, -⟩ :=
    h22 ↥Y (Lb.subgroupOf Y) hHyp hChevL hnot hswap H hH hH2 hHiso
  exact ⟨K, hHK, hKN, hKsub, hKind, M, hMne, hModd, hKM⟩

private theorem exists_oddIndex_of_isAlt_g45f2a {V : Type} [Group V]
    [Finite (MulAut V)] {Y Lb : Subgroup (MulAut V)} (h23 : GomiFact23)
    (hLY : Lb ≤ Y) (hHyp : GomiHyp21 (Lb.subgroupOf Y))
    {n : ℕ} (hn7 : 7 ≤ n) (e : ↥Lb ≃* alternatingGroup (Fin n))
    (hneq : ∀ m : ℕ, n ≠ 2 ^ m + 1)
    (H : Subgroup ↥Y) (hH : H ≠ ⊥) (hH2 : IsPGroup 2 H)
    (hHiso : IsPIsolatedOver 2 (Subgroup.normalizer (H : Set ↥Y)) H) :
    ∃ N : Subgroup ↥Y, H ≤ N ∧ N ≤ Subgroup.normalizer (H : Set ↥Y) ∧
      (N.subgroupOf (Subgroup.normalizer (H : Set ↥Y))).IsSubnormal ∧
      2 ∣ H.relIndex N ∧ ∃ M : Subgroup ↥Y, M ≠ ⊤ ∧ Odd M.index ∧ N ≤ M := by
  have eL : ↥(Lb.subgroupOf Y) ≃* alternatingGroup (Fin n) :=
    (Subgroup.subgroupOfEquivOfLe hLY).trans e
  obtain ⟨M, hMne, hModd, ⟨K, hHK, hKN, hKsub, hKind, hKM⟩⟩ :=
    (h23 ↥Y (Lb.subgroupOf Y) n hHyp hn7 ⟨eL⟩ H hH hH2 hHiso).1 hneq
  exact ⟨K, hHK, hKN, hKsub, hKind, M, hMne, hModd, hKM⟩

private theorem controlsSylowIntersections_of_not_isGomiStepF_g45f2
    (h : GomiThm45Counterexample c G S) (h22 : GomiFact22) (h23 : GomiFact23)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hType : GomiHyp43Type ↥Lb)
    (hF : ¬ IsGomiStepF (autOn S (gomiV G)) Lb) :
    ControlsSylowIntersections 2
      {M : Subgroup ↥(autOn G (gomiV G)) | M ≠ ⊤ ∧ Odd M.index} ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLY : Lb ≤ autOn G (gomiV G) := hL.le
  have hSbY : autOn S (gomiV G) ≤ autOn G (gomiV G) := h.isSylowIn_autOn.1
  have hSb2 : IsPGroup 2 (autOn S (gomiV G)) := h.isSylowIn_autOn.2.1
  have hSbindex : ¬ 2 ∣ ((autOn S (gomiV G)).subgroupOf (autOn G (gomiV G))).index := by
    simpa only [Subgroup.relIndex] using h.isSylowIn_autOn.2.2
  have hqLb : CFSG.IsQuasisimple ↥Lb :=
    (isQuasisimple_and_odd_center_of_gomiHyp43Type_g45f1 hType).1
  have hHyp : GomiHyp21 (Lb.subgroupOf (autOn G (gomiV G))) :=
    gomiHyp21_subgroupOf_g45f2a hLY hSbY hSb2 hL.commute hL.sup_eq hqLb
  have hmain : ∀ H : Subgroup ↥(autOn G (gomiV G)), H ≠ ⊥ → IsPGroup 2 H →
      IsPIsolatedOver 2
        (Subgroup.normalizer (H : Set ↥(autOn G (gomiV G)))) H →
      ∃ N : Subgroup ↥(autOn G (gomiV G)),
        H ≤ N ∧ N ≤ Subgroup.normalizer (H : Set ↥(autOn G (gomiV G))) ∧
        (N.subgroupOf (Subgroup.normalizer (H : Set ↥(autOn G (gomiV G))))).IsSubnormal ∧
        2 ∣ H.relIndex N ∧
        ∃ M : Subgroup ↥(autOn G (gomiV G)), M ≠ ⊤ ∧ Odd M.index ∧ N ≤ M := by
    intro H hH hH2 hHiso
    rcases hType with hChev | ⟨n, hn7, ⟨e⟩⟩
    · obtain ⟨hChev, hU3, hSz⟩ := hChev
      exact exists_oddIndex_of_isGomiChevTwo_g45f2a
        (Y := autOn G (gomiV G)) (Sb := autOn S (gomiV G)) (Lb := Lb)
        h22 hLY hSbY hSb2 hSbindex hHyp hChev hU3 hSz hF H hH hH2 hHiso
    · have hneq : ∀ m : ℕ, n ≠ 2 ^ m + 1 := by
        intro m hm
        have h2m : 6 ≤ 2 ^ m := by omega
        have hm3 : 3 ≤ m := by
          by_contra hlt
          have hm2 : m ≤ 2 := by omega
          interval_cases m <;> norm_num at h2m
        exact hF (Or.inr (Or.inr ⟨m, hm3, ⟨hm ▸ e⟩⟩))
      exact exists_oddIndex_of_isAlt_g45f2a
        (Y := autOn G (gomiV G)) (Lb := Lb)
        h23 hLY hHyp hn7 e hneq H hH hH2 hHiso
  refine controlsSylowIntersections_of_isPIsolatedOver fun H hH hH2 hHiso => ?_
  obtain ⟨N, hHN, hNnorm, hNsub, hNidx, M, hMne, hModd, hNM⟩ := hmain H hH hH2 hHiso
  exact ⟨N, hHN, hNnorm, hNsub, hNidx, M, ⟨hMne, hModd⟩, hNM⟩

omit [Finite Ω] in
private theorem relIndex_map_comap_g45f2b
    (φ : ↥G →* ↥(autOn G (gomiV G))) (hφ : Function.Surjective φ)
    {M : Subgroup ↥(autOn G (gomiV G))} (hM : M ≠ ⊤) :
    ((M.comap φ).map G.subtype).relIndex G = M.index ∧
      ((M.comap φ).map G.subtype) ≠ G := by
  have hri := Subgroup.relIndex_map_map_of_injective (f := G.subtype) (M.comap φ) ⊤
    G.subtype_injective
  rw [Subgroup.map_top, Subgroup.subtype_range, Subgroup.relIndex_top_right] at hri
  have hrel : ((M.comap φ).map G.subtype).relIndex G = M.index := by
    rw [hri, Subgroup.index_comap_of_surjective M hφ]
  refine ⟨hrel, ?_⟩
  intro heq
  apply hM
  have hone : ((M.comap φ).map G.subtype).relIndex G = 1 := by
    rw [heq, Subgroup.relIndex_self]
  rw [hrel] at hone
  exact Subgroup.index_eq_one.mp hone

private theorem isNormalSetIn_oddIndex_g45f2b {X : Type*} [Group X] :
    IsNormalSetIn {M : Subgroup X | M ≠ ⊤ ∧ Odd M.index} ⊤ := by
  constructor
  · intro M _
    exact le_top
  · intro M hM g _
    refine ⟨?_, ?_⟩
    · intro htop
      apply hM.1
      have h1 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) htop
      rw [CFSG.GroupTheory.map_conj_map_conj_inv g M,
        Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective] at h1
      exact h1
    · exact (Subgroup.index_map_equiv (H := M) (MulAut.conj g)) ▸ hM.2

private theorem isRegular_of_subgroup_of_odd_relIndex_g45f2b
    (h : GomiThm45Counterexample c G S) {D : Subgroup Ω}
    (hDG : D ≤ G) (hodd : ¬ 2 ∣ D.relIndex G) (hDne : D ≠ G) :
    c.selection.IsRegular D := by
  have hDlt : D < G := lt_of_le_of_ne hDG hDne
  obtain ⟨T, hTD⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 D
  have hTG : CFSG.ABGLocalTools.IsSylowOf 2 T G := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hTD ⊢
    obtain ⟨hTDle, hT2, hTidx⟩ := hTD
    refine ⟨hTDle.trans hDG, hT2, ?_⟩
    intro h2
    have hmul := Subgroup.relIndex_mul_relIndex T D G hTDle hDG
    rw [← hmul] at h2
    exact Nat.Prime.not_dvd_mul Nat.prime_two hTidx hodd h2
  have hSG : CFSG.ABGLocalTools.IsSylowOf 2 S G :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp h.isSylowTwoOf
  obtain ⟨k, hkG, hconj⟩ := hTG.exists_mem_conj hSG
  have hSmap : S = T.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [hconj x]
    constructor
    · intro hx
      refine Subgroup.mem_map.mpr ⟨k⁻¹ * x * k, hx, ?_⟩
      simp [MulAut.conj_apply]
      group
    · rintro ⟨t, ht, rfl⟩
      have h : k⁻¹ * (k * t * k⁻¹) * k = t := by group
      simpa [MulAut.conj_apply, h] using ht
  have hSDk : S ≤ D.map (MulAut.conj k).toMonoidHom :=
    hSmap.le.trans (Subgroup.map_mono hTD.le)
  have hGmap : G.map (MulAut.conj k).toMonoidHom = G :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkG)
  have hDklt : D.map (MulAut.conj k).toMonoidHom < G := by
    have hlt : D.map (MulAut.conj k).toMonoidHom < G.map (MulAut.conj k).toMonoidHom :=
      (Subgroup.map_lt_map_iff_of_injective (MulAut.conj k).injective).mpr hDlt
    rwa [hGmap] at hlt
  have hJ : thompsonJ S ⊔ pCoreOf 2 G ≤ D.map (MulAut.conj k).toMonoidHom :=
    sup_le (B6.thompsonJ_le S |>.trans hSDk)
      ((B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf).trans hSDk)
  have hreg := h.isRegular_of_lt hDklt hJ
  have hconjD := PSubgroupSelection.IsRegular.map_conj (f := c.selection) hreg k⁻¹
  rwa [CFSG.GroupTheory.map_conj_map_conj_inv k D] at hconjD

private theorem not_isPIsolatedOver_and_nonempty_g45f2b
    (h : GomiThm45Counterexample c G S) (hiso : ¬ IsPIsolatedOver 2 (autOn G (gomiV G)) ⊥)
    (hctrl : ControlsSylowIntersections 2
      {M : Subgroup ↥(autOn G (gomiV G)) | M ≠ ⊤ ∧ Odd M.index} ⊤) :
    (¬ IsPIsolatedOver 2 (⊤ : Subgroup ↥(autOn G (gomiV G))) ⊥) ∧
      {M : Subgroup ↥(autOn G (gomiV G)) | M ≠ ⊤ ∧ Odd M.index}.Nonempty := by
  have hX : ¬ IsPIsolatedOver 2 (⊤ : Subgroup ↥(autOn G (gomiV G))) ⊥ := by
    intro h'
    exact hiso ((isPIsolatedOver_subgroupOf_iff (p := 2)
      (H := (⊥ : Subgroup (MulAut ↥(gomiV G))))
      (K := autOn G (gomiV G)) (K' := autOn G (gomiV G)) bot_le le_rfl).mp
      (by simpa only [Subgroup.subgroupOf_self, Subgroup.bot_subgroupOf] using h'))
  have hO : ∀ P : Subgroup ↥(autOn G (gomiV G)), P.Normal → IsPGroup 2 P → P = ⊥ :=
    fun P hPN hP2 => eq_bot_of_normal_isPGroup_two_g45f1 (o2Trivial_autOn h) hPN hP2
  have hp : 2 ∣ Nat.card ↥(autOn G (gomiV G)) := by
    obtain ⟨A, hA⟩ := h.pset_nonempty
    exact even_iff_two_dvd.mp
      (E3.even_card_of_isPGroup hA.1 (E3.isPGroup_of_isElemAbelian2 hA.2.2.1) hA.2.1)
  exact ⟨hX, ControlsSylowIntersections.nonempty_of_not_isPIsolatedOver hctrl hX hO hp⟩

private theorem isRegular_of_controlsSylowIntersections_g45f2
    (h : GomiThm45Counterexample c G S) (hiso : ¬ IsPIsolatedOver 2 (autOn G (gomiV G)) ⊥)
    (hctrl : ControlsSylowIntersections 2
      {M : Subgroup ↥(autOn G (gomiV G)) | M ≠ ⊤ ∧ Odd M.index} ⊤) :
    c.selection.IsRegular G := by
  let Y : Subgroup (MulAut ↥(gomiV G)) := autOn G (gomiV G)
  let Mbar : Set (Subgroup ↥Y) := {M | M ≠ ⊤ ∧ Odd M.index}
  have hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  let ψ : ↥G →* ↥Y := (A4.actionOn (gomiV G) G hG).codRestrict Y (fun g =>
    (A4.mem_autOn_iff hG).2 ⟨g, rfl⟩)
  have hψ : Function.Surjective ψ := by
    intro a
    obtain ⟨g, hg⟩ := (A4.mem_autOn_iff hG).1 a.2
    exact ⟨g, Subtype.ext hg⟩
  obtain ⟨hX, hne⟩ := not_isPIsolatedOver_and_nonempty_g45f2b h hiso hctrl
  have hnormal : IsNormalSetIn Mbar ⊤ := isNormalSetIn_oddIndex_g45f2b
  have hind : ∀ M ∈ Mbar, ¬ 2 ∣ M.index := fun M hM h2 =>
    (Nat.not_even_iff_odd.2 hM.2) (even_iff_two_dvd.2 h2)
  let Dset : Set (Subgroup Ω) :=
    (fun X => X.map G.subtype) '' ((fun X => X.comap ψ) '' Mbar)
  have hctrl0 : ControlsSylowIntersections 2 ((fun X => X.comap ψ) '' Mbar) ⊤ :=
    ControlsSylowIntersections.comap_of_surjective (φ := ψ) hψ hnormal hne hind hctrl hX
  have hctrlG : ControlsSylowIntersections 2 Dset G :=
    ControlsSylowIntersections.map_subtype hctrl0
  have hreg : ∀ D ∈ Dset, c.selection.IsRegular D := by
    rintro D ⟨D₀, ⟨M, hM, rfl⟩, rfl⟩
    obtain ⟨hrel, hneG⟩ := relIndex_map_comap_g45f2b (G := G) ψ hψ hM.1
    exact isRegular_of_subgroup_of_odd_relIndex_g45f2b h (Subgroup.map_subtype_le _)
      (by rw [hrel]; exact hind M hM) hneG
  have hindD : ∀ D ∈ Dset, ¬ 2 ∣ D.relIndex G := by
    rintro D ⟨D₀, ⟨M, hM, rfl⟩, rfl⟩
    obtain ⟨hrel, -⟩ := relIndex_map_comap_g45f2b (G := G) ψ hψ hM.1
    rw [hrel]
    exact hind M hM
  exact PSubgroupSelection.IsRegular.of_controlsSylowIntersections
    (f := c.selection) (K := G) (fun D hD => by
      obtain ⟨D₀, -, rfl⟩ := hD
      exact Subgroup.map_subtype_le D₀) hindD hreg hctrlG

theorem isGomiStepF (h : GomiThm45Counterexample c G S) (hB : GomiBender)
    (hBSL : GomiBenderSL2) (h22 : GomiFact22) (h23 : GomiFact23)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) :
    IsGomiStepF (autOn S (gomiV G)) Lb := by
  by_cases hiso : IsPIsolatedOver 2 (autOn G (gomiV G)) ⊥
  · exact Or.inl (h.eq_of_isPIsolatedOver hB hBSL hL hiso).2
  rcases hL.type with hSL | hType
  · exact Or.inl ⟨1, le_rfl, hSL⟩
  by_contra hF
  exact h.not_isRegular (isRegular_of_controlsSylowIntersections_g45f2 h hiso
    (controlsSylowIntersections_of_not_isGomiStepF_g45f2 h h22 h23 hL hType hF))

private theorem false_of_isSLn_one_g45g {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (h : IsSLn ↥L 2 1) : False := by
  obtain ⟨K, hK, hFin, hKcard, ⟨e⟩⟩ := h
  have h6 : Nat.card ↥L = 6 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two K, hKcard]
    norm_num
  have : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  exact CFSG.Quasithin.G64.not_isQuasisimple_of_card_six h6 hq

private theorem commutator_map_conj_ne_bot_g45g {W : Type} [CommGroup W]
    {X Y : Subgroup (MulAut W)} {g : MulAut W} (h : ⁅X, Y⁆ ≠ ⊥) :
    ⁅X.map (MulAut.conj g).toMonoidHom, Y.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  rw [← Subgroup.map_commutator]
  exact fun hbot =>
    h ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hbot)

private theorem ne_bot_commutator_sSup_pstarSet_of_le {W : Type} [CommGroup W]
    {Y L : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L)
    (hL : L ≤ sSup (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet Y)) :
    ⁅L, sSup (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet Y)⁆ ≠ ⊥ := by
  intro hbot
  have hself : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
  have hle : ⁅L, L⁆ ≤
      ⁅L, sSup (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet Y)⁆ :=
    Subgroup.commutator_mono le_rfl hL
  rw [hself, hbot] at hle
  exact CFSG.Quasithin.FFJImage.ne_bot_of_isQuasisimple hq (le_bot_iff.mp hle)

private theorem exists_pstar1_ne_bot_commutator_g45g {W : Type} [CommGroup W]
    {Y L : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (hL1 : L ≤ gomiGstar1 Y) :
    ∃ A ∈ gomiPstar1Set Y, ⁅L, A⁆ ≠ ⊥ := by
  have hne : ⁅L, sSup (gomiPstar1Set Y)⁆ ≠ ⊥ := by
    intro hbot
    have hCL : L ≤ Subgroup.centralizer
        (sSup (gomiPstar1Set Y) : Subgroup (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hLc : L ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
      hCL.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hL1))
    have hbot' : ⁅L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLc
    rw [Subgroup.isPerfect_iff.mp hq.1] at hbot'
    exact CFSG.Quasithin.FFJImage.ne_bot_of_isQuasisimple hq hbot'
  by_contra hcon
  push Not at hcon
  refine hne ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  refine sSup_le fun A hA => ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hcon A hA

private theorem ne_bot_commutator_sSup_pstarSet_g45g {W : Type} [CommGroup W] [Finite W]
    {Y S L : Subgroup (MulAut W)} (hSyl : IsSylowIn 2 S Y)
    (hcomm : ∀ y ∈ Y, L.map (MulAut.conj y).toMonoidHom ≠ L →
      ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj y).toMonoidHom, a * b = b * a)
    (hsup : (⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom) ⊔ S = Y)
    (hq : CFSG.IsQuasisimple ↥L) (hL1 : L ≤ gomiGstar1 Y) :
    ⁅L, sSup (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet S)⁆ ≠ ⊥ := by
  have hN : (⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom) ≤
      Subgroup.normalizer (L : Set (MulAut W)) := iSup_map_conj_le_normalizer hcomm
  obtain ⟨A, hA1, hAne⟩ := exists_pstar1_ne_bot_commutator_g45g hq hL1
  have hAP : A ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet Y := hA1.1
  obtain ⟨y, hy, hAle⟩ :=
    CFSG.Quasithin.E3.exists_le_conj_of_isSylowIn (H := Y) (S := S) (Y := A) hSyl hAP.1.1
      (CFSG.Quasithin.E3.isPGroup_of_isElemAbelian2 hAP.1.2.2.1)
  have hBS : A.map (MulAut.conj y).toMonoidHom ≤ S := by
    rintro b ⟨a, ha, rfl⟩
    have hmem := (CFSG.Quasithin.mem_conjSubgroup_iff (A := S) (g := y) (x := a)).mp (hAle ha)
    simpa [MulAut.conj_apply] using hmem
  have hBmem : A.map (MulAut.conj y).toMonoidHom ∈
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet Y :=
    map_conj_mem_pstarSet hAP hy
  have hBne : ⁅L.map (MulAut.conj y).toMonoidHom,
      A.map (MulAut.conj y).toMonoidHom⁆ ≠ ⊥ := commutator_map_conj_ne_bot_g45g hAne
  obtain ⟨s, hs, hEq⟩ := exists_mem_map_conj_eq hSyl.le hN hsup hy
  have hBne' : ⁅L.map (MulAut.conj s).toMonoidHom,
      A.map (MulAut.conj y).toMonoidHom⁆ ≠ ⊥ := by rwa [← hEq]
  have hCne : ⁅L, (A.map (MulAut.conj y).toMonoidHom).map
      (MulAut.conj s⁻¹).toMonoidHom⁆ ≠ ⊥ := by
    have h3 := commutator_map_conj_ne_bot_g45g (X := L.map (MulAut.conj s).toMonoidHom)
      (Y := A.map (MulAut.conj y).toMonoidHom) (g := s⁻¹) hBne'
    rwa [map_conj_map_conj_inv s L] at h3
  have hCmem : (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom ∈
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet S := by
    refine (mem_pstarSet_iff_of_le hSyl.le).mpr ⟨?_, ?_⟩
    · exact map_conj_mem_pstarSet hBmem (hSyl.le (S.inv_mem hs))
    · rintro c ⟨b, hb, rfl⟩
      simpa [MulAut.conj_apply] using S.mul_mem (S.mul_mem (S.inv_mem hs) (hBS hb)) hs
  exact fun hbot => hCne (le_bot_iff.mp
    ((Subgroup.commutator_mono le_rfl (le_sSup hCmem)).trans (le_of_eq hbot)))

private theorem fixV_sylow_le_fixV_conj_g45g (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hle : CFSG.Quasithin.fixV (autOn S (gomiV G)) ≤ CFSG.Quasithin.fixV Lb) :
    CFSG.Quasithin.fixV (autOn S (gomiV G)) ≤
      CFSG.Quasithin.fixV (⨆ y ∈ autOn G (gomiV G), Lb.map (MulAut.conj y).toMonoidHom) := by
  have hN : (⨆ y ∈ autOn G (gomiV G), Lb.map (MulAut.conj y).toMonoidHom) ≤
      Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) :=
    iSup_map_conj_le_normalizer hL.commute
  have hmapS : ∀ s ∈ autOn S (gomiV G),
      (CFSG.Quasithin.fixV (autOn S (gomiV G))).map s.toMonoidHom =
        CFSG.Quasithin.fixV (autOn S (gomiV G)) := by
    intro s hs
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      show s v ∈ CFSG.Quasithin.fixV (autOn S (gomiV G))
      rw [show s v = v from hv s hs]
      exact hv
    · intro v hv
      refine ⟨v, hv, ?_⟩
      show (s : MulAut ↥(gomiV G)) v = v
      exact hv s hs
  have hfixle : ∀ y ∈ autOn G (gomiV G),
      CFSG.Quasithin.fixV (autOn S (gomiV G)) ≤
        CFSG.Quasithin.fixV (Lb.map (MulAut.conj y).toMonoidHom) := by
    intro y hy
    obtain ⟨s, hs, hEq⟩ := exists_mem_map_conj_eq (isSylowIn_autOn h).le hN hL.sup_eq hy
    rw [hEq, CFSG.Quasithin.fixV_map_conj_eq, ← hmapS s hs]
    exact Subgroup.map_mono hle
  have hconj : (⨆ y ∈ autOn G (gomiV G), Lb.map (MulAut.conj y).toMonoidHom) ≤
      CFSG.Quasithin.centSub (CFSG.Quasithin.fixV (autOn S (gomiV G))) := by
    refine iSup_le fun y => iSup_le fun hy => ?_
    intro a ha
    rw [CFSG.Quasithin.mem_centSub]
    intro v hv
    exact CFSG.Quasithin.mem_fixV.mp (hfixle y hy hv) a ha
  intro v hv
  rw [CFSG.Quasithin.mem_fixV]
  intro n hn
  exact CFSG.Quasithin.mem_centSub.mp (hconj hn) v hv

private theorem fixV_sylow_le_fixV_autOn_g45g (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hle : CFSG.Quasithin.fixV (autOn S (gomiV G)) ≤ CFSG.Quasithin.fixV Lb) :
    CFSG.Quasithin.fixV (autOn S (gomiV G)) ≤ CFSG.Quasithin.fixV (autOn G (gomiV G)) := by
  have hfixN := fixV_sylow_le_fixV_conj_g45g h hL hle
  rw [← hL.sup_eq, CFSG.Quasithin.FixVLat.fixV_sup_eq]
  exact le_inf hfixN le_rfl

private theorem omegaOneCenterOf_le_fixV_sylow_g45g (h : GomiThm45Counterexample c G S) :
    (CFSG.Quasithin.omegaOneCenterOf S).subgroupOf (gomiV G) ≤
      CFSG.Quasithin.fixV (autOn S (gomiV G)) := by
  have hVle : CFSG.Quasithin.omegaOneCenterOf S ≤ gomiV G :=
    CFSG.GroupTheory.omegaOneCenterOf_le_gomiV_of_pCoreOf_le h.hyp43.charTwo
      h.isSylowTwoOf.1
      (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf)
  intro v hv
  rw [Subgroup.mem_subgroupOf] at hv
  rw [CFSG.Quasithin.mem_fixV]
  intro a ha
  obtain ⟨n, hn, rfl⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp ha
  apply Subtype.ext
  rw [CFSG.Quasithin.AutOn.coe_conjAct_apply,
    Subgroup.mem_centralizer_iff.mp
      (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf S hv).2 (n : Ω) hn]
  group

private theorem le_centralizer_omegaOneCenterOf_g45g (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hle : CFSG.Quasithin.fixV (autOn S (gomiV G)) ≤ CFSG.Quasithin.fixV Lb) :
    G ≤ Subgroup.centralizer (CFSG.Quasithin.omegaOneCenterOf S : Set Ω) := by
  have hGH := fixV_sylow_le_fixV_autOn_g45g h hL hle
  have hfixG : CFSG.Quasithin.fixV (autOn G (gomiV G)) =
      (Subgroup.centralizer (G : Set Ω)).subgroupOf (gomiV G) :=
    CFSG.Quasithin.AutOn.fixV_autOn_eq (gomiV_moduleSetting G).2
  have hVle : CFSG.Quasithin.omegaOneCenterOf S ≤ gomiV G :=
    CFSG.GroupTheory.omegaOneCenterOf_le_gomiV_of_pCoreOf_le h.hyp43.charTwo
      h.isSylowTwoOf.1
      (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf)
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hmem : (⟨v, hVle hv⟩ : ↥(gomiV G)) ∈
      (Subgroup.centralizer (G : Set Ω)).subgroupOf (gomiV G) := by
    rw [← hfixG]
    exact hGH (omegaOneCenterOf_le_fixV_sylow_g45g h (Subgroup.mem_subgroupOf.mpr hv))
  rw [Subgroup.mem_subgroupOf] at hmem
  exact (Subgroup.mem_centralizer_iff.mp hmem g hg).symm

private theorem not_fixV_sylow_le_fixV_g45g (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) :
    ¬ CFSG.Quasithin.fixV (autOn S (gomiV G)) ≤ CFSG.Quasithin.fixV Lb := by
  intro hle
  have hcent := le_centralizer_omegaOneCenterOf_g45g h hL hle
  refine h.not_isRegular (PSubgroupSelection.isRegular_of_le_normalizer
    (f := c.selection) (F := CFSG.Quasithin.omegaOneCenterOf S)
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp h.isSylowTwoOf) ?_
    (hcent.trans (Subgroup.centralizer_le_normalizer _)))
  change CFSG.Quasithin.omegaOneCenterOf S ∈
    ({c.C₁ S, c.C₂ S, CFSG.Quasithin.omegaOneCenterOf S} : Set (Subgroup Ω))
  simp

private theorem isGomiStepG_of_mem_gomiNSet_g45g (h : GomiThm45Counterexample c G S)
    (h31 : GomiFact31) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hP0 : (gomiPstar0Set (autOn G (gomiV G))).Nonempty)
    (hNmem : Lb ∈ gomiNSet (autOn G (gomiV G))) : IsGomiStepG Lb := by
  have hV2 : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)
  have hO2 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O2Trivial
      (gomiGstar0 (autOn G (gomiV G))) :=
    o2Trivial_of_normal (o2Trivial_autOn h) (gomiGstar0_le _) (gomiGstar0_subgroupOf_normal _)
  obtain ⟨⟨hSLn, -, -, -⟩, ⟨hNat, -, -⟩, -, -⟩ :=
    h31 ↥(gomiV G) hV2 (autOn G (gomiV G)) hP0 hO2
  have hker : gomiWXKer Lb = ⊥ := by
    rw [gomiWXKer]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c167_inf_fixV_eq_bot_of_binaryNaturalSL
      (by norm_num) (hNat Lb hNmem)
  exact Or.inl ⟨1, le_rfl, hSLn Lb hNmem, by rw [hker]; exact hNat Lb hNmem⟩

private theorem gomiFact37Hyp_of_isSLn_g45g {W : Type} [CommGroup W]
    {Y S L : Subgroup (MulAut W)} {m : ℕ} (hP : (Pset Y).Nonempty)
    (hSyl : IsSylowIn 2 S Y) (hLY : L ≤ Y) (hsub : (L.subgroupOf Y).IsSubnormal)
    (hm2 : 2 ≤ m) (hSLn : IsSLn ↥L 2 m) : GomiFact37Hyp Y S L := by
  refine ⟨hP, hSyl, hLY, hsub, Or.inl ⟨m, hm2, Or.inl hSLn⟩, ?_⟩
  intro hAlt3
  obtain ⟨-, h35⟩ := eq_two_and_eq_five_of_isSLn_of_isAlt (by omega) hSLn hAlt3
  exact absurd h35 (by norm_num)

private theorem gomiFact37Hyp_of_isAlt_g45g {W : Type} [CommGroup W]
    {Y S L : Subgroup (MulAut W)} {m : ℕ} (hP : (Pset Y).Nonempty)
    (hSyl : IsSylowIn 2 S Y) (hLY : L ≤ Y) (hsub : (L.subgroupOf Y).IsSubnormal)
    (hm2 : 2 ≤ m) (hAlt : IsAlt ↥L (2 ^ m + 1)) : GomiFact37Hyp Y S L := by
  have hpow : 2 * 2 ^ (m - 1) = 2 ^ m := by
    rw [mul_comm, ← pow_succ, show m - 1 + 1 = m by omega]
  have hpos : 2 ≤ 2 ^ (m - 1) + 1 := by
    have h2 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    omega
  have hAlt' : IsAlt ↥L (2 * (2 ^ (m - 1) + 1) - 1) := by
    have heq : 2 * (2 ^ (m - 1) + 1) - 1 = 2 ^ m + 1 := by
      rw [Nat.mul_add, Nat.mul_one, hpow]; omega
    rwa [heq]
  refine ⟨hP, hSyl, hLY, hsub, Or.inl ⟨2 ^ (m - 1) + 1, hpos, Or.inr hAlt'⟩, ?_⟩
  intro hAlt3
  obtain ⟨e3⟩ := hAlt3
  obtain ⟨e⟩ := hAlt
  have hEq : 3 = 2 ^ m + 1 :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d.n_eq_of_alt_equiv
      (by norm_num) (by omega) (e3.symm.trans e)
  have h8 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  omega

private theorem isGomiStepG_of_isSLn_g45g {W : Type} [CommGroup W] [Finite W]
    (h37 : GomiFact37Two) (hW2 : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} {m : ℕ} (hm1 : 1 ≤ m) (hSLn : IsSLn ↥L 2 m)
    (hHyp : GomiFact37Hyp Y S L)
    (hne : ⁅L, sSup (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet Y)⁆ ≠ ⊥) :
    IsGomiStepG L := by
  rcases h37 W hW2 Y S L hHyp hne with
    ⟨m', hm'2, hsln', hnat'⟩ | ⟨m', hm'2, halt', hmod'⟩ | ⟨halt7, -⟩
  · exact Or.inl ⟨m', by omega, hsln', hnat'⟩
  · obtain ⟨-, h5⟩ := eq_two_and_eq_five_of_isSLn_of_isAlt hm1 hSLn halt'
    refine Or.inr ⟨2, by norm_num, ?_, ?_⟩
    · rw [show 2 ^ 2 + 1 = 5 by norm_num, ← h5]; exact halt'
    · rw [show 2 ^ 2 + 1 = 5 by norm_num, ← h5]; exact hmod'
  · obtain ⟨-, h75⟩ := eq_two_and_eq_five_of_isSLn_of_isAlt hm1 hSLn halt7
    exact absurd h75 (by norm_num)

private theorem isGomiStepG_of_isAlt_g45g {W : Type} [CommGroup W] [Finite W]
    (h37 : GomiFact37Two) (hW2 : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} {m : ℕ} (hm3 : 3 ≤ m) (hAlt : IsAlt ↥L (2 ^ m + 1))
    (hHyp : GomiFact37Hyp Y S L)
    (hne : ⁅L, sSup (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet Y)⁆ ≠ ⊥) :
    IsGomiStepG L := by
  have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rcases h37 W hW2 Y S L hHyp hne with
    ⟨m', hm'2, hsln', -⟩ | ⟨m', hm'2, halt', hmod'⟩ | ⟨halt7, -⟩
  · obtain ⟨-, h5⟩ := eq_two_and_eq_five_of_isSLn_of_isAlt (by omega) hsln' hAlt
    have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    omega
  · have hEq : 2 * m' - 1 = 2 ^ m + 1 :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d.n_eq_of_alt_equiv
        (by omega) (by omega) (halt'.some.symm.trans hAlt.some)
    exact Or.inr ⟨m, by omega, hAlt, by rw [← hEq]; exact hmod'⟩
  · obtain ⟨e7⟩ := halt7
    obtain ⟨e⟩ := hAlt
    have hEq : 7 = 2 ^ m + 1 :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d.n_eq_of_alt_equiv
        (by norm_num) (by omega) (e7.symm.trans e)
    have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    omega

private theorem false_of_isGomiParabolicSwap_g45g (h : GomiThm45Counterexample c G S)
    (h36 : GomiFact36) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hcompG : CFSG.IsComponent (Lb.subgroupOf (autOn G (gomiV G))))
    (hqLb : CFSG.IsQuasisimple ↥Lb) (hLle1 : Lb ≤ gomiGstar1 (autOn G (gomiV G)))
    (hfcheb : IsGomiChevTwo ↥Lb)
    (hfcon : IsGomiL3 (↥Lb ⧸ Subgroup.center ↥Lb) ∨
      IsGomiSp4 (↥Lb ⧸ Subgroup.center ↥Lb))
    (hfswap : IsGomiParabolicSwap (autOn S (gomiV G)) Lb) : False := by
  have hV2 : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)
  exact absurd hfswap
    (h36 ↥(gomiV G) hV2 (autOn G (gomiV G)) (autOn S (gomiV G)) Lb (isSylowIn_autOn h)
      hL.le hcompG
      (ne_bot_commutator_sSup_pstarSet_g45g (isSylowIn_autOn h) hL.commute hL.sup_eq
        hqLb hLle1)
      (not_fixV_sylow_le_fixV_g45g h hL) hfcheb hfcon)

theorem isGomiStepG (h : GomiThm45Counterexample c G S) (h31 : GomiFact31) (h36 : GomiFact36)
    (h37 : GomiFact37Two) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hf : IsGomiStepF (autOn S (gomiV G)) Lb) :
    IsGomiStepG Lb := by
  rcases hL.mem_or with ⟨hP0, hNmem⟩ | ⟨hP0, hLle1, hcomp⟩
  · exact isGomiStepG_of_mem_gomiNSet_g45g h h31 hP0 hNmem
  · have hcompG : CFSG.IsComponent (Lb.subgroupOf (autOn G (gomiV G))) :=
      isComponent_subgroupOf_of_normal hLle1 (gomiGstar1_le _)
        (gomiGstar1_subgroupOf_normal _) hcomp
    have hqLb : CFSG.IsQuasisimple ↥Lb :=
      (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hL.le)).mp hcompG.1
    have hG1' : ⁅Lb, sSup (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet
        (autOn G (gomiV G)))⁆ ≠ ⊥ :=
      ne_bot_commutator_sSup_pstarSet_of_le hqLb
        (hLle1.trans (gomiGstar1_le_sSup_pstarSet _))
    rcases hf with ⟨m, hmle, hSLn⟩ | ⟨hfcheb, hfcon, hfswap⟩ | ⟨m, hm3, hAlt⟩
    · by_cases hm : m = 1
      · exact False.elim (false_of_isSLn_one_g45g hqLb (by rwa [hm] at hSLn))
      · exact isGomiStepG_of_isSLn_g45g h37 (fun w =>
            Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)) hmle hSLn
          (gomiFact37Hyp_of_isSLn_g45g (pset_nonempty h) (isSylowIn_autOn h) hL.le
            hcompG.2 (by omega) hSLn) hG1'
    · exact False.elim (false_of_isGomiParabolicSwap_g45g h h36 hL hcompG hqLb hLle1
        hfcheb hfcon hfswap)
    · exact isGomiStepG_of_isAlt_g45g h37 (fun w =>
          Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)) hm3 hAlt
        (gomiFact37Hyp_of_isAlt_g45g (pset_nonempty h) (isSylowIn_autOn h) hL.le
          hcompG.2 (by omega) hAlt) hG1'

theorem gomiFact37Hyp_of_isGomiStepG (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hLle1 : Lb ≤ gomiGstar1 (autOn G (gomiV G)))
    (hcomp : CFSG.IsComponent (Lb.subgroupOf (gomiGstar1 (autOn G (gomiV G)))))
    (hg : IsGomiStepG Lb) :
    GomiFact37Hyp (autOn G (gomiV G)) (autOn S (gomiV G)) Lb ∧
      ⁅Lb, ffJ (autOn G (gomiV G))⁆ ≠ ⊥ ∧
      ((∃ m : ℕ, 2 ≤ m ∧ IsSLn ↥Lb 2 m ∧ BinaryNaturalSL Lb (commV Lb) (gomiWXKer Lb) 2 m) ∨
        ∃ m : ℕ, 2 ≤ m ∧ IsAlt ↥Lb (2 * m - 1) ∧
          (FFModel.altDn (2 * m - 1)).Realizes Lb (commV Lb) (gomiWXKer Lb)) := by
  have hcompG : CFSG.IsComponent (Lb.subgroupOf (autOn G (gomiV G))) :=
    isComponent_subgroupOf_of_normal hLle1 (gomiGstar1_le _)
      (gomiGstar1_subgroupOf_normal _) hcomp
  have hqLb : CFSG.IsQuasisimple ↥Lb :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hL.le)).mp hcompG.1
  have hne : ⁅Lb, sSup (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PstarSet
      (autOn G (gomiV G)))⁆ ≠ ⊥ :=
    ne_bot_commutator_sSup_pstarSet_of_le hqLb
      (hLle1.trans (gomiGstar1_le_sSup_pstarSet _))
  have hJ : ⁅Lb, ffJ (autOn G (gomiV G))⁆ ≠ ⊥ := fun hbot => hne (le_bot_iff.mp
    ((Subgroup.commutator_mono le_rfl (sSup_pstarSet_le_ffJ _)).trans (le_of_eq hbot)))
  rcases hg with ⟨m, hm1, hSLn, hnat⟩ | ⟨m, hm2, hAlt, hmod⟩
  · obtain rfl | hlt := Nat.eq_or_lt_of_le hm1
    · exact absurd hSLn (false_of_isSLn_one_g45g hqLb)
    · exact ⟨gomiFact37Hyp_of_isSLn_g45g (pset_nonempty h) (isSylowIn_autOn h) hL.le
        hcompG.2 (by omega) hSLn, hJ, Or.inl ⟨m, hlt, hSLn, hnat⟩⟩
  · have he : 2 * (2 ^ (m - 1) + 1) - 1 = 2 ^ m + 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      omega
    have h2 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    refine ⟨gomiFact37Hyp_of_isAlt_g45g (pset_nonempty h) (isSylowIn_autOn h) hL.le
        hcompG.2 hm2 hAlt, hJ, Or.inr ⟨2 ^ (m - 1) + 1, by omega, ?_, ?_⟩⟩
    · rw [he]
      exact hAlt
    · rw [he]
      exact hmod

end GomiThm45Counterexample

end CFSG.GroupTheory
