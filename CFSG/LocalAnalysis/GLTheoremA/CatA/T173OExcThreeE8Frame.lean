module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveQ2Char
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Census.CommonUnipotent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTwRigidLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3T
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KGD.D4QA1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.EPilot
open CFSG.StandardType CFSG.StandardType.TableBExcTwo CFSG.StandardType.TableBExcTwoTB
open CFSG.SeitzReduction.E8Pilot CFSG.HardMathSupport.Timmesfeld.CrossChar

section Frame

variable (K : Type) [Field K] [Finite K] [CharP K 2]

noncomputable def e8FrameV : Subgroup ↥(adjointGroup .E8 K) :=
  ((tE K frameE7).range.map (e7LeviEquiv K).symm.toMonoidHom).map (e7Levi K).subtype

variable {K}

private theorem e7Embed_frameE7Root :
    ∀ i : Fin 7, e7Embed (frameE7Root i) = frameE8Root i.succ := by
  decide +kernel

private theorem coe_tGen_eq_pinnedX_mul {τ : Tag} {d : ℕ} (F : OrthFrame τ d) (i : Fin (d + 1)) :
    ((tGen K F i : adjointGroup τ K) : ModGL τ K) =
      pinnedX τ K (F.root i) 1 * pinnedX τ K (-(F.root i)) 1 := by
  rw [tGen, coe_rho, map_mul, rootSL2_uSL_two, rootSL2_vSL_two (F.isRoot i)]

theorem e7LeviEquiv_symm_tGen (i : Fin 7) :
    (((e7LeviEquiv K).symm (tGen K frameE7 i) : e7Levi K) : ↥(adjointGroup .E8 K)) =
      tGen K frameE8 i.succ := by
  have hβ : IsRoot .E7 (frameE7Root i) := frameE7.isRoot i
  set g₁ : ↥(adjointGroup .E7 K) :=
    ⟨pinnedX .E7 K (frameE7Root i) 1, pinnedX_mem_adjointGroup _ 1⟩ with hg₁
  set g₂ : ↥(adjointGroup .E7 K) :=
    ⟨pinnedX .E7 K (-(frameE7Root i)) 1, pinnedX_mem_adjointGroup _ 1⟩ with hg₂
  have hgen : tGen K frameE7 i = g₁ * g₂ :=
    Subtype.ext (by rw [coe_tGen_eq_pinnedX_mul]; rfl)
  rw [hgen, map_mul]
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, e7LeviEquiv_symm_pinnedX hβ 1,
    e7LeviEquiv_symm_pinnedX (IsRoot.neg hβ) 1]
  change ((e7LeviPar K (frameE7Root i) 1 : ↥(adjointGroup .E8 K)) : ModGL .E8 K) *
      ((e7LeviPar K (-(frameE7Root i)) 1 : ↥(adjointGroup .E8 K)) : ModGL .E8 K) =
    ((tGen K frameE8 i.succ : ↥(adjointGroup .E8 K)) : ModGL .E8 K)
  rw [coe_e7LeviPar, coe_e7LeviPar, e7Embed_neg, e7Embed_frameE7Root i]
  exact (coe_tGen_eq_pinnedX_mul (K := K) frameE8 i.succ).symm

private theorem e7LeviEquiv_symm_tD (f : Fin 7 → Multiplicative (ZMod 3)) :
    (((e7LeviEquiv K).symm (tD K frameE7 f) : e7Levi K) : ↥(adjointGroup .E8 K)) =
      tD K frameE8 (Fin.cons 1 f) := by
  let c : (Fin 7 → Multiplicative (ZMod 3)) →* (Fin 8 → Multiplicative (ZMod 3)) :=
    MonoidHom.pi fun j =>
      Fin.cases (1 : (Fin 7 → Multiplicative (ZMod 3)) →* Multiplicative (ZMod 3))
        (fun i => Pi.evalMonoidHom (fun _ : Fin 7 => Multiplicative (ZMod 3)) i) j
  have hc : ∀ g : Fin 7 → Multiplicative (ZMod 3), c g = Fin.cons 1 g := by
    intro g
    funext j
    refine Fin.cases ?_ ?_ j <;> simp [c]
  have hc_single : ∀ (i : Fin 7) (a : Multiplicative (ZMod 3)),
      c (Pi.mulSingle i a) = Pi.mulSingle i.succ a := by
    intro i a
    rw [hc]
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero, Pi.mulSingle_eq_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    · intro k
      by_cases h : k = i
      · subst h
        simp [Fin.cons_succ]
      · simp [Fin.cons_succ, Pi.mulSingle_eq_of_ne h, Fin.succ_inj, h]
  let φ : ↥(adjointGroup .E7 K) →* ↥(adjointGroup .E8 K) :=
    (e7Levi K).subtype.comp (e7LeviEquiv K).symm.toMonoidHom
  have hφ : ∀ (i : Fin 7) (a : Multiplicative (ZMod 3)),
      φ (tC K frameE7 i a) = tC K frameE8 i.succ a := by
    intro i a
    rw [tC_apply, tC_apply, map_pow]
    congr 1
    exact e7LeviEquiv_symm_tGen i
  have hLR : φ.comp (tD K frameE7) = (tD K frameE8).comp c := by
    refine MonoidHom.pi_ext fun i a => ?_
    simp only [MonoidHom.comp_apply]
    rw [tD, MonoidHom.noncommPiCoprod_mulSingle, hc_single,
      tD, MonoidHom.noncommPiCoprod_mulSingle]
    exact hφ i a
  have h := DFunLike.congr_fun hLR f
  simp only [MonoidHom.comp_apply] at h
  rw [hc f] at h
  exact h

private theorem e7LeviEquiv_symm_tE (u : Fin 7 → ZMod 3) :
    (((e7LeviEquiv K).symm (tE K frameE7 (Multiplicative.ofAdd u)) : e7Levi K) :
        ↥(adjointGroup .E8 K)) =
      tE K frameE8 (Multiplicative.ofAdd (Fin.cons 0 u)) := by
  rw [tE_apply, tE_apply, e7LeviEquiv_symm_tD]
  rfl

theorem mem_e8FrameV_iff {x : ↥(adjointGroup .E8 K)} :
    x ∈ e8FrameV K ↔ ∃ v : Fin 8 → ZMod 3, v 0 = 0 ∧
      x = tE K frameE8 (Multiplicative.ofAdd v) := by
  constructor
  · rintro ⟨y, ⟨z, ⟨g, rfl⟩, rfl⟩, rfl⟩
    refine ⟨Fin.cons 0 (Multiplicative.toAdd g), by simp, ?_⟩
    change (e7Levi K).subtype ((e7LeviEquiv K).symm.toMonoidHom
      (tE K frameE7 (Multiplicative.ofAdd (Multiplicative.toAdd g)))) =
        tE K frameE8 (Multiplicative.ofAdd (Fin.cons 0 (Multiplicative.toAdd g)))
    exact e7LeviEquiv_symm_tE (Multiplicative.toAdd g)
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, rfl⟩ : ∃ u : Fin 7 → ZMod 3, v = Fin.cons 0 u := by
      refine ⟨Fin.tail v, ?_⟩
      calc v = Fin.cons (v 0) (Fin.tail v) := (Fin.cons_self_tail v).symm
        _ = Fin.cons 0 (Fin.tail v) := by rw [hv]
    rw [← e7LeviEquiv_symm_tE u]
    refine ⟨(e7LeviEquiv K).symm (tE K frameE7 (Multiplicative.ofAdd u)), ?_, rfl⟩
    exact ⟨_, ⟨Multiplicative.ofAdd u, rfl⟩, rfl⟩

theorem e8FrameV_le_e7Levi : e8FrameV K ≤ e7Levi K := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem card_e8FrameV : Nat.card (e8FrameV K) = 3 ^ 7 := by
  rw [e8FrameV, Subgroup.card_map_of_injective (e7Levi K).subtype_injective,
    Subgroup.card_map_of_injective (e7LeviEquiv K).symm.injective,
    ← Nat.card_congr (MonoidHom.ofInjective (tE_injective (K := K) frameE7)).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem tGen_zero_notMem_e8FrameV : tGen K frameE8 0 ∉ e8FrameV K := by
  intro h
  rw [mem_e8FrameV_iff] at h
  obtain ⟨v, hv0, hv⟩ := h
  have hsingle : tGen K frameE8 0 =
      tE K frameE8 (Multiplicative.ofAdd (Pi.single 0 1)) := by
    rw [tE_single, tC_one]
  have hEq : Multiplicative.ofAdd (Pi.single (0 : Fin 8) 1) =
      Multiplicative.ofAdd v :=
    tE_injective frameE8 (hsingle.symm.trans hv)
  have hsv : Pi.single (0 : Fin 8) 1 = v := Multiplicative.ofAdd.injective hEq
  have h0 := congrFun hsv 0
  rw [Pi.single_eq_same, hv0] at h0
  exact one_ne_zero h0

theorem e7Levi_le_centralizer_tGen_zero :
    e7Levi K ≤ Subgroup.centralizer ({tGen K frameE8 0} : Set ↥(adjointGroup .E8 K)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hg' : (g : ModGL .E8 K) ∈ rootSpan .E8 K (perpRoots .E8) :=
    (mem_e7Levi_iff (K := K)).mp hg
  have ht : (tGen K frameE8 0 : ModGL .E8 K) ∈ highRootSL2 .E8 K := by
    have hmem := rootSL2_mem_rootSpan_pair (τ := .E8) (L := K)
      (β := CFSG.SeitzReduction.highRoot .E8)
      (CFSG.SeitzReduction.isRoot_highRoot .E8) (uSL 1 * vSL 1)
    rw [rootSpan, iSup_insert, iSup_singleton] at hmem
    have hθ : frameE8.root 0 = CFSG.SeitzReduction.highRoot .E8 := rfl
    simpa [tGen, coe_rho, highRootSL2, hθ] using hmem
  have hcomm : (g : ModGL .E8 K) * (tGen K frameE8 0 : ModGL .E8 K) =
      (tGen K frameE8 0 : ModGL .E8 K) * (g : ModGL .E8 K) :=
    (Subgroup.mem_centralizer_iff.mp
      (highRootSL2_le_centralizer_perpLevi (Or.inr (Or.inr rfl)) ht)) _ hg'
  exact Subtype.ext hcomm

theorem exists_conj_eq_e8FrameV_of_le_e7Levi (hF : Nat.card K = 2)
    {E : Subgroup ↥(adjointGroup .E8 K)} (hEM : E ≤ e7Levi K) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 7 ≤ Nat.card E) :
    ∃ m ∈ e7Levi K, E.map (MulAut.conj m).toMonoidHom = e8FrameV K := by
  let M := e7Levi K
  let e := e7LeviEquiv K
  have hcard' : 3 ^ 7 ≤ Nat.card ((E.subgroupOf M).map e.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv]
    exact hcard
  obtain ⟨c, hc⟩ := exists_conj_frame_of_card_E7 hF
    ((hE.subgroupOf M).map e.toMonoidHom) hcard'
  set a : ↥M := e.symm c with ha
  have h1 : ((E.subgroupOf M).map e.toMonoidHom).map e.symm.toMonoidHom =
      E.subgroupOf M := by
    rw [Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id ↥M := by
      refine MonoidHom.ext fun x => ?_
      exact e.symm_apply_apply x
    rw [hcomp, Subgroup.map_id]
  have h2 : E.subgroupOf M =
      ((tE K frameE7).range.map (MulAut.conj c).toMonoidHom).map e.symm.toMonoidHom := by
    rw [← h1, hc]
  have hcomp : e.symm.toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp e.symm.toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    simp [ha, MulAut.conj_apply]
  have h3 : ((tE K frameE7).range.map (MulAut.conj c).toMonoidHom).map
        e.symm.toMonoidHom =
      ((tE K frameE7).range.map e.symm.toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hframeSub : (e8FrameV K).subgroupOf M = (tE K frameE7).range.map e.symm.toMonoidHom := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (e8FrameV_le_e7Levi), e8FrameV]
  have h4 : E.subgroupOf M = ((e8FrameV K).subgroupOf M).map (MulAut.conj a).toMonoidHom := by
    rw [h2, h3, hframeSub]
  have hcomp' : M.subtype.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (M.subtype a)).toMonoidHom.comp M.subtype := by
    refine MonoidHom.ext fun x => ?_
    simp [MulAut.conj_apply]
  have hEeq : E = (e8FrameV K).map (MulAut.conj (M.subtype a)).toMonoidHom := by
    calc E = (E.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hEM).symm
      _ = (((e8FrameV K).subgroupOf M).map (MulAut.conj a).toMonoidHom).map M.subtype := by
          rw [h4]
      _ = ((e8FrameV K).subgroupOf M).map (M.subtype.comp (MulAut.conj a).toMonoidHom) := by
          rw [Subgroup.map_map]
      _ = ((e8FrameV K).subgroupOf M).map
            ((MulAut.conj (M.subtype a)).toMonoidHom.comp M.subtype) := by rw [hcomp']
      _ = (((e8FrameV K).subgroupOf M).map M.subtype).map
            (MulAut.conj (M.subtype a)).toMonoidHom := by rw [Subgroup.map_map]
      _ = (e8FrameV K).map (MulAut.conj (M.subtype a)).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le (e8FrameV_le_e7Levi)]
  refine ⟨((M.subtype a)⁻¹), M.inv_mem a.2, ?_⟩
  rw [hEeq, CFSG.LieType.Chevalley.map_conj_inv_map_conj]

end Frame

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
