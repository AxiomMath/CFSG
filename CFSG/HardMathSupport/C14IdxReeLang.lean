module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx
public import CFSG.RankThree.PartOne.TCX.Ree.Closure
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.LieType.AlgebraicGroups.ToralCentralizerComponent
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangCurves
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.RankThree.PartOne.KLR.FrameTorus
public import CFSG.LieType.AlgebraicGroups.SeminaireExp3Basic
public import CFSG.HardMathSupport.C14IdxReeEndo
import CFSG.LocalAnalysis.StandardType.GGReeLangPositionF4

public noncomputable section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.TCX.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction WithConv
open scoped CFSG.ConvolutionPoints
open CFSG.StandardType (ggReeLangAux_exists_S0_co ggReeLangAux_famSub ggReeLangAux_famSubImage
  ggReeLangAux_isConnected_famSub ggReeLangAux_famSub_sigmaB)


private theorem reeLang_famSub_stable
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (C : ReeClosure L) (b' : ℕ) {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ)
    (σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐc[L] (realizedCoord ReeTag.F4.tag L))
    (hσ₀ : ∀ φ, realizedPointEquiv ReeTag.F4.tag L (pointMap σ₀ φ) =
      (C.Φ * C.Fr ^ b') (realizedPointEquiv ReeTag.F4.tag L φ))
    (u : adjointGroup ReeTag.F4.tag L)
    (hM : ∀ g ∈ ggReeLangAux_famSub b,
      u * (C.Φ * C.Fr ^ b') g * u⁻¹ ∈ ggReeLangAux_famSub b) :
    ∀ y ∈ subgroupPoints (ggReeLangAux_famSubImage b),
      y.comp (((σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L]
        (realizedCoord ReeTag.F4.tag L)).comp
        (innerCo ((realizedPointEquiv ReeTag.F4.tag L).symm u)))) ∈
        subgroupPoints (ggReeLangAux_famSubImage b) := by
  classical
  intro y hy
  set Eq := realizedPointEquiv ReeTag.F4.tag L with hEq
  set x := Eq.symm u with hx
  set t : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L) :=
    (σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)).comp (innerCo x)
    with htdef
  set Fb := ggReeLangAux_famSub b with hFb
  set G' := Fb.map Eq.symm.toMonoidHom with hG'def
  have hmemG' : ∀ y : (realizedCoord ReeTag.F4.tag L) →ₐ[L] L,
      y ∈ subgroupPoints G' ↔ Eq (toConv y) ∈ Fb := by
    intro y
    change toConv y ∈ G' ↔ _
    rw [hG'def, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have ht : ∀ y : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L),
      Eq (toConv (y.ofConv.comp t)) = u * (C.Φ * C.Fr ^ b') (Eq y) * u⁻¹ := by
    intro y
    rw [htdef, point_comp_twist, map_mul, map_mul, map_inv, hσ₀, hx,
      MulEquiv.apply_symm_apply]
  have hy' : y ∈ subgroupPoints G' := hy
  have hgoal : y.comp t ∈ subgroupPoints G' := by
    rw [hmemG']
    have h := hM (Eq (toConv y)) ((hmemG' y).1 hy')
    have h2 := ht (toConv y)
    rw [ofConv_toConv] at h2
    rw [h2]
    exact h
  exact hgoal

private theorem reeLang_lang_famSub
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (C : ReeClosure L) (b' : ℕ) {ι : Type} (b : ι → Fin ReeTag.F4.tag.rank → Lˣ)
    (u : adjointGroup ReeTag.F4.tag L)
    (hM : ∀ g ∈ ggReeLangAux_famSub b,
      u * (C.Φ * C.Fr ^ b') g * u⁻¹ ∈ ggReeLangAux_famSub b) :
    ∀ c : adjointGroup ReeTag.F4.tag L, c ∈ ggReeLangAux_famSub b →
      ∃ z : adjointGroup ReeTag.F4.tag L, z ∈ ggReeLangAux_famSub b ∧
        z⁻¹ * (u * (C.Φ * C.Fr ^ b') z * u⁻¹) = c := by
  classical
  obtain ⟨σ₀, hσ₀, hD⟩ := ggReeLangAux_exists_S0_co C b'
  have hφ := reeLang_famSub_stable C b' b σ₀ hσ₀ u hM
  obtain ⟨σB, hσBπ, hzero⟩ := ggReeLangAux_famSub_sigmaB b σ₀ u hD hφ
  set S := C.Φ * C.Fr ^ b' with hS
  set Eq := realizedPointEquiv ReeTag.F4.tag L with hEq
  set x := Eq.symm u with hx
  set t : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L) :=
    (σ₀ : (realizedCoord ReeTag.F4.tag L) →ₐ[L] (realizedCoord ReeTag.F4.tag L)).comp (innerCo x)
    with htdef
  have ht : ∀ y : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L),
      Eq (toConv (y.ofConv.comp t)) = u * S (Eq y) * u⁻¹ := by
    intro y
    rw [htdef, point_comp_twist, map_mul, map_mul, map_inv, hσ₀, hx,
      MulEquiv.apply_symm_apply]
  set Fb := ggReeLangAux_famSub b with hFb
  set G' := Fb.map Eq.symm.toMonoidHom with hG'def
  have hG' : IsConnectedAlgebraicSubgroup L G' := ggReeLangAux_isConnected_famSub b
  have hmemG' : ∀ y : (realizedCoord ReeTag.F4.tag L) →ₐ[L] L,
      y ∈ subgroupPoints G' ↔ Eq (toConv y) ∈ Fb := by
    intro y
    change toConv y ∈ G' ↔ _
    rw [hG'def, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have := hG'.finiteType
  have := hG'.isReduced
  have := hG'.smooth.1
  have := hG'.connectedSpace
  set π := Ideal.Quotient.mkₐ L (subgroupIdeal G') with hπ
  intro c hc
  set eB := subgroupQuotientPointsEquiv G' hG'.pointsZero_eq with heB
  have hcG : Eq.symm c ∈ G' := Subgroup.mem_map_of_mem _ hc
  obtain ⟨h, hh⟩ := exceptional_Lang_connected_twisted_orbit_surjectivity σB (m := 2)
    (by norm_num) hzero (eB.symm ⟨_, hcG⟩)
  set w0 : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L) :=
    ((eB h : G') : WithConv ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L)) with hw0
  have hz' : w0.ofConv ∈ subgroupPoints G' := by
    change toConv _ ∈ G'
    rw [toConv_ofConv]
    exact (eB h).2
  have hzF := (hmemG' _).1 hz'
  rw [toConv_ofConv] at hzF
  refine ⟨Eq w0, hzF, ?_⟩
  have hpm : ((eB (pointMap σB h) : G') : WithConv
      ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L)) = toConv (w0.ofConv.comp t) := by
    apply WithConv.ext
    have e1 : ((eB (pointMap σB h) : G') : WithConv
        ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L)).ofConv =
        (pointMap σB h).ofConv.comp π := subgroupQuotientPointsEquiv_apply G' _ _
    have e2 : w0.ofConv = h.ofConv.comp π := subgroupQuotientPointsEquiv_apply G' _ _
    rw [e1, e2, ofConv_toConv, pointMap_apply, ofConv_toConv, ofConv_toConv]
    rw [AlgHom.comp_assoc]
    rw [show ((σB : (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G') →ₐ[L]
        (realizedCoord ReeTag.F4.tag L ⧸ subgroupIdeal G')).comp π) = π.comp t from
      AlgHom.ext fun a => hσBπ a]
    rw [AlgHom.comp_assoc]
  have h4 := congrArg (fun w => Eq ((eB w : G') : WithConv
    ((realizedCoord ReeTag.F4.tag L) →ₐ[L] L))) hh
  simp only [MulEquiv.apply_symm_apply, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_inv] at h4
  rw [h4, hpm, ht]

theorem exists_reeLang_famM {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ)
    (u : adjointGroup ReeTag.F4.tag L) {ι : Type} {a : ι → Fin ReeTag.F4.tag.rank → Lˣ}
    (hM : ∀ g ∈ famM a, u * ReeTag.F4.reeEndo L hf a₀ g * u⁻¹ ∈ famM a)
    {c : adjointGroup ReeTag.F4.tag L} (hc : c ∈ famM a) :
    ∃ z ∈ famM a, z⁻¹ * (u * ReeTag.F4.reeEndo L hf a₀ z * u⁻¹) = c := by
  obtain ⟨C, hC⟩ := exists_reeClosure_reeEndo (L := L) hf a₀
  have hM' : ∀ g ∈ ggReeLangAux_famSub a,
      u * (C.Φ * C.Fr ^ a₀) g * u⁻¹ ∈ ggReeLangAux_famSub a := by
    intro g hg
    have h := hM g hg
    rw [← hC g] at h
    exact h
  have h := reeLang_lang_famSub C a₀ a u hM' c hc
  simpa only [hC, famM] using h

end CFSG.HardMathSupport.C14Idx
