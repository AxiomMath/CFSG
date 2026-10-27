module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2324Q
import CFSG.LieType.SeitzGeneration.Hyper

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem genAut_of_forall_genPlane {S X : Type} [Group S] [Group X] [Finite S] [Finite X]
    (f : S ≃* X) (hcen : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))
    (hK : ∀ P : Subgroup X, CFSG.Open.IsElemAbelian 3 P → Nat.card P = 9 →
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q.GenPlane P)
    {E : Subgroup (MulAut S)} (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q.GenAut E := by
  have hinj := CFSG.RankThree.PartTwo.Sec4.Item434Kit.conj_injective_of_center_eq_bot hcen
  have hEinn : ∀ φ ∈ E, φ ∈ (MulAut.conj : S →* MulAut S).range := fun φ hφ =>
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.mem_range_conj_of_pow_three hout (hE.2 φ hφ)
  set PS : Subgroup S := E.comap (MulAut.conj : S →* MulAut S) with hPS
  have hPSE : PS.map (MulAut.conj : S →* MulAut S) = E := by
    rw [hPS, Subgroup.map_comap_eq]
    exact inf_eq_right.2 fun φ hφ => hEinn φ hφ
  have hPSel : IsElemAbelian 3 PS :=
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.isElemAbelian_of_map_injective hinj (hPSE ▸ hE)
  have hPScard : Nat.card PS = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hPSE]
    exact hE9
  set PX : Subgroup X := PS.map f.toMonoidHom with hPX
  have hPXel : IsElemAbelian 3 PX := CFSG.Open.IsElemAbelian.map hPSel _
  have hPXcard : Nat.card PX = 9 := by
    rw [hPX, Subgroup.card_map_of_injective f.injective]
    exact hPScard
  rw [← hPSE]
  exact genAut_of_genPlane hcen (GenPlane.of_map f (hK PX hPXel hPXcard))

theorem seitzHyperGamma_eq_top_of_top_le_iSup_fixSub {Y : Type} [Group Y]
    {A : Subgroup (MulAut Y)} (hA9 : Nat.card A = 3 ^ 2)
    (h : (⊤ : Subgroup Y) ≤ ⨆ (α : MulAut Y) (_ : α ∈ A) (_ : α ≠ 1),
      CFSG.Open.GLAPPrimeCoreOf 3 (CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub α)) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 A = ⊤ := by
  have htop : (⊤ : Subgroup Y) ≤ CFSG.LieType.SeitzGeneration.planeClosure A := by
    refine h.trans (iSup_le fun α => iSup_le fun hα => iSup_le fun hα1 =>
      (CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub α)).trans ?_)
    intro y hy
    exact CFSG.LieType.SeitzGeneration.mem_planeClosure_of_fixed hα hα1 hy
  have hgen : CFSG.LieType.SeitzGeneration.PlaneGen A := top_le_iff.mp htop
  exact (CFSG.LieType.SeitzGeneration.planeGen_iff_seitzHyperGamma Nat.prime_three hA9).mp hgen

theorem seitzHyperGamma_eq_top_of_m22
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hZ : IsPGroup 3 ↥(Subgroup.center Y))
    (e₀ : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.sporadic .M22).Group)
    {A : Subgroup (MulAut Y)} (hA : CFSG.Open.IsElemAbelian 3 A) (hA9 : Nat.card A = 3 ^ 2) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 A = ⊤ := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  let f : (Y ⧸ Subgroup.center Y) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e₀.trans b.symm
  have hout : ¬ 3 ∣ Nat.card (Outer (Y ⧸ Subgroup.center Y)) := by
    have hle : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := by
      rw [Nat.card_congr (equivalence f).toEquiv]
      exact CFSG.RankThree.PartTwo.Sec4.card_outer_le_two_of_card_mulAut_le
        CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card
    intro hd
    have hpos : 0 < Nat.card (Outer (Y ⧸ Subgroup.center Y)) := Nat.card_pos
    have := Nat.le_of_dvd hpos hd
    omega
  have hφ := quotientCenterAut'_injective hq.1
  have hĀel : IsElemAbelian 3 (A.map (quotientCenterAut' Y)) :=
    CFSG.Open.IsElemAbelian.map hA _
  have hĀ9 : Nat.card (A.map (quotientCenterAut' Y)) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hφ, hA9]
  have hg : GenAut (A.map (quotientCenterAut' Y)) :=
    genAut_of_forall_genPlane f (center_quot_eq_bot hq) hout
      (fun P hP hP9 => kill_m22 P hP hP9) hĀel hĀ9
  exact seitzHyperGamma_eq_top_of_top_le_iSup_fixSub hA9 (top_le_of_genAut hq.1 hZ hg)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central
