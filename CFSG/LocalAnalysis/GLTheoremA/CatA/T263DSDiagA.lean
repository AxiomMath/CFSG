module

public import CFSG.HardMathSupport.Solomon.Coordinator.I2_5
public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

section Core

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def diagK (E J : Subgroup Y) : Subgroup Y := ⨆ e ∈ E, GLBConj e J

theorem t263_isComponentOf_gLBConj {J : Subgroup Y} (hJ : IsComponentOf J ⊤) (g : Y) :
    IsComponentOf (GLBConj g J) ⊤ :=
  i25_isComponentOf_gLBConj hJ (Subgroup.mem_normalizer_iff.2 fun h => by simp)

theorem t263_conj_le_diagK {E J : Subgroup Y} {e : Y} (he : e ∈ E) : GLBConj e J ≤ diagK E J :=
  le_biSup (fun e => GLBConj e J) he

theorem t263_conj_isComponentOf_diagK {E J : Subgroup Y} (hJ : IsComponentOf J ⊤) {e : Y} (he : e ∈ E) :
    IsComponentOf (GLBConj e J) (diagK E J) := by
  have hc := t263_isComponentOf_gLBConj hJ e
  exact ⟨t263_conj_le_diagK he, isSubnormal_of_le_of_le hc.2.1 (t263_conj_le_diagK he) le_top, hc.2.2⟩

theorem t263_gLBConj_conj {J : Subgroup Y} (g e : Y) : GLBConj g (GLBConj e J) = GLBConj (e * g) J :=
  gLBConj_gLBConj g e J

theorem t263_diagK_conj_le {E J : Subgroup Y} {g : Y} (hg : g ∈ E) : GLBConj g (diagK E J) ≤ diagK E J := by
  unfold diagK
  have h : GLBConj g (⨆ e ∈ E, GLBConj e J) = ⨆ e ∈ E, GLBConj g (GLBConj e J) := by
    unfold GLBConj
    simp only [Subgroup.map_iSup]
  rw [h]
  refine iSup₂_le fun e he => ?_
  rw [t263_gLBConj_conj]
  exact le_biSup (fun e => GLBConj e J) (E.mul_mem he hg)

theorem t263_mem_normalizer_diagK {E J : Subgroup Y} {g : Y} (hg : g ∈ E) :
    g ∈ Subgroup.normalizer (diagK E J : Set Y) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (t263_diagK_conj_le hg) ?_
  have h := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g (t263_diagK_conj_le (E := E) (J := J) (E.inv_mem hg))
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h

theorem t263_diagK_components {E J : Subgroup Y} (hJ : IsComponentOf J ⊤) {L : Subgroup Y}
    (hL : IsComponentOf L (diagK E J)) : ∃ e ∈ E, L = GLBConj e J := by
  by_contra hne
  push Not at hne
  have hcomm : ∀ e ∈ E, ∀ x ∈ L, ∀ y ∈ GLBConj e J, x * y = y * x := by
    intro e he x hx y hy
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hL (t263_conj_isComponentOf_diagK hJ he) with h | h
    · exact absurd h (hne e he)
    · exact h x hx y hy
  have hK : diagK E J ≤ Subgroup.centralizer (L : Set Y) := by
    refine iSup₂_le fun e he y hy => ?_
    exact Subgroup.mem_centralizer_iff.2 fun x hx => hcomm e he x hx y hy
  have hbot : ⁅L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hL.1.trans hK)
  rw [i25_commutator_eq hL.2.2] at hbot
  have := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 this hbot

theorem t263_layer_diagK {E J : Subgroup Y} (hJ : IsComponentOf J ⊤) :
    GLALayer (diagK E J) = diagK E J :=
  le_antisymm (i25_layer_le _)
    (iSup₂_le fun _ he => i25_le_layer (t263_conj_isComponentOf_diagK hJ he))

theorem t263_diagK_transitive {E J : Subgroup Y} (hJ : IsComponentOf J ⊤) :
    ∀ L L' : Subgroup Y, IsComponentOf L (diagK E J) → IsComponentOf L' (diagK E J) →
      ∃ e ∈ E, GLBConj e L = L' := by
  intro L L' hL hL'
  obtain ⟨a, ha, rfl⟩ := t263_diagK_components hJ hL
  obtain ⟨b, hb, rfl⟩ := t263_diagK_components hJ hL'
  refine ⟨a⁻¹ * b, E.mul_mem (E.inv_mem ha) hb, ?_⟩
  rw [t263_gLBConj_conj, mul_inv_cancel_left]

theorem t263_diagK_free {p : ℕ} {E J : Subgroup Y} (hE : IsElemAbelian p E) (hJ : IsComponentOf J ⊤)
    (hfree : ∀ e ∈ E, e ≠ 1 → GLBConj e J ≠ J) :
    ∀ e ∈ E, e ≠ 1 → ∀ L : Subgroup Y, IsComponentOf L (diagK E J) → GLBConj e L ≠ L := by
  intro e he he1 L hL h
  obtain ⟨a, ha, rfl⟩ := t263_diagK_components hJ hL
  apply hfree e he he1
  rw [t263_gLBConj_conj] at h
  have h2 := congrArg (GLBConj a⁻¹) h
  rw [gLBConj_gLBConj, gLBConj_inv_gLBConj, isElemAbelian_commute hE ha he, mul_inv_cancel_right] at h2
  exact h2

theorem t263_diagK_isSubnormal {E J : Subgroup Y} (hJ : IsComponentOf J ⊤) :
    IsSubnormal (diagK E J) ⊤ := by
  let 𝒮 : Set (Subgroup Y) := {A | ∃ e ∈ E, A = GLBConj e J}
  have hsn : ∀ A ∈ 𝒮, A.IsSubnormal := by
    rintro A ⟨e, -, rfl⟩
    exact CFSG.Open.IsSubnormal.top_iff.1 (t263_isComponentOf_gLBConj hJ e).2.1
  obtain ⟨h, -⟩ := CFSG.GroupTheory.subnormal_subgroups_generated_join 𝒮 hsn
  have heq : diagK E J = Subgroup.closure (⋃ A ∈ 𝒮, (A : Set Y)) := by
    apply le_antisymm
    · refine iSup₂_le fun e he y hy => ?_
      exact Subgroup.subset_closure (Set.mem_biUnion (x := GLBConj e J) ⟨e, he, rfl⟩ hy)
    · refine (Subgroup.closure_le _).2 (Set.iUnion₂_subset fun A hA => ?_)
      obtain ⟨e, he, rfl⟩ := hA
      exact t263_conj_le_diagK he
  rw [heq]
  exact CFSG.Open.IsSubnormal.of_mathlib h

theorem t263_diag_core {p : ℕ} {E J : Subgroup Y} (hE : IsElemAbelian p E) (hJ : IsComponentOf J ⊤)
    (hfree : ∀ e ∈ E, e ≠ 1 → GLBConj e J ≠ J) :
    ∃ d : ↥J →* Y,
      (∀ x : ↥J, d x ∈ diagK E J ∧ d x ∈ Subgroup.centralizer (E : Set Y) ∧
        (x : Y)⁻¹ * d x ∈ Subgroup.centralizer (J : Set Y)) ∧
      d.ker ≤ Subgroup.center ↥J ∧ CFSG.Open.IsQuasisimple ↥d.range ∧
      IsSubnormal d.range (Subgroup.centralizer (E : Set Y)) ∧
      GLALayer (diagK E J ⊓ Subgroup.centralizer (E : Set Y)) = d.range := by
  have hEN : E ≤ Subgroup.normalizer (diagK E J : Set Y) := fun g hg => t263_mem_normalizer_diagK hg
  have hfr := t263_diagK_free hE hJ hfree
  have hL := t263_layer_diagK (E := E) hJ
  have htr := t263_diagK_transitive (E := E) hJ
  have hX₁ : IsComponentOf J (diagK E J) := by
    have := t263_conj_isComponentOf_diagK hJ (E.one_mem : (1 : Y) ∈ E)
    rwa [gLBConj_one] at this
  obtain ⟨d, hd⟩ := i25_exists_diag hEN hfr hX₁
  have hlayer := i25_layer_eq_range hL htr hX₁ hd
  have hker : d.ker ≤ Subgroup.center ↥J := i25_ker_le_center fun x => (hd x).2.2
  have hq : CFSG.IsQuasisimple ↥J := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hX₁.2.2
  have hquasi : CFSG.Open.IsQuasisimple ↥d.range := by
    refine CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      (CFSG.LocalCores.isQuasisimple_of_surjective hq d.rangeRestrict d.rangeRestrict_surjective ?_)
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  refine ⟨d, hd, hker, hquasi, ?_, hlayer⟩
  set C := diagK E J ⊓ Subgroup.centralizer (E : Set Y) with hCdef
  have hdC : d.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(hd x).1, (hd x).2.1⟩
  have hdec : ∀ c ∈ C, ∃ x : ↥J, ∃ w ∈ (Subgroup.center ↥(diagK E J)).map (diagK E J).subtype,
      c = d x * w := by
    intro c hc
    obtain ⟨x, hw⟩ := i25_exists_mem_center hL htr hX₁ hd hc
    exact ⟨x, _, hw.1, by group⟩
  have hcent : ∀ w ∈ (Subgroup.center ↥(diagK E J)).map (diagK E J).subtype, ∀ g ∈ diagK E J,
      Commute w g := by
    rintro _ ⟨z, hz, rfl⟩ g hg
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)).symm
  have hnorm : IsSubnormal d.range C := by
    refine CFSG.Quasithin.A3.subnormal_of_normal hdC ?_
    rw [Subgroup.normal_subgroupOf_iff hdC]
    rintro _ c ⟨y, rfl⟩ hc
    obtain ⟨x, w, hw, rfl⟩ := hdec c hc
    refine ⟨x * y * x⁻¹, ?_⟩
    have h1 : Commute w (d y) := hcent w hw _ (hd y).1
    rw [map_mul, map_mul, map_inv]
    calc d x * d y * (d x)⁻¹ = d x * (w * d y) * w⁻¹ * (d x)⁻¹ := by rw [h1.eq]; group
      _ = d x * w * d y * (d x * w)⁻¹ := by group
  have hCsn : IsSubnormal C (Subgroup.centralizer (E : Set Y)) := by
    have := CFSG.Open.IsSubnormal.inf (t263_diagK_isSubnormal (E := E) hJ) (Subgroup.centralizer (E : Set Y))
    rwa [top_inf_eq] at this
  exact CFSG.Open.IsSubnormal.trans hnorm hCsn

end Core

end CFSG.LocalAnalysis.GLTheoremA.T263

end
