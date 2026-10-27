module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AExtShape
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AExtU33
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AExtRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AExtDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InnRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416ROdd
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
import CFSG.Adapters.LieModelSimple
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.T173

section Reduction


theorem ext_quot_model {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} {S : Subgroup Ω}
    (hqs : CFSG.Open.IsQuasisimple ↥S) {t : StatedLieTag} {n q f : ℕ}
    (h : StatedClassicalModel (PSimple p S) t n q f) :
    StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) t n q f := by
  haveI : Nontrivial (PSimple p S) :=
    (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h).toNontrivial
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter p S hqs
    inferInstance
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem t173AExtract_of_inputs (hRig : CFSG.StandardType.GGLabelRigidInput)
    (hb : CatDistinct.OrderBridge) (hOdd : Chev2OddAmb) (hInn : Rk2InnRank) : T173AExtract := by
  intro p Ω _ _ S B N D K x hcfg hcat
  have hp := hcfg.prime
  have hp2 := hcfg.odd
  have hqs := hcfg.qs
  have hmark := ext_split_rank hInn hp hp2 hcfg.elem hcfg.four hcfg.mem hcfg.ne_one hcfg.cent
    hcfg.split
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R0, _, I0, F0, hs0, hna0, θ0, hrank, hrest0⟩ := rk2_rawDatum_exists hraw
  have hHasLab : CFSG.StandardType.GGHasLabel lab (↥S ⧸ Subgroup.center ↥S) := by
    unfold CFSG.StandardType.GGHasLabel
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hraw' : GLARawDatum lab fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥S ⧸ Subgroup.center ↥S ≃* R, GLASplit16 p lab ∧
        B ≤ Subgroup.normalizer (S : Set Ω) ∧
        ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' : ↥S => (l' : Ω) = b⁻¹ * l * b) φ :=
    rk2_rawDatum_mono (fun R _ I F ⟨hs, hna, θ, _, hrest⟩ => ⟨hs, hna, θ, hrest⟩) hraw
  rcases ext_shape hb hOdd hcfg.chev hcat with ⟨r, f, hM⟩ | ⟨r, f, hM⟩ | hM
  ·
    have hMZ := ext_quot_model hqs hM
    have hiso := hRig lab ⟨.A, r, f⟩ _ hlab (CFSG.StandardType.largeEvenInLambda2_typeA hMZ) hHasLab
      (CFSG.StandardType.ggHasLabel_typeA hMZ)
    exact Or.inl (ext_lin_data hlab (ext_tag_of_iso_A hiso) hraw')
  ·
    have hMZ := ext_quot_model hqs hM
    obtain ⟨⟨-, hf, hr, hne⟩, E, hEF, hEfin, hE, ⟨e⟩⟩ := hMZ
    have hTl : LargeEvenInLambda2 ⟨.twA, r, f⟩ := by
      refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA hf (by omega) ?_
      intro hr2
      have hn1 : f ≠ 1 := by
        intro hn
        exact hne (by simp [hr2, hn])
      omega
    have hiso := hRig lab ⟨.twA, r, f⟩ _ hlab hTl hHasLab
      (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA hE e)
    exact Or.inr (ext_uni_data hlab (ext_tag_of_iso_twA hiso) hrank hraw')
  ·
    exfalso
    haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hqs.2
    have hMZ := ext_quot_model hqs hM
    have hiso := hRig lab ⟨.G2der, 0, 1⟩ _ hlab ⟨le_rfl, rfl, rfl⟩ hHasLab (ext_u33_label hperf hMZ)
    have hlab_eq := ext_label_of_iso_g2der hiso
    subst hlab_eq
    have h2 : rk2Mult (⟨.G2der, 0, 1⟩ : GLALabel) (rk2Ord p 1) ≤ 2 :=
      rk2Mult_le_two_of_small (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        (rk2Ord_pos hp hp2 1)
    have h3 : 3 ≤ rk2Mult (⟨.G2der, 0, 1⟩ : GLALabel) (rk2Ord p 1) := hrank
    omega

end Reduction

theorem t173AExtract_holds :
    T173AExtract :=
  t173AExtract_of_inputs CFSG.StandardType.ggLabelRigidInput_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds chev2OddAmb_holds
    (rk2InnRank_of_kRank rk2KRank)

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
