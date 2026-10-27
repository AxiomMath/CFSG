module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.Open.GLADefs
import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnExcLabel

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.StandardType (GGLabelRigidInput)

theorem canonLabel_eq_of_hasLabel (hRig : GGLabelRigidInput) {X : Type} [Group X]
    {lab lab' : GLALabel} (h : HasLabel X (fun l : GLALabel => l = lab))
    (h' : HasLabel X (fun l : GLALabel => l = lab')) : canonLabel lab = canonLabel lab' := by
  obtain ⟨hl, -, hg⟩ := Y10GInnLin.ggHasLabel_of_hasLabel h
  obtain ⟨hl', -, hg'⟩ := Y10GInnLin.ggHasLabel_of_hasLabel h'
  exact Y10GInnLin.canonLabel_eq_of_ggLabelIso
    (hRig lab lab' (X ⧸ Subgroup.center X) hl hl' hg hg')

theorem canon_n_dvd_of_glaPComponent_top (hRig : GGLabelRigidInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] {p : ℕ} {labK labJ : GLALabel} {J : Subgroup S}
    (hK : HasLabel S (fun l : GLALabel => l = labK))
    (hJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJp : GLAPComponent p (⊤ : Subgroup S) J) :
    (canonLabel labK).n ∣ (canonLabel labJ).n := by
  obtain ⟨-, hsn, -, -⟩ := id hJp
  have htop : J = ⊤ := by
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn
      (Subgroup.topEquiv.isSimpleGroup) with hbot | htop
    · exact absurd hbot (CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJp)
    · exact htop
  have e : ↥J ≃* S := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hJ' : HasLabel S (fun l : GLALabel => l = labJ) :=
    (hasLabel_congr e (fun l : GLALabel => l = labJ)).1 hJ
  rw [canonLabel_eq_of_hasLabel hRig hK hJ']

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnExcLabel

end
