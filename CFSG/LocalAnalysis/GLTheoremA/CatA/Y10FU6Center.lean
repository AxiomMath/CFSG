module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


theorem hasLabel_model {X : Type} [Group X] [Finite X] {lab : GLALabel}
    (h : HasLabel X (fun l : GLALabel => l = lab)) :
    1 ≤ lab.n ∧ CFSG.Open.IsQuasisimple X ∧
      CFSG.StandardType.MarkedModel lab (X ⧸ Subgroup.center X) := by
  obtain ⟨hcomm, lab', hlam, R, _, I, F, θ, hs, -, ⟨rfl, hm⟩⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists
      (CFSG.StandardType.Canonical.largeEvenMarking_markedModel h)
  haveI := hs
  exact ⟨hlam.1, ⟨hcomm, θ.isSimpleGroup⟩,
    CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm⟩

theorem u6Center_holds : U6Center := by
  intro L _ _ hL
  obtain ⟨hn1, hQ, hM⟩ := hasLabel_model hL
  have hm := i61_model_psu hM (lab := ⟨.twA, 5, 2⟩) rfl rfl
  obtain ⟨h3, h5⟩ := i61_card_center_dvd_psu hQ (n := 2) le_rfl hm
  have h1 : Nat.card (Subgroup.center L) ∣ 1 := by
    have := Nat.dvd_gcd h3 h5
    simpa using this
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 h1)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
