module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction
public import CFSG.Timmesfeld.RankTwo.SLThreeGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatalogueBHigherLinearField


private lemma slFieldAut_tv {F : Type} [Field F] {σ : F ≃+* F}
    {a b : Fin 3} (hab : a ≠ b) (c : F) :
    slFieldAut (Fin 3) F σ (CFSG.Timmesfeld.tv a b c) = CFSG.Timmesfeld.tv a b (σ c) := by
  apply Subtype.ext
  change (slFieldEquiv (Fin 3) σ (CFSG.Timmesfeld.tv a b c) : Matrix (Fin 3) (Fin 3) F) =
    (CFSG.Timmesfeld.tv a b (σ c) : Matrix (Fin 3) (Fin 3) F)
  rw [CFSG.Timmesfeld.tv_of_ne hab, CFSG.Timmesfeld.tv_of_ne hab]
  ext p q
  rw [slFieldEquiv_entry, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem twistHom_comp_eq_slFieldAut {F : Type} [Field F] (σ : F ≃+* F)
    {i j : Fin TwistTag.E6.tag.rank} (hi : TwistTag.E6.perm i = i) (hj : TwistTag.E6.perm j = j)
    (ι : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F)
    (hι : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c ∧
      ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    twistHom TwistTag.E6 F σ.toRingHom (ι g) = ι (slFieldAut (Fin 3) F σ g) := by
  let φ : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F :=
    (twistHom TwistTag.E6 F σ.toRingHom).comp ι
  let ψ : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F :=
    ι.comp (slFieldAut (Fin 3) F σ).toMonoidHom
  have hφψ : φ = ψ := by
    refine MonoidHom.eq_of_eqOn_dense (CFSG.Timmesfeld.closure_tv_three (F := F)) ?_
    intro g hg
    simp only [Set.mem_union, Set.mem_setOf_eq] at hg
    rcases hg with ((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩
    · dsimp only [φ, ψ]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [(hι c).1, twistHom_xUnit, hi, slFieldAut_tv (a := 0) (b := 1) (by decide) c,
        (hι (σ c)).1]
      rfl
    · dsimp only [φ, ψ]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [(hι c).2.1, twistHom_yUnit, hi, slFieldAut_tv (a := 1) (b := 0) (by decide) c,
        (hι (σ c)).2.1]
      rfl
    · dsimp only [φ, ψ]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [(hι c).2.2.1, twistHom_xUnit, hj, slFieldAut_tv (a := 1) (b := 2) (by decide) c,
        (hι (σ c)).2.2.1]
      rfl
    · dsimp only [φ, ψ]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [(hι c).2.2.2, twistHom_yUnit, hj, slFieldAut_tv (a := 2) (b := 1) (by decide) c,
        (hι (σ c)).2.2.2]
      rfl
  exact DFunLike.congr_fun hφψ g

end CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace
