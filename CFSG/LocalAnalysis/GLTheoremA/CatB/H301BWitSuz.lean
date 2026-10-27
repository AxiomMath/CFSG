module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430SuzHolds
public import CFSG.Sporadic.Bridge.SuzSurj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz


theorem witSuzCover_holds : CoverTwoRankAttained .Suz 4 := by
  intro H _ _ hcat hZ
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  haveI hNat : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Suz :=
    CFSG.Sporadic.Suz.isSimpleGroup_Suz
  haveI : IsSimpleGroup TauCeti.SporadicName.Suz.Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ hNat b.symm
  obtain ⟨eX⟩ := nonempty_mulEquiv_suzX
  let φ : H →* suzX := (e.trans eX).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hφ : Function.Surjective φ :=
    (e.trans eX).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center H := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hZe : IsElemAbelian 3 (Subgroup.center H) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a)⟩⟩, fun z hz => ?_⟩
    have h3 := pow_card_eq_one' (G := Subgroup.center H) (x := ⟨z, hz⟩)
    rw [hZ] at h3
    exact congrArg Subtype.val h3
  have hm : CFSG.Open.pRank 3 (Subgroup.center H) = 1 :=
    le_antisymm (CFSG.SectionRank.pRank_le (by norm_num) fun F hF _ => by
        rw [pow_one, ← hZ]
        exact Subgroup.card_le_of_le hF)
      (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hZe (by rw [hZ, pow_one]))
  obtain ⟨U, E, hU, hU2, hEN, hE, hEc⟩ := S8.L84.i1430TwoLocal_of_suzX φ hφ hker
  rw [hm] at hEc
  exact ⟨E, U, hE, hEc, hU, hU2, hEN⟩

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
