module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.U4Coords
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.U4Point
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.U4Line
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentLeft
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint

theorem forK_U4char2 :
    ForK (fun S _ => ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSU 4 2 f) := by
  intro K _ _ L V MK hK ⟨f, hf, hm⟩
  obtain ⟨-, hXs, -⟩ := hK.quasisimple
  refine hK.conclK_of_bar_psl2 fun L' V' MK' hc => ?_
  obtain ⟨F, hF, h, e, hpar⟩ := KConfig.exists_u4_coords hXs hm hc
  letI : Field F := hF
  have hc' : KConfig (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0) (L'.map e.toMonoidHom)
      (V'.map e.toMonoidHom) (MK'.map e.toMonoidHom) := hc.map_mulEquiv e
  rcases hpar with hpar | hpar
  ·
    rw [hpar] at hc'
    exact (KConfig.not_parP h hc').elim
  ·
    rw [hpar] at hc'
    obtain ⟨hleft, hpsl⟩ := KConfig.u4_line h hc'
    refine ⟨?_, 2 * f, ?_⟩
    ·
      have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
      refine conclKLeft_of_map e.toMonoidHom e.surjective (by rw [hker]; exact bot_le) ?_
        hc.elemAbelian hc.le_normalizer (by rw [hker, inf_bot_eq]) ?_
      · rw [hker, Subgroup.card_bot]
        exact odd_one
      · rw [hpar]
        exact hleft
    ·
      let eL : ↥L' ≃* ↥(L'.map e.toMonoidHom) :=
        Subgroup.equivMapOfInjective L' e.toMonoidHom e.injective
      let ψ : (↥L' ⧸ CFSG.pCore 2 ↥L') ≃*
          (↥(L'.map e.toMonoidHom) ⧸ CFSG.pCore 2 ↥(L'.map e.toMonoidHom)) :=
        QuotientGroup.congr _ _ eL (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eL)
      exact IsPSL.of_mulEquiv ψ.symm hpsl

theorem for_U4char2
    (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSU 4 2 f) :=
  For.of_forK h37 h38 h39 forK_U4char2

end CFSG.SectionRank.QTK.Insp443

end
