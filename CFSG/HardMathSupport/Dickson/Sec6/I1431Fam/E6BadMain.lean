module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadLift
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTorus
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Mult
public import CFSG.LieType.Steinberg.CentralExt.E6E7Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits
  CFSG.RankThree.PerfectCover
  CFSG.HardMathSupport.Dickson.Sec6.I923

section


theorem y1431_noCfg_e6Bad : Y1431NoCfgAt FamE6Bad := by
  intro Y _ _ Â ξ J q hcfg t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨rfl, h3⟩ := hF
  have hn0 : n = 0 ∧ UntwistedChevalleyModel (Y ⧸ Subgroup.center Y) .E6 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact ⟨hn, hE.2⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨rfl, hU⟩ := hn0
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hX : LieModel ↥(adjointGroup Tag.E6 F) .E6 0 p f := LieModel.of_mulEquiv θ hm
  let π : Y →* adjointGroup Tag.E6 F :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = Subgroup.center Y := by
    ext y
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hperf : Group.IsPerfect ↥(e6Data_valid.minGroup F) := isPerfect_e6 F
  have hθker : (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F) :=
    le_antisymm (ker_le_center_of_isQuasisimple (isQuasisimple_e6 F) (e6Isogeny_ne_one F))
      (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.center_le_ker_of_surjective
        (e6Isogeny_surjective F) center_adjointGroup_eq_bot)
  have hcardker : Nat.card (e6Isogeny F).ker = Nat.gcd 3 (p ^ f - 1) := by
    rw [hθker, (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 F).1, hFcard]
  have hcardM : Nat.card (hopfMultiplier ↥(adjointGroup Tag.E6 F)) = Nat.gcd 3 (p ^ f - 1) :=
    card_hopfMultiplier_e6 hX
  have hgcd : Nat.gcd 3 (p ^ f - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  obtain ⟨ρ, hρ⟩ := exists_hom_lift_of_hopf_card (e6Isogeny F) (e6Isogeny_surjective F)
    (hθker ▸ le_rfl) (hcardM.trans hcardker.symm).le (hcardM ▸ hgcd) π hπ hπker.le
  have h3F : 3 ∣ Nat.card F - 1 := by rw [hFcard]; exact h3
  obtain ⟨E, U, hE, hcard, hU0, hU2, hN⟩ := e6_exists_torus_witness (F := F) h3F
  exact not_rkY_of_hom_lift π hπ hπker ρ (e6Isogeny F) hρ hE
    (le_trans (by norm_num) hcard) hU0 hU2 hN hcfg.rank

end

end CFSG.HardMathSupport.Dickson.Sec6.I1431
