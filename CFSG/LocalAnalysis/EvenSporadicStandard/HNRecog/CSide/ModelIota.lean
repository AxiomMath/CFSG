module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelV0
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog.Fpf

private theorem cSide_center_sl2_eq_bot :
    Subgroup.center SL2 = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Subgroup.mem_bot]
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    have key : ∀ x : F4, x ^ 2 = 1 → x = 1 := by decide
    exact key r hr2
  rw [hr1, map_one] at hAr
  exact Subtype.ext hAr.symm

private theorem cSide_isSimpleGroup_sl2 : IsSimpleGroup SL2 := by
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F4) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [F4.card_eq])
  let e : SL2 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F4 :=
    ((QuotientGroup.quotientMulEquivOfEq cSide_center_sl2_eq_bot).trans
      QuotientGroup.quotientBot).symm
  exact e.isSimpleGroup

private theorem cSide_card_sl2 : Nat.card SL2 = 60 := by
  have hq : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact F4.card_eq
  rw [Matrix.card_SL_field (𝔽 := F4) (n := 2), hq]
  norm_num [Fin.prod_univ_two]

theorem cSide_nonempty_mulEquiv_sl2 : Nonempty (A5 ≃* SL2) := by
  haveI := cSide_isSimpleGroup_sl2
  obtain ⟨e⟩ :=
    CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty cSide_card_sl2
  exact ⟨e.symm⟩

noncomputable def iota : A5 ≃* SL2 := Classical.choice cSide_nonempty_mulEquiv_sl2

noncomputable def sigma0 : A5 × A5 →* (V0 ≃ₗ[ZMod 2] V0) :=
  act0.comp (MonoidHom.prodMap (iota : A5 →* SL2) (iota : A5 →* SL2))

theorem sigma0_apply (g : A5 × A5) (M : V0) : sigma0 g M = actFun (iota g.1, iota g.2) M := by
  rw [sigma0, MonoidHom.comp_apply, MonoidHom.coe_prodMap, act0_apply]
  rfl

theorem q0_sigma0 (g : A5 × A5) (M : V0) : q0 (sigma0 g M) = q0 M := by
  rw [sigma0_apply]
  exact q0_act0 (iota g.1, iota g.2) M

end CFSG.EvenSporadicStandard.HNRecog.CSide
