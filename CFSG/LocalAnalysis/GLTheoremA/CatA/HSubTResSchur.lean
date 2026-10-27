module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8F
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem torsBound_psp_four_two {r : ℕ} (hr : r.Prime) :
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound r StatedLieTag.PSp 4 2 1 = 1 := by
  have h1 : ¬ r ∣ 1 := fun h => hr.one_lt.ne' (Nat.dvd_one.mp h)
  simp [CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.torsBound,
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.tors, CFSG.Blueprint.Multiplier.genericOrders,
    CFSG.Blueprint.Multiplier.exceptionalOrders, h1]

theorem lieModel_statedSp_four_two :
    CFSG.Blueprint.LieModel (StatedSp 4 (ZMod 2)) StatedLieTag.PSp 4 2 1 := by
  have hsc : (StatedScalars (Fin 4 ⊕ Fin 4) (ZMod 2)).subgroupOf (StatedSp 4 (ZMod 2)) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf]
  let eP : StatedSp 4 (ZMod 2) ≃* StatedProj (StatedSp 4 (ZMod 2)) :=
    ((QuotientGroup.quotientMulEquivOfEq hsc).trans QuotientGroup.quotientBot).symm
  unfold CFSG.Blueprint.LieModel
  refine Or.inl ⟨by decide, ?_⟩
  unfold CFSG.Open.StatedClassicalModel
  refine ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, ?_⟩
  exact ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, ⟨eP⟩⟩

theorem schurSp8_holds
    : SchurSp8 := by
  intro J _ hJq hcat
  obtain ⟨eJ⟩ := sp8_model hcat
  have hCQ : CFSG.IsQuasisimple J :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr hJq
  haveI : Finite J := CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hCQ eJ
  have hm := lieModel_statedSp_four_two
  obtain ⟨-, ⟨eg⟩⟩ :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models (StatedSp 4 (ZMod 2))
      StatedLieTag.PSp 4 2 1 hm
  have hbound : ∀ r : ℕ, r.Prime → Nat.card {z : Subgroup.center J // z ^ r = 1} ≤ 1 := by
    intro r hr
    have h := CFSG.StandardType.center_torsion_le_native hJq.1 eJ hm ⟨eg⟩ hr
    rwa [torsBound_psp_four_two hr] at h
  by_contra hne
  have hnt : Nontrivial (Subgroup.center J) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hcard : Nat.card (Subgroup.center J) ≠ 1 := by
    have := Finite.one_lt_card (α := Subgroup.center J)
    omega
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center J) p hdvd
  have hxp : x ^ p = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hx1 : (x : J) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  haveI : Nontrivial {z : Subgroup.center J // z ^ p = 1} :=
    ⟨⟨⟨1, one_pow p⟩, ⟨x, hxp⟩, fun h => hx1 (congrArg (fun z => (z.1 : J)) h).symm⟩⟩
  have h2 := Finite.one_lt_card (α := {z : Subgroup.center J // z ^ p = 1})
  have h1 := hbound p hp
  omega

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
