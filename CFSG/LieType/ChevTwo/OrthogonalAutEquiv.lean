module

public import CFSG.LieType.ChevTwo.OrthogonalAutSmall

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def isoGrpEquivOrthogonalGroup {Q : (ι → ZMod 2) → ZMod 2}
    {q : QuadraticForm (ZMod 2) (ι → ZMod 2)} (hq : ⇑q = Q) :
    isoGrp Q ≃* TauCeti.QuadraticMap.orthogonalGroup q :=
  (MulEquiv.subgroupCongr (isoGrp_eq_comap hq)).trans
    (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).subgroupMap _).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).surjective _)))

noncomputable def GoodQ.kappaEquiv {Q : (ι → ZMod 2) → ZMod 2} (hQ : GoodQ Q)
    (hind : OmegaTwoAutInduced Q) : isoGrp Q ≃* MulAut ↥(StatedOmega Q) :=
  MulEquiv.ofBijective (kappa Q) ⟨hQ.kappa_injective, fun α =>
    MonoidHom.mem_range.mp ((inducedByIso_iff_mem_range Q α).mp (hind α))⟩

theorem statedClassicalModel_statedOmega_quadMinus_three_two :
    StatedClassicalModel ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) .PSU 4 2 1 := by
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨E, _, h, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      hK hirr
  obtain ⟨hsimple, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (Or.inr rfl) hirr
  have : Finite E := h.finite
  have hE : Nat.card E = (2 ^ 1) ^ 2 := by rw [h.card_eq_sq]
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hcenter : Subgroup.center ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) = ⊥ := by
    have := hsimple
    exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun hc =>
      hna fun x y => hc.is_comm.comm x y
  have hscal : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    rw [← (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := 1) hE (by norm_num) hnq).2, ← Subgroup.map_center_eq eSU, hcenter,
      Subgroup.map_bot]
  exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, hnq⟩, E, inferInstance, this, hE,
    ⟨eSU.trans ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot).symm⟩⟩

theorem lieModel_statedOmega_quadMinus_three_two :
    CFSG.Blueprint.LieModel ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) .PSp 2 3 1 :=
  Or.inl ⟨by decide, CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two
    statedClassicalModel_statedOmega_quadMinus_three_two⟩

theorem nonempty_orthogonalGroup_quadMinus_three_two_equiv_mulAut :
    Nonempty (↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) 1 1)) ≃*
      MulAut ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1))) :=
  ⟨(isoGrpEquivOrthogonalGroup
      (CFSG.LieType.Universal.Spin.coe_quadMinus 3 (ZMod 2) 1 1)).symm.trans
    ((goodQ_minus (n := 2) (by norm_num)).kappaEquiv omegaTwoAutInduced_minus_two)⟩

end CFSG.LieType.ChevTwo
