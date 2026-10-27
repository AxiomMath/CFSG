module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD.Main
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCent
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

theorem fixThreeVoid_d_residual (hGA : CFSG.Open.GriessAllModelsStatement) :
    FixThreeVoid (IsLieOf IdxDResidual) := by
  intro Y _ _ L J u h hX
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hX
  have hq : CFSG.Open.IsQuasisimple ↥L := h.parab.comp.2.2
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  cases d with
  | D r q =>
    obtain ⟨hp2, hq2, hr⟩ := hPd
    have hZ : Nat.card (Subgroup.center ↥L) = 1 := by
      obtain ⟨hd, hA, h2A⟩ := ToralCensus.rest_index (P := IdxD) (Or.inr (Or.inl rfl))
        (show IdxD (.D r q) from hp2)
      exact ToralCensus.card_center_eq_one_of_index hGA ⟨.D r q, hv⟩ hd hA h2A e h.parab.odd
    obtain ⟨u', hbar⟩ := exists_fixBarFull_of_fixThreeHyp h hZ
    have hexp : q.exponent = 1 := by
      have hpos := q.exponent_pos
      by_contra hne
      have h2 : 2 ≤ q.exponent := by omega
      have : 2 ^ 2 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
      rw [TauCeti.PrimePower.card_def, hp2] at hq2
      omega
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp2 e
    rw [hp2, hexp] at hm
    obtain ⟨⟨-, -, hr4⟩, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hm
    have := Fintype.ofFinite F
    have hcardF : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
    let φ : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hcardF).symm
    let ee : (↥L ⧸ Subgroup.center ↥L) ≃*
        CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedOmega
          (CFSG.Assembly.LowTwoRank.StatedQuadPlus r (ZMod 2))) :=
      e'.trans (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
          (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.statedQuadPlus_comp φ r))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ))
    exact ResidualD.false_of_fixBarFull_omegaPlus hr4 (by omega) ee hbar
  | _ => exact hPd.elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
