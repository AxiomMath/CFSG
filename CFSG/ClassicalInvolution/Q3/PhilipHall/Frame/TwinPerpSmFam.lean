module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmPair
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallL5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallU5

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
  CFSG.Assembly.LowTwoRank CFSG.Blueprint


theorem leaf_g2Ne3 {n : ℕ} : TwinLeafS n SmallG2Ne3 :=
  TwinLeafS.of_no fun Y _ _ R S t h hsmall hF => by
    haveI := h.core.simple
    obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hF
    have hce := Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide)
      (by decide)
    exact false_of_outTwoCyclic_of_noTwinPair h (outTwoCyclic_G2 hp2 hce)
      (not_twinPair_of_twoCompShape (twoCompShape_g2 ⟨p, f, hp, hp2, hf, h3, hm⟩) hsmall)

theorem leaf_d4Ne3 {n : ℕ} : TwinLeafS n SmallD4Ne3 :=
  TwinLeafS.of_no fun Y _ _ R S t h hsmall hF => by
    haveI := h.core.simple
    obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hF
    have hce := Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide)
      (by decide)
    exact false_of_outTwoCyclic_of_noTwinPair h (outTwoCyclic_trialityD4 hp2 hce)
      (not_twinPair_of_twoCompShape (twoCompShape_d4 ⟨p, f, hp, hp2, hf, h3, hm⟩) hsmall)

theorem leaf_l5Ne3 {n : ℕ} : TwinLeafS n SmallL5Ne3 :=
  TwinLeafS.of_no fun Y _ _ R S t h hsmall hF => by
    haveI := h.core.simple
    obtain ⟨p, f, hp, hp2, hf, h4, h3, hm⟩ := hF
    obtain ⟨-, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
    exact false_of_outTwoCyclic_of_noTwinPair h (outTwoCyclic_PSL5 hp hf h4 hm)
      (not_twinPair_of_twoBlockShape (twoBlockShape_l5 hp hp2 h5 hm) hsmall)

theorem leaf_u5 {n : ℕ} : TwinLeafS n SmallU5 :=
  TwinLeafS.of_no fun Y _ _ R S t h hsmall hF => by
    haveI := h.core.simple
    obtain ⟨p, f, hp, hp2, hf, h4, hm⟩ := hF
    have hsm := Q5L5U5.statedClassicalModel_of_lieModel_psu hm
    have hg : Odd (Nat.gcd 5 (p ^ f + 1)) :=
      (by decide : Odd 5).of_dvd_nat (Nat.gcd_dvd_left 5 _)
    have h5 : 5 ≤ p ^ f := by
      have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      have := hp.two_le
      omega
    exact false_of_outTwoCyclic_of_noTwinPair h (outTwoCyclic_PSU hsm hg)
      (not_twinPair_of_twoBlockShape (twoBlockShape_u5 hp hp2 h5 hm) hsmall)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
