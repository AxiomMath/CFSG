module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigKlein
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinNonIso

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Assembly.LowTwoRank

theorem kleinSC_psl2
    (F : Type) [Field F] [Finite F]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F)) :
    KleinSC (CFSG.GorensteinWalter.PSL2 F) := by
  intro V hV4 hV2 g hg
  have hVK : IsKleinFour ↥V := CFSG.LinearGroups.isKleinFour_of_card_eq_four hV4
    (fun x => Subtype.ext (by simpa [sq] using hV2 x.1 x.2))
  have hC := CFSG.GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF V hVK
  rw [← hC]
  exact Subgroup.mem_centralizer_iff.mpr (fun h hh => (hg h hh).symm)

theorem kleinSC_of_psl2_17
    {X : Type} [Group X] (h : StatedClassicalModel X .PSL 2 17 1) :
    KleinSC X := by
  obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hFc : Nat.card F = 17 ^ 1 := hFcard
  let e' := e.trans
    (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 17 1 (by norm_num) hFc)
  have hcard : Nat.card (GaloisField 17 1) = 17 ^ 1 := GaloisField.card 17 1 (by norm_num)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 17 1)) :=
    ⟨17, 1, by norm_num, by decide, le_rfl, hcard⟩
  exact KleinSC.of_mulEquiv e' (kleinSC_psl2 (GaloisField 17 1) hodd)

theorem card_dvd_of_psl2_17 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 2 17 1) :
    16 ∣ Nat.card X := by
  obtain ⟨-, h2⟩ := CFSG.QuasithinUnique.Fin257.card_psl_two h
  have h17 : (17 : ℕ) ^ 3 = 4913 := by norm_num
  rw [h17] at h2
  omega

end CFSG.QuasithinUnique.DoubleA3
