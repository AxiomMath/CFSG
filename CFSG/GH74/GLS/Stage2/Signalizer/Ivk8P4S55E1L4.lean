module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Ln
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1BT
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Types

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG CFSG.LocalAnalysis.ComponentInitial

theorem e1_l4 : E1Type FL4d := by
  intro r Y _ _ hr hr2 hF b hb1 hbr hHH E hE hinv
  obtain ⟨f, hf, -, hL⟩ := hF
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : CharP F r := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hBT : LieType.BorelTits.Holds Y r := holds_of_lieModel hL (by decide)
  have hBT' : LieType.BorelTits.Holds (LinearFlag.projectiveSL 4 F) r :=
    LieType.BorelTits.Holds.of_mulEquiv e hBT
  exact E1Core.of_mulEquiv e (e1Core_projectiveSL (by norm_num) hBT') b hb1 hbr hHH E hE hinv

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
