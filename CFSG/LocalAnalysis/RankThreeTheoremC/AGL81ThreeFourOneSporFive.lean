module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneSporBase
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HSFive
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.RuFive
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Aux
public import CFSG.RankThree.Native.HSMcLFiveData
public import CFSG.RankThree.Native.HSMcLSmallData
public import CFSG.RankThree.PartOne.KS.RuFiveData
public import CFSG.Sporadic.Schreier.RuDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.HardMathSupport.Dickson.I271 (hsFive_noSig ruFive_noSig autModel_center_eq_bot
  conj_injective_of_center_bot_sg)
open CFSG.LocalAnalysis.RankThreeTheoremC (exists_isElemAbelian_card_sq_of_card_cube)

open CFSG.RankThree.Native in
theorem signalizerThreeAt_hs :
    SignalizerThreeAt 5 (TauCeti.CFSGIndex.sporadic .HS).Group := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, hQcard, hQexp⟩, -⟩ := R3E_HS_full_five_centralizer_structures
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have hZ : Subgroup.center hs100P = ⊥ :=
    autModel_center_eq_bot CFSG.RankThree.PartOne.hs_autModel
  obtain ⟨E₀, -, hE₀, hE₀2⟩ := exists_isElemAbelian_card_sq_of_card_cube (X := hs100P) (p := 5)
    (E := hs100FiveQ.subgroupOf hs100P)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQcard]; norm_num)
    fun x hx => by
      have h := Monoid.pow_exponent_eq_one
        (⟨(x : Equiv.Perm (Fin 100)), Subgroup.mem_subgroupOf.1 hx⟩ : hs100FiveQ)
      rw [hQexp] at h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
  refine signalizerThreeAt_of_model_noSig Nat.prime_five (by norm_num)
    ⟨hs100Equiv.symm.trans b⟩ hE₀.isPGroup (hsFive_noSig _ (hE₀.map _) ?_)
  rw [Subgroup.card_map_of_injective (conj_injective_of_center_bot_sg hZ), hE₀2]

open CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier in
theorem signalizerThreeAt_ru :
    SignalizerThreeAt 5 (TauCeti.CFSGIndex.sporadic .Ru).Group := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, hQcard, hQexp⟩, -⟩ := R3E_Ru_full_five_centralizer_structures
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have hZ : Subgroup.center ruP = ⊥ := autModel_center_eq_bot ru_autModel
  obtain ⟨E₀, -, hE₀, hE₀2⟩ := exists_isElemAbelian_card_sq_of_card_cube (X := ruP) (p := 5)
    (E := ruFiveQ.subgroupOf ruP)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQcard]; norm_num)
    fun x hx => by
      have h := Monoid.pow_exponent_eq_one
        (⟨(x : Equiv.Perm (Fin 4060)), Subgroup.mem_subgroupOf.1 hx⟩ : ruFiveQ)
      rw [hQexp] at h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
  refine signalizerThreeAt_of_model_noSig Nat.prime_five (by norm_num)
    ⟨ruEquivP.symm.trans b⟩ hE₀.isPGroup (ruFive_noSig _ (hE₀.map _) ?_)
  rw [Subgroup.card_map_of_injective (conj_injective_of_center_bot_sg hZ), hE₀2]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
