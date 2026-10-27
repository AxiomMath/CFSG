module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCyc
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.AUTSL.OddOutRee
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki
public import CFSG.LieType.SeitzGeneration.ExcVacuousTits
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.RankThree.PartOne.CTP.BabyRankFour

public section

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.OutStructure CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.PlaneCases
open CFSG.LieType.SeitzGeneration

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


private theorem outCycAt_cat_twistedE6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) :
    OutCycAt p (Cat ⟨.twistedE6 q, hv⟩) := by
  obtain ⟨K, hfield, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  letI : Field K := hfield
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hKq : Nat.card K = q.card ^ 2 := by
    rw [hK, TauCeti.PrimePower.card_def]
  have hσ' : ∀ c, σ c = c ^ q.card := by
    intro c
    rw [TauCeti.PrimePower.card_def]
    exact hσ c
  have hC : commutator (twistedE6RootGroup K σ) = ⊤ :=
    commutator_twistedE6RootGroup_eq_top q.prime_p q.exponent_pos hK σ hσ
  have hKf : Nat.card K = q.p ^ (2 * q.exponent) := by
    rw [hK, ← pow_mul, mul_comm]
  have hring := card_ringAut_and_isCyclic q.prime_p K hKf
  haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by
    rw [hring.1]
    exact Nat.mul_ne_zero (by norm_num) q.exponent_pos.ne')
  haveI : IsCyclic (RingAut K) := hring.2
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ hσ
  refine outCycAt_of_mulEquiv e.symm (outCycAt_of_cyclic hp (E := ⊤)
    (fun α _ => Subgroup.mem_top α)
    (Θ.comp (⊤ : Subgroup (MulAut (twistedE6RootGroup K σ))).subtype) ?_)
  intro x hx _
  have hxmem : (x : MulAut (twistedE6RootGroup K σ)) ∈ Θ.ker := hx
  rw [hker] at hxmem
  exact commutator_le_innAutDerived _ (twistedE6Inndiag_le_commutator σ hKq hσ' hC hxmem)

theorem lieOutCyc_excTwisted : LieOutCyc isExcTwistedIdx := by
  intro d p hp hp2 hchar hP
  obtain ⟨d, hd⟩ := d
  cases d with
  | twistedE6 q => exact outCycAt_cat_twistedE6 hd hp
  | suzuki m =>
    have hmodel : SuzukiModel (Cat ⟨.suzuki m, hd⟩) 2 (2 * m + 1) := suzukiModel_cat hd
    haveI : Finite (Cat ⟨.suzuki m, hd⟩) :=
      CFSG.LieType.Simplicity.fam_suzuki_finiteness _ 2 (2 * m + 1) hmodel
    exact outCycAt_of_outPChain hp (OutPNice.toChain (outPNice_Suzuki hp hmodel))
  | reeG2 m =>
    have hmodel : ReeTitsModel (Cat ⟨.reeG2 m, hd⟩) .twistedG2 3 (2 * m + 1) :=
      reeTitsModel_reeG2 m ⟨hd, ⟨MulEquiv.refl _⟩⟩
    haveI : Finite (Cat ⟨.reeG2 m, hd⟩) :=
      CFSG.LieType.Simplicity.fam_ree_tits_finiteness _ .twistedG2 3 (2 * m + 1) hmodel
    exact outCycAt_of_outPChain hp
      (OutPNice.toChain (CFSG.RankThree.PartOne.AUTSL.outPNice_twistedG2 hp hmodel))
  | reeF4 m =>
    have hmodel : ReeTitsModel (Cat ⟨.reeF4 m, hd⟩) .twistedF4 2 (2 * m + 1) :=
      reeTitsModel_cat_reeF4 hd
    haveI : Finite (Cat ⟨.reeF4 m, hd⟩) :=
      CFSG.LieType.Simplicity.fam_ree_tits_finiteness _ .twistedF4 2 (2 * m + 1) hmodel
    exact outCycAt_of_outPChain hp (OutPNice.toChain (outPNice_twistedF4 hp hmodel))
  | tits =>
    have hT := card_cat_tits_outer hd
    haveI : Finite (Cat ⟨.tits, hd⟩) := Nat.finite_of_card_ne_zero (by rw [hT.1]; norm_num)
    have hout : ¬ p ∣ Nat.card (Outer (Cat ⟨.tits, hd⟩)) := by
      rw [hT.2]
      exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    exact outCycAt_of_outPChain hp (OutPNice.toChain (outPNice_of_not_dvd_outer hp hout))
  | A n q => exact absurd hP (by simp [isExcTwistedIdx])
  | twistedA n q => exact absurd hP (by simp [isExcTwistedIdx])
  | B n q => exact absurd hP (by simp [isExcTwistedIdx])
  | C n q => exact absurd hP (by simp [isExcTwistedIdx])
  | D n q => exact absurd hP (by simp [isExcTwistedIdx])
  | twistedD n q => exact absurd hP (by simp [isExcTwistedIdx])
  | E6 q => exact absurd hP (by simp [isExcTwistedIdx])
  | E7 q => exact absurd hP (by simp [isExcTwistedIdx])
  | E8 q => exact absurd hP (by simp [isExcTwistedIdx])
  | F4 q => exact absurd hP (by simp [isExcTwistedIdx])
  | G2 q => exact absurd hP (by simp [isExcTwistedIdx])
  | trialityD4 q => exact absurd hP (by simp [isExcTwistedIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
