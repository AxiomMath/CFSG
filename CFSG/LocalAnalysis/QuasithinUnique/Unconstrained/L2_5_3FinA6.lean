module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRad
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinF1
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8A6
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore
public import Certificates.Certificate4153
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.ClassicalGroups
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsNormal
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Unc25A6
  CFSG.QuasithinUnique.Unc25K1.A6Model

theorem a6_odd_check :
    Core.pslLit.all (fun x => x == Core.cid || Core.cpow x 45 != Core.cid ||
    Core.pslLit.all fun u => Core.cmul u x != Core.cmul x u || Core.cpow u 45 == Core.cid) =
      true :=
  Certificates.certificate4153

theorem x0_odd_field : ∀ x : X0, x ≠ 1 → Odd (orderOf x) → ∀ u : X0, u * x = x * u →
    Odd (orderOf u) := by
  intro x hx1 hxo u hux
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  have hcard : Nat.card X0 = 8 * 45 := by
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hx45 : x ^ 45 = 1 := by
    have hdvd : orderOf x ∣ 8 * 45 := hcard ▸ orderOf_dvd_natCard x
    have hcop : Nat.Coprime (orderOf x) 8 := by
      have := Nat.Coprime.pow_right 3 (Odd.coprime_two_right hxo)
      simpa using this
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hdvd)
  have hcx : Core.cpow (code (x : P10)) 45 = Core.cid := by
    rw [← code_pow_X0, hx45, code_one_X0]
  have hxne : code (x : P10) ≠ Core.cid := fun h =>
    hx1 (code_inj_X0 (by rw [h, code_one_X0]))
  have hcomm : Core.cmul (code (u : P10)) (code (x : P10)) =
      Core.cmul (code (x : P10)) (code (u : P10)) := by
    rw [← code_mul_X0, ← code_mul_X0, hux]
  have h := List.all_eq_true.mp a6_odd_check (code (x : P10)) (code_X0_mem x)
  have h1 : (Core.pslLit.all fun u => Core.cmul u (code (x : P10)) != Core.cmul (code (x : P10)) u ||
      Core.cpow u 45 == Core.cid) = true := by
    rcases Bool.or_eq_true_iff.mp h with ha | hc
    · rcases Bool.or_eq_true_iff.mp ha with ha | hb
      · exact absurd (beq_iff_eq.mp ha) hxne
      · exact absurd hcx (bne_iff_ne.mp hb)
    · exact hc
  have h2 := List.all_eq_true.mp h1 (code (u : P10)) (code_X0_mem u)
  have h3 : Core.cpow (code (u : P10)) 45 = Core.cid := by
    rcases Bool.or_eq_true_iff.mp h2 with hb | hb
    · exact absurd hcomm (bne_iff_ne.mp hb)
    · exact beq_iff_eq.mp hb
  have hu45 : u ^ 45 = 1 := code_inj_X0 (by rw [code_pow_X0, code_one_X0]; exact h3)
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hu45)

theorem a6RadicalCharTwo : A6RadicalCharTwo := by
  intro G _ _ K R ⟨e⟩ hRK hR2 hR hrad
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  let φ : ↥K ≃* X0 := e.trans ψ.symm
  refine charTwo_inf_normalizer_of_odd_cent_odd (fun x hx1 hxo u hux => ?_) hRK hR2 hR hrad
  have hφx : φ x ≠ 1 := fun h => hx1 (φ.injective (by rw [h, map_one]))
  have hφo : Odd (orderOf (φ x)) := by rwa [MulEquiv.orderOf_eq]
  have hφu : φ u * φ x = φ x * φ u := by rw [← map_mul, ← map_mul, hux]
  have := x0_odd_field (φ x) hφx hφo (φ u) hφu
  rwa [MulEquiv.orderOf_eq] at this

end CFSG.QuasithinUnique.Fin253
