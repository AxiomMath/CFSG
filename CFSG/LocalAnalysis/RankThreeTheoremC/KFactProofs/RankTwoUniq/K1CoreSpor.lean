module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreAlmost
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporRows3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporVacuous3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporDatum3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MonsterD2PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.ComponentClassification.OuterAutomorphisms

section M11


variable {X : Type} [Group X] [Finite X]

theorem k1Core_false_of_m11 {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K) (e : K ≃* (TauCeti.CFSGIndex.sporadic .M11).Group)
    (hRA : (R : Subgroup X) ≠ A) : False := by
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  let e' : K ≃* ↥CFSG.Blueprint.NativeSporadic.M11 := e.trans f.symm
  have hout : ¬ 3 ∣ Nat.card (Outer K) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    have h2 := (CFSG.Sporadic.Schreier.at_m11_schreier).1
    have : Finite (MulAut ↥CFSG.Blueprint.NativeSporadic.M11) := MulEquiv.finite_left
    have hpos : 0 < Nat.card (Outer ↥CFSG.Blueprint.NativeSporadic.M11) := Nat.card_pos
    intro h3
    have := Nat.le_of_dvd hpos h3
    omega
  exact hRA (k1Core_sylow_eq_of_le h.toD2Reduced (h.sylow_le_of_not_dvd_card_outer hout)
    (by rw [Nat.card_congr e'.toEquiv, CFSG.Sporadic.Schreier.m11_card]; norm_num))

end M11

section Sporadic


variable {X : Type} [Group X] [Finite X]

theorem k1Core_false_of_sporadic {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K) (s : TauCeti.SporadicName)
    (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hRA : (R : Subgroup X) ≠ A) : False := by
  have hvac : ∀ s' : TauCeti.SporadicName,
      s' ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) →
      (s', 3) ∉ d2SporadicOpenPairs3 → D2VacuousAt (.sporadic s') 3 :=
    fun s' hs' hp => d2SporadicVacuous3_of_certificates s' hs' 3 hp
  have hbig : ∀ s' : TauCeti.SporadicName,
      (∀ (L : Type) [Group L] [Finite L],
        Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.Carrier s') → D2IndexDatum L 3) →
      D2VacuousAt (.sporadic s') 3 := by
    intro s' hrow
    obtain ⟨f⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s'
    exact d2VacuousAt_of_datum fun L _ _ ⟨e⟩ => hrow L ⟨e.trans f.symm⟩
  cases s
  case M11 => exact k1Core_false_of_m11 h e hRA
  case J2 => exact d2VacuousAt_J2_three X R A X₀ K h ⟨e⟩
  case He => exact d2VacuousAt_He_three X R A X₀ K h ⟨e⟩
  case Ru => exact d2VacuousAt_Ru_three X R A X₀ K h ⟨e⟩
  case J4 => exact d2VacuousAt_J4_three X R A X₀ K h ⟨e⟩
  case Fi22 => exact hbig .Fi22 d2IndexDatum_Fi22_three X R A X₀ K h ⟨e⟩
  case Fi23 => exact hbig .Fi23 d2IndexDatum_Fi23_three X R A X₀ K h ⟨e⟩
  case Fi24Prime => exact hbig .Fi24Prime d2IndexDatum_Fi24Prime_three X R A X₀ K h ⟨e⟩
  case B => exact hbig .B d2IndexDatum_B_three X R A X₀ K h ⟨e⟩
  case M => exact d2FreeCaseAt_M_three_five X 3 (Or.inl rfl) R A X₀ K h ⟨e⟩
  all_goals exact hvac _ (by decide) (by decide) X R A X₀ K h ⟨e⟩

end Sporadic

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
