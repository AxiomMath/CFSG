module

public import CFSG.ClassicalInvolution.RouteD.MultiModelConn
public import CFSG.ClassicalInvolution.RouteD.MultiModelConnC
public import CFSG.ClassicalInvolution.RouteD.MultiModelOrthStar
public import CFSG.ClassicalInvolution.RouteD.MultiModelOrthLayer
public import CFSG.ClassicalInvolution.RouteD.MultiModelLayer
public import CFSG.ClassicalInvolution.RouteD.MultiModelSp
public import CFSG.ClassicalInvolution.RouteD.MultiModelSL
public import CFSG.ClassicalInvolution.RouteD.MultiModelSU
public import CFSG.ClassicalInvolution.RouteD.MultiModelShortB
public import CFSG.ClassicalInvolution.RouteD.MultiModelShortMinus
public import CFSG.ClassicalInvolution.RouteD.MultiModelShortF4
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

@[expose] def ConnGeneric (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSL ∧ 5 ≤ n) ∨ (t = .PSU ∧ ((Even n ∧ 6 ≤ n) ∨ (¬ Even n ∧ 7 ≤ n))) ∨ (t = .PSp ∧ 3 ≤ n) ∨
    (t = .POmegaOdd ∧ 5 ≤ n) ∨ (t = .POmegaPlus ∧ 5 ≤ n) ∨ (t = .POmegaMinus ∧ 6 ≤ n) ∨
    t = .E6 ∨ t = .E7 ∨ t = .E8

@[expose] def ConnShort (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .POmegaOdd ∧ n = 4) ∨ (t = .POmegaMinus ∧ n = 5) ∨ t = .F4

@[expose] def ConnExotic (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSU ∧ n = 5) ∨ t = .twistedE6

section Models

variable {p : ℕ} [Fact p.Prime]

theorem commFamilyConnected_of_generic {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hg : ConnGeneric t n) :
    CommFamilyConnected (ModelFund p t n e) := by
  rcases hg with ⟨rfl, h⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl | rfl | rfl
  · exact commFamilyConnected_psl hp2 hadm h
  · exact commFamilyConnected_psu_even hp2 hadm h.1 h.2
  · exact commFamilyConnected_psu_odd hp2 hadm h.1 h.2
  · exact commFamilyConnected_psp hp2 hadm h
  · exact commFamilyConnected_pOmegaOdd hp2 hadm h
  · exact commFamilyConnected_pOmegaPlus hp2 hadm h
  · exact commFamilyConnected_pOmegaMinus hp2 hadm h
  · obtain rfl : n = 0 := hadm.2.2
    exact commFamilyConnected_E6 hp2 hadm
  · obtain rfl : n = 0 := hadm.2.2
    exact commFamilyConnected_E7 hp2 hadm
  · obtain rfl : n = 0 := hadm.2.2
    exact commFamilyConnected_E8 hp2 hadm

theorem commFamilyConnected_of_short {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hs : ConnShort t n) :
    CommFamilyConnected (ModelFund p t n e) := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
  · exact commFamilyConnected_pOmegaOdd_four hp2 hadm
  · exact commFamilyConnected_pOmegaMinus_five hp2 hadm
  · obtain rfl : n = 0 := hadm.2.2
    exact commFamilyConnected_F4 hp2 hadm

omit [Fact p.Prime] in
theorem small_model_cases {t : StatedLieTag} {n e : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hg : ¬ ConnGeneric t n) (hs : ¬ ConnShort t n) (hx : ¬ ConnExotic t n) :
    (t = .PSL ∧ n ≤ 4) ∨ (t = .PSU ∧ n ≤ 4) ∨ (t = .PSp ∧ n = 2) ∨ (t = .POmegaOdd ∧ n = 3) ∨
      (t = .POmegaPlus ∧ n = 4) ∨ (t = .POmegaMinus ∧ n = 4) := by
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine Or.inl ⟨rfl, ?_⟩
    by_contra h
    exact hg (Or.inl ⟨rfl, by omega⟩)
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    by_contra h
    by_cases h5 : n = 5
    · exact hx (Or.inl ⟨rfl, h5⟩)
    · by_cases he : Even n
      · exact hg (Or.inr (Or.inl ⟨rfl, Or.inl ⟨he, by omega⟩⟩))
      · exact hg (Or.inr (Or.inl ⟨rfl, Or.inr ⟨he, by
          obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp he
          omega⟩⟩))
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
    by_contra h
    exact hg (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
  case POmegaOdd =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))
    by_contra h
    by_cases h4 : n = 4
    · exact hs (Or.inl ⟨rfl, h4⟩)
    · exact hg (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))))
  case POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))))
    by_contra h
    exact hg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))))
  case POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))))
    by_contra h
    by_cases h5 : n = 5
    · exact hs (Or.inr (Or.inl ⟨rfl, h5⟩))
    · exact hg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))))))
  case G2 => exact absurd rfl hG2
  case F4 => exact absurd (Or.inr (Or.inr rfl)) hs
  case E6 => exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) hg
  case E7 =>
    exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) hg
  case E8 =>
    exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))) hg
  case twistedE6 => exact absurd (Or.inr rfl) hx
  case trialityD4 => exact absurd rfl hD4
  all_goals exact absurd hfund (by simp [IsFundTag])

@[expose] def ModelConnExotic (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), IsFundTag t → StatedLieAdmissible t n p e → p ≠ 2 →
    5 ≤ p ^ e → ConnExotic t n → CommFamilyConnected (ModelFund p t n e)

theorem modelConnFactNe_of_exotic (h : ModelConnExotic p) : ModelConnFactNe p := by
  intro t n e hfund hadm hp2 hq hG2 hD4 R hR R₁ hR₁ R₂ hR₂ hne h1 h2 h12
  by_cases hg : ConnGeneric t n
  · exact commFamilyConnected_of_generic hp2 hadm hg
  by_cases hs : ConnShort t n
  · exact commFamilyConnected_of_short hp2 hadm hs
  by_cases hx : ConnExotic t n
  · exact h t n e hfund hadm hp2 hq hx
  exfalso
  rcases small_model_cases hfund hadm hG2 hD4 hg hs hx with
    ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne (eq_of_commutes_commutes_psl_small hp2 hq hadm hn hR hR₁ hR₂ h1 h2)
  · exact hne (eq_of_commutes_commutes_psu_small hp2 hq hadm hn hR hR₁ hR₂ h1 h2)
  · exact hne (eq_of_commutes_commutes_psp_two hp2 hq hadm hR hR₁ hR₂ h1 h2)
  · rcases modelLayer_pOmegaOdd hp2 hq R hR R₁ hR₁ R₂ hR₂ h1 h2 with h | h
    · exact hne h
    · exact h12 h
  · rcases modelLayer_pOmegaPlus hp2 hq R hR R₁ hR₁ R₂ hR₂ h1 h2 with h | h
    · exact hne h
    · exact h12 h
  · rcases modelLayer_pOmegaMinus hp2 hq hadm R hR R₁ hR₁ R₂ hR₂ h1 h2 with h | h
    · exact hne h
    · exact h12 h

theorem modelStarFact : ModelStarFact p := by
  intro t n e hfund hadm hp2 hq hG2 hD4 R hR R₁ hR₁ R₂ hR₂ R_q hRq h1 h2 h12 hnl hq1 hq2 hq3
  have key : ∃ R_β ∈ ModelFund p t n e,
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R_β) := by
    by_cases hP : t = .POmegaPlus
    · subst hP
      exact modelStar_pOmegaPlus hp2 hq hadm.2.2 R hR R₁ hR₁ R₂ hR₂ h1 h2 h12 hnl
    by_cases hO : t = .POmegaOdd
    · subst hO
      exact modelStar_pOmegaOdd hp2 hq hadm.2.2.1 R hR R₁ hR₁ R₂ hR₂ h1 h2 h12 hnl
    by_cases hM : t = .POmegaMinus
    · subst hM
      exact modelStar_pOmegaMinus hp2 hq hadm R hR R₁ hR₁ R₂ hR₂ h1 h2 h12 hnl
    exfalso
    apply hnl
    by_cases hX : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6
    · exact linkedIn_modelFund_exceptional hp2 hq hX hadm hR hR₁ hR₂ h1.symm h2.symm
    have hcl : t = .PSL ∨ t = .PSU ∨ t = .PSp := by
      cases t <;> simp_all [IsFundTag]
    rcases hcl with rfl | rfl | rfl
    · exact linkedIn_modelFund_psl hp2 hq hadm hR hR₁ hR₂ h1 h2 h12
    · exact linkedIn_modelFund_psu hp2 hq hadm hR hR₁ hR₂ h1 h2 h12
    · exact linkedIn_modelFund_psp hp2 hq hadm hR hR₁ hR₂ h1 h2 h12
  obtain ⟨R_β, hRβ, a, b, c⟩ := key
  exact ⟨R_β, hRβ, R₁, hR₁, R₂, hR₂, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl,
    a, b, c⟩

theorem multiPiece_of_exotic {f : ℕ} (hconn : ModelConnExotic p) (hno : NoG2D4 p f) :
    MultiPiece p f :=
  multiPiece_of_modelFactsNe (modelConnFactNe_of_exotic hconn) modelStarFact hno

end Models

end CFSG.ClassicalInvolution.RouteD
