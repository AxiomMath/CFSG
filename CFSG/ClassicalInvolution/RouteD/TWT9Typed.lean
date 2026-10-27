module

public import CFSG.ClassicalInvolution.RouteD.TWT9Spin
public import CFSG.ClassicalInvolution.RouteD.TWT8Bridge
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

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes)

set_option linter.unusedSectionVars false

section Group

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.TwinY

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem exists_chain_members_typed (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {u}) {t : StatedLieTag} {n : ℕ}
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hshape : LocalShapeT p f 0 t n Ω u)
    (hY : YData p f t n)
    (hF : OrthFacts (fundamentalSubgroups t (modelUniv t n p f Fact.out).D) (GaloisField p f))
    (hchain : ∀ {R₀ R₁ : Subgroup (modelUniv t n p f Fact.out).K},
      R₀ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D →
      R₁ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D →
      ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) R₀ R₁ →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) →
      ∃ T₁ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
        ∃ T₂ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
          Commutes T₁ R₀ ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ T₁) ∧
          Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧
          ∃ W, LinearBlockStandardPair (GaloisField p f) W T₁ T₂)
    {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember p f K z) (hs : IsClassicalMember p f β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) :
    ∃ J₁ ∈ centralizingMembers Ω {u}, ∃ N ∈ centralizingMembers Ω {u},
      Commutes K J₁ ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W β J₁) ∧
      Commutes K N ∧ Commutes β N ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W J₁ N) := by
  classical
  obtain ⟨e⟩ := Layer0.of_shape hΩ hex hG2 hD4 hshape
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) R₀ R₁ :=
    e.modelAdj hY hΩ hP1 hK hβ hR₀ hR₁ hKR hβR hz hs (ne_of_linearBlockStandardPair hW)
      (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hF hP1 hK hβ hR₀ hR₁ hKR hβR hW
  obtain ⟨T₁, hT₁, T₂, hT₂, c10, ⟨W₁, hW₁⟩, c20, c21, ⟨W₂, hW₂⟩⟩ := hchain hR₀ hR₁ hadjR ⟨W', hW'⟩
  obtain ⟨J₁, hJ₁, hJ₁T⟩ := e.comp T₁ hT₁
  obtain ⟨N, hN, hNT⟩ := e.comp T₂ hT₂
  refine ⟨J₁, hJ₁, N, hN, ?_, ?_, ?_, ?_, ?_⟩
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hJ₁ hK hT₁ hJ₁T hKR).mpr c10)
  · exact e.pair_of_model hq hΩ hP1 hβ hJ₁ hβR hJ₁T hW₁
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN hK hT₂ hNT hKR).mpr c20)
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN hβ hT₂ hNT hβR).mpr c21)
  · exact e.pair_of_model hq hΩ hP1 hJ₁ hN hJ₁T hNT hW₂

theorem twinYModel_minus_four_of_mod (h : p ^ f % 4 = 1) :
    twinYModel (p ^ f) .POmegaMinus 4 = (.POmegaMinus, 5) := by
  simp [twinYModel, h]

theorem twinYModel_minus_four_of_ne (h : ¬ p ^ f % 4 = 1) :
    twinYModel (p ^ f) .POmegaMinus 4 = (.POmegaPlus, 5) := by
  simp [twinYModel, h]

theorem exists_chain_members_td4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {u}) (h3 : p ^ f % 4 = 3)
    (hshape : LocalShapeT p f 0 (twinYModel (p ^ f) .POmegaMinus 4).1
      (twinYModel (p ^ f) .POmegaMinus 4).2 Ω u) {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember p f K z) (hs : IsClassicalMember p f β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) :
    ∃ J₁ ∈ centralizingMembers Ω {u}, ∃ N ∈ centralizingMembers Ω {u},
      Commutes K J₁ ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W β J₁) ∧
      Commutes K N ∧ Commutes β N ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W J₁ N) := by
  classical
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have : Invertible (2 : GaloisField p f) :=
    invertibleOfNonzero (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2)
  have h4 : ¬ p ^ f % 4 = 1 := by omega
  rw [twinYModel_minus_four_of_ne h4] at hshape
  have hadm : StatedLieAdmissible .POmegaPlus 5 p f := ⟨Fact.out, hf1, by norm_num⟩
  exact exists_chain_members_typed (t := .POmegaPlus) (n := 5) hp2 hq hΩ hex hP1 (by decide)
    (by decide) hshape (yData_plus (by norm_num) hadm (by omega))
    (orthFacts_plus (m := 5) hp2 (by norm_num) hq)
    (fun h0 h1 hadj hlin => exists_chain_spin_plus hp2 hq h0 h1 hadj hlin) hK hβ hz hs hKβ

end Group

end CFSG.ClassicalInvolution.RouteD.TWT9
