module

public import CFSG.ClassicalInvolution.RouteD.TWT4Model
public import CFSG.ClassicalInvolution.RouteD.TWZSu4Row
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

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Visible

variable {p f : ℕ} [Fact p.Prime]


theorem exists_visible_three (hmod : (p ^ f) % 4 = 3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {K T J : Subgroup G} {z t : G} (S : RouteDSetup p f K z)
    (e : TwinElt K T z) (A : AtT p f K T J z t .PSU 4) :
    ∃ M₁ M₂ : Subgroup G,
      M₁ ∈ centralizingMembers (𝒞 K) {e.u} ∧ M₂ ∈ centralizingMembers (𝒞 K) {e.u} ∧
      M₁ ∈ centralizingMembers (𝒞 K) {t} ∧ M₂ ∈ centralizingMembers (𝒞 K) {t} ∧
      M₁ ≠ J ∧ M₁ ≠ A.J₂ ∧ M₂ ≠ J ∧ M₂ ≠ A.J₂ ∧ M₁ ≠ M₂ ∧ Commutes M₁ M₂ ∧
      ∀ N ∈ centralizingMembers (𝒞 K) {e.u}, N ∈ centralizingMembers (𝒞 K) {t} → N ≠ J →
        N ≠ A.J₂ → N = M₁ ∨ N = M₂ := by
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts A e
  obtain ⟨S₁, S₂, hS₁, hS₂, hne, hcomm, hc₁, hc₂, huniq⟩ :=
    twinMF_two_psu4 S.odd S.five hmod A.hdat.toOn hãR hã'R hsq hsq'
  obtain ⟨M₁, hM₁t, hM₁S⟩ := mem_locFamily_iff.mp (A.d.mem_fam S₁ hS₁)
  obtain ⟨M₂, hM₂t, hM₂S⟩ := mem_locFamily_iff.mp (A.d.mem_fam S₂ hS₂)
  have hcen : ∀ (M : Subgroup G) (R : Subgroup (modelUniv .PSU 4 p f Fact.out).K),
      M ∈ centralizingMembers (𝒞 K) {t} → R ∈ fundamentalSubgroups .PSU
        (modelUniv .PSU 4 p f Fact.out).D → locImg (𝒞 K) t M = R.map A.d.ψ →
      (∀ s ∈ R, (ã * ã') * s = s * (ã * ã')) →
      M ∈ centralizingMembers (𝒞 K) {e.u} := by
    intro M R hMt hR hMR hcR
    refine ⟨hMt.1, ?_⟩
    refine (le_centralizer_iff_locImg S.inClass A.hP1 hMt ⟨e.u, huY⟩).mpr ?_
    have h2 : R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv .PSU 4 p f Fact.out).K) :=
      fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hcR s hs).symm
    have h3 := (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf R hR) (ã * ã')).mp h2
    rw [hMR, ← hψu]
    exact h3
  have hM₁u := hcen M₁ S₁ hM₁t hS₁ hM₁S hc₁
  have hM₂u := hcen M₂ S₂ hM₂t hS₂ hM₂S hc₂
  have hne' : ∀ (M : Subgroup G) (R : Subgroup (modelUniv .PSU 4 p f Fact.out).K),
      M ∈ centralizingMembers (𝒞 K) {t} → R ∈ fundamentalSubgroups .PSU
        (modelUniv .PSU 4 p f Fact.out).D → locImg (𝒞 K) t M = R.map A.d.ψ →
      M ≠ J ∧ M ≠ A.J₂ := by
    intro M R hMt hR hMR
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h] at hMt hMR
      exact not_fund_of_isolated S.inClass A.hP1 A.rf A.d hMt A.hJiso hR hMR
    · rw [h] at hMt hMR
      exact not_fund_of_isolated S.inClass A.hP1 A.rf A.d hMt A.hJ₂iso hR hMR
  obtain ⟨hM₁J, hM₁J₂⟩ := hne' M₁ S₁ hM₁t hS₁ hM₁S
  obtain ⟨hM₂J, hM₂J₂⟩ := hne' M₂ S₂ hM₂t hS₂ hM₂S
  have hcommM : Commutes M₁ M₂ :=
    (commutes_iff_fund S.inClass A.hP1 A.rf A.d hM₁t hM₂t hS₁ hM₁S hM₂S).mpr
      (fun a ha b hb => hcomm a ha b hb)
  have hMM : M₁ ≠ M₂ := by
    intro h
    rw [← h] at hcommM
    exact not_commutes_self_of_mem S.inClass hM₁t.1 hcommM
  refine ⟨M₁, M₂, hM₁u, hM₂u, hM₁t, hM₂t, hM₁J, hM₁J₂, hM₂J, hM₂J₂, hMM, hcommM, ?_⟩
  intro N hNu hNt hNJ hNJ₂
  obtain ⟨RN, hRN, hNR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
    A.hJiso A.hJ₂iso hNt hNJ hNJ₂
  have h1 : locImg (𝒞 K) t N ≤ Subgroup.centralizer ({locMk (𝒞 K) t ⟨e.u, huY⟩} : Set _) :=
    (le_centralizer_iff_locImg S.inClass A.hP1 hNt ⟨e.u, huY⟩).mp hNu.2
  have h2 : RN ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv .PSU 4 p f Fact.out).K) :=
    (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf RN hRN) (ã * ã')).mpr (by
      rw [hψu, ← hNR]
      exact h1)
  have h3 : ∀ s ∈ RN, (ã * ã') * s = s * (ã * ã') := fun s hs =>
    (Subgroup.mem_centralizer_singleton_iff.mp (h2 hs)).symm
  rcases huniq RN hRN h3 with rfl | rfl
  · exact Or.inl (locImg_injOn S.inClass A.hP1 hNt hM₁t (hNR.trans hM₁S.symm))
  · exact Or.inr (locImg_injOn S.inClass A.hP1 hNt hM₂t (hNR.trans hM₂S.symm))

end Visible

end CFSG.ClassicalInvolution.RouteD.TWT4
