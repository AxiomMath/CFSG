module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpShape
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpExc
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrth
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwisted
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
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6TwinMain
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem te6PerpTableR_of_excLayer (hexc : ExcLayer p f) : TE6PerpTableR p f := by
  intro hp2 hq t n e he hfund hG2 hD4 hadm R₀ hR₀ k hkR hkc φ hφ h0
  subst he
  have hf : 1 ≤ e := hadm.2.1
  have hk : R₀ ≤ Subgroup.centralizer ({k} : Set _) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hkc r hr).symm
  have h0' : φ ⟨R₀, hR₀, hk⟩ = none := h0 _ rfl
  have hfund' : ModelFacts.IsFundTag t := by
    cases t <;> trivial
  have hfin : Finite (modelUniv t n p e Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out hfund' hadm
  have hcount : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} =
        te6Core (p ^ e) + 1 := by
    have h1 := te6Card_of_layer hR₀ hkR hk φ hφ h0'
    have h2 := card_te6Layer_eq hp2 hf (by omega : 2 ≤ p ^ e)
    omega
  have hnc : NoTE6Config (fundamentalSubgroups t (modelUniv t n p e Fact.out).D) → False :=
    fun hN => by
      obtain ⟨R₁, hP, hT⟩ := te6Shape_of_layer hp2 hf hR₀ hkR hk φ hφ h0'
      exact hN R₀ hR₀ R₁ hP hT
  cases t with
  | PSL => exact (hnc (noTE6Config_psl_model hp2 hadm)).elim
  | PSU => exact (hnc (noTE6Config_psu_model hp2 hadm)).elim
  | PSp => exact (hnc (noTE6Config_psp_model hp2 hadm)).elim
  | POmegaOdd => exact (te6_false_odd hp2 hq hadm hR₀ hcount).elim
  | POmegaPlus => exact (te6_false_plus hp2 hq hadm hR₀ hcount).elim
  | POmegaMinus => exact ⟨rfl, te6_eq_minus hp2 hq hadm hR₀ hcount⟩
  | G2 => exact absurd rfl hG2
  | F4 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (hexc hp2 hq .F4 n (Or.inl rfl) hadm))).elim
  | E6 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (hexc hp2 hq .E6 n (Or.inr (Or.inl rfl)) hadm))).elim
  | E7 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (hexc hp2 hq .E7 n (Or.inr (Or.inr (Or.inl rfl))) hadm))).elim
  | E8 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (hexc hp2 hq .E8 n (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm))).elim
  | twistedE6 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (hexc hp2 hq .twistedE6 n (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm))).elim
  | trialityD4 => exact absurd rfl hD4
  | twistedB2 => exact hfund.elim
  | twistedG2 => exact hfund.elim
  | twistedF4 => exact hfund.elim
  | Tits => exact hfund.elim

variable (p f) in
theorem te6PerpTableR : TE6PerpTableR p f :=
  te6PerpTableR_of_excLayer excLayer

section Consumer

variable [Finite G]

theorem routeD_typeU_five_of_adaptation (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hMFZ : Gaps.FundNoncentral p)
    (hIH : LocalLieSystems p f Ω)
    (hP1x : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) → LocalOddCentral Ω {z * nd.w 0})
    (hexc : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) →
      ∀ D : LieSystemData p f (locQuot Ω (z * nd.w 0)) (locFamily Ω (z * nd.w 0)),
        ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    (hAdapt : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) → TE6Adaptation hadm.2.1 nd) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 :=
  routeD_typeU_five_of_nonclassical_r hp2 hadm hq hΩ hex hK hsingle hconn hz hshape hP1 hMFZ hIH
    hP1x hexc (te6PerpTableR p f) hAdapt

end Consumer

end CFSG.ClassicalInvolution.RouteD.NonClassical
