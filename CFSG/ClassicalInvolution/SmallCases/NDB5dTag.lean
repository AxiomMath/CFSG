module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dLay
public import CFSG.ClassicalInvolution.SmallCases.NDB5dModel
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

namespace CFSG.ClassicalInvolution.NDB.WC

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
theorem fund_eq_top_of_A1 {Φ : Set (Subgroup G)} {a : G} (D : LocalLieSystemAt p f Φ a)
    (j : Fin D.card) (hj : D.tag j = .PSL ∧ D.rank j = 2) {R : Subgroup (compModel D j).K}
    (hR : R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D) : R = ⊤ := by
  have key : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), t = .PSL → n = 2 →
      StatedLieAdmissible t n p e →
      ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R = ⊤ := by
    intro t n e ht hn hadm R hR
    subst ht hn
    exact ModelFacts.fundamentalSubgroups_eq_top_PSL_two p e Fact.out hadm R hR
  exact key (D.tag j) (D.rank j) (D.exp j) hj.1 hj.2 (D.admissible j) R hR

theorem tag_of_sComponent_core {K : Subgroup G} {z : G} (hS : SettingCore p f K z)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G}
    (hax : PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂) {L₁ L₂ : Subgroup G}
    (hL₁ : IsVertexLayer p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ L₁)
    (hN : NormalizesLayer (S.sFamily (t₁ * t₂ * t₃) L₁ L₂) (t₁ * t₂ * t₃))
    (D : LocalLieSystemAt p f (S.sFamily (t₁ * t₂ * t₃) L₁ L₂) (t₁ * t₂ * t₃))
    (j₀ : Fin D.card) (R₁ R₂ : Subgroup (compModel D j₀).K)
    (hSC : S.SComponent (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (t₁ * t₂ * t₃) z₁ z₂ L₁ L₂ hN D j₀
      R₁ R₂) :
    (D.tag j₀ = .PSL ∧ D.rank j₀ = 3) ∨ (D.tag j₀ = .PSU ∧ D.rank j₀ = 3) ∨
      D.tag j₀ = .G2 ∨ D.tag j₀ = .trialityD4 := by
  by_cases hG2 : D.tag j₀ = .G2
  · exact Or.inr (Or.inr (Or.inl hG2))
  by_cases hD4 : D.tag j₀ = .trialityD4
  · exact Or.inr (Or.inr (Or.inr hD4))
  by_cases hA2 : D.tag j₀ = .PSL ∧ D.rank j₀ = 3
  · exact Or.inl hA2
  by_cases h2A2 : D.tag j₀ = .PSU ∧ D.rank j₀ = 3
  · exact Or.inr (Or.inl h2A2)
  exfalso
  set ψ := secComponentHom hN D j₀ with hψ
  have hA1 : ¬ (D.tag j₀ = .PSL ∧ D.rank j₀ = 2) := by
    intro h1
    apply hSC.ne
    rw [← hSC.img₁, ← hSC.img₂, fund_eq_top_of_A1 D j₀ h1 hSC.fund₁,
      fund_eq_top_of_A1 D j₀ h1 hSC.fund₂]
  have hq' : 5 ≤ p ^ D.exp j₀ := by
    rcases D.exp_eq j₀ with h1 | ⟨h1, -⟩
    · rw [h1]
      exact hS.five
    · exact absurd h1 hD4
  obtain ⟨S', hS', hSR, hc⟩ := exists_commuting_partner hS.odd hq' (D.isFundTag j₀)
    (D.admissible j₀) hA1 hA2 h2A2 hG2 hD4 hSC.fund₁
  obtain ⟨k, hk⟩ := ModelFacts.fundamentalSingleClass (D.tag j₀) (D.rank j₀) p (D.exp j₀)
    Fact.out (D.isFundTag j₀) (D.admissible j₀) hG2 hD4 R₁ hSC.fund₁ S' hS'
  obtain ⟨h, hhC, hhimg⟩ := hSC.conj₁ k
  have hkS : conjSub k R₁ = S' := hk.symm
  have hhimg' : S'.map ψ = modOdd (t₁ * t₂ * t₃) (conjSub h L₁) := by
    rw [← hkS]
    exact hhimg
  have hcomm : ∀ x ∈ modOdd (t₁ * t₂ * t₃) (conjSub h L₁), ∀ y ∈ modOdd (t₁ * t₂ * t₃) L₁,
      x * y = y * x := by
    rw [← hhimg', ← hSC.img₁]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc b hb a ha]
  have hwc := weak_closure_of_vertexLayer_core hS hax hL₁ hhC hcomm
  have h4 : 4 ≤ p ^ D.exp j₀ := by omega
  have hper : ∀ {R : Subgroup (compModel D j₀).K},
      R ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D → R ≤ ⁅R, R⁆ := fun hR =>
    ModelFacts.fundPerfect_core (D.tag j₀) (D.rank j₀) p (D.exp j₀) hS.odd (D.isFundTag j₀)
      (D.admissible j₀) h4 _ hR
  refine hSR (RouteD.eq_of_map_eq_of_perfect ψ hSC.ker (hper hS') (hper hSC.fund₁) ?_)
  rw [hhimg', hwc, hSC.img₁]

end CFSG.ClassicalInvolution.NDB.WC
