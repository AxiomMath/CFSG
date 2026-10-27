module

public import CFSG.ClassicalInvolution.Q3.TL3C7
public import CFSG.ClassicalInvolution.AschTight.S19B93

public section

namespace CFSG.ClassicalInvolution.Q3.TC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Graph

variable {G : Type} [Group G] [Finite G] {A : Subgroup G → Subgroup G → Prop}
variable {Ω : Set (Subgroup G)} (hF : GraphFam Ω A)
include hF

omit [Finite G] in
theorem maxAdj_conj {M N : Subgroup G} (h : MaxAdj A M N) (g : G) :
    MaxAdj A (conjSub g M) (conjSub g N) := by
  refine ⟨hF.graph.conj g h.1, ?_⟩
  rw [orbOf_conj hF.graph, maxOrbs_conj hF]
  exact ⟨_, h.2, rfl⟩

theorem exists_conj_maxAdj {M N M' N' : Subgroup G} (h : MaxAdj A M N) (h' : MaxAdj A M' N') :
    ∃ g : G, conjSub g M = M' ∧ conjSub g N = N' := by
  have hM : M ∈ Ω := hF.mem h.1
  have hM' : M' ∈ Ω := hF.mem h'.1
  obtain ⟨g₀, -, hg₀⟩ := hF.trans M hM M' hM'
  have h₀ := maxAdj_conj hF h g₀
  rw [hg₀] at h₀
  have heq : orbOf A M' (conjSub g₀ N) = orbOf A M' N' := maxOrb_unique hF hM' h₀.2 h'.2
  have hN' : N' ∈ orbOf A M' (conjSub g₀ N) := by rw [heq]; exact mem_orbOf_self M' N'
  obtain ⟨l, hl, hlN⟩ := hN'
  refine ⟨l * g₀, ?_, ?_⟩
  · rw [conjSub_mul, hg₀]
    exact conjSub_self_of_mem_nbrGen hF.graph hl
  · rw [conjSub_mul, hlN]

end Graph

section Tight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def TwoIn (z x : G) : Prop :=
  ∃ P : Subgroup G, IsNormalTwoIn P z ∧ x ∈ P

@[expose] def E2At (M N : Subgroup G) : Prop :=
  ∀ z u : G, IsUniqueInvolution M z → IsUniqueInvolution N u → TwoIn z u

@[expose] def ThinAt (Ω : Set (Subgroup G)) (M N : Subgroup G) : Prop :=
  E2At M N ∧ ∀ z : G, IsUniqueInvolution M z → ¬ UAt Ω z N

omit [Finite G] in
theorem IsNormalTwoIn.conj {P : Subgroup G} {z : G} (h : IsNormalTwoIn P z) (g : G) :
    IsNormalTwoIn (conjSub g P) (g * z * g⁻¹) := by
  obtain ⟨hPC, hP2, hPn⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * x := by group
  · exact hP2.map (MulAut.conj g).toMonoidHom
  · intro c hc p hp
    rw [mem_conjSub_iff] at hp ⊢
    have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      have h1 : c * (g * z * g⁻¹) = g * z * g⁻¹ * c := hc
      calc g⁻¹ * c * g * z = g⁻¹ * (c * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹ * c) * g := by rw [h1]
        _ = z * (g⁻¹ * c * g) := by group
    have h2 := hPn _ hc' _ hp
    have e : g⁻¹ * (c * p * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * p * g) * (g⁻¹ * c * g)⁻¹ := by
      group
    rw [e]
    exact h2

omit [Finite G] in
theorem TwoIn.conj {z x : G} (h : TwoIn z x) (g : G) : TwoIn (g * z * g⁻¹) (g * x * g⁻¹) := by
  obtain ⟨P, hP, hxP⟩ := h
  exact ⟨conjSub g P, hP.conj g, conj_mem_conjSub hxP⟩

omit [Finite G] in
theorem uAt_conj (hΩ : ConjInvariant Ω) {z : G} {N : Subgroup G} (h : UAt Ω z N) (g : G) :
    UAt Ω (g * z * g⁻¹) (conjSub g N) := by
  obtain ⟨U, hU, hUN, P, hP, hUP⟩ := h
  exact ⟨conjSub g U, S19B.conjSub_mem_USet hΩ hU g, conjSub_mono hUN, conjSub g P, hP.conj g,
    conjSub_mono hUP⟩

omit [Finite G] in
theorem e2At_conj {M N : Subgroup G} (h : E2At M N) (g : G) :
    E2At (conjSub g M) (conjSub g N) := by
  intro z u hz hu
  have hz' : IsUniqueInvolution M (g⁻¹ * z * g⁻¹⁻¹) := by
    have := hz.conj g⁻¹
    rwa [conjSub_inv_conjSub] at this
  have hu' : IsUniqueInvolution N (g⁻¹ * u * g⁻¹⁻¹) := by
    have := hu.conj g⁻¹
    rwa [conjSub_inv_conjSub] at this
  have h1 := (h _ _ hz' hu').conj g
  have e1 : g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ = z := by group
  have e2 : g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ = u := by group
  rwa [e1, e2] at h1

variable (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (hsep : SepHyp Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (htr : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hgen : (⨆ J ∈ Ω, J) = ⊤) (hconn : Disconnected.DConnected Ω)
include hΩ h2 hsep hK htr hgen hconn

omit hK in
theorem e2At_of_e2At {M₀ N₀ : Subgroup G} (h₀ : MaxAdj (nbrAdj Ω) M₀ N₀) (hE : E2At M₀ N₀)
    {M N : Subgroup G} (h : MaxAdj (nbrAdj Ω) M N) : E2At M N := by
  have hF := graphFam hΩ h2 hsep htr hgen hconn
  obtain ⟨g, rfl, rfl⟩ := exists_conj_maxAdj hF h₀ h
  exact e2At_conj hE g

omit hK in
theorem not_uAt_of_not_uAt {M₀ N₀ : Subgroup G} (h₀ : MaxAdj (nbrAdj Ω) M₀ N₀) {z₀ : G}
    (hz₀ : IsUniqueInvolution M₀ z₀) (hU₀ : ¬ UAt Ω z₀ N₀) {M N : Subgroup G}
    (h : MaxAdj (nbrAdj Ω) M N) {z : G} (hz : IsUniqueInvolution M z) : ¬ UAt Ω z N := by
  have hF := graphFam hΩ h2 hsep htr hgen hconn
  obtain ⟨g, rfl, rfl⟩ := exists_conj_maxAdj hF h h₀
  intro hU
  apply hU₀
  have h1 := uAt_conj hΩ.conjInvariant hU g
  have e := hz₀.eq (hz.conj g)
  rwa [← e] at h1

theorem inO2_or_not_uAt (hself : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → UAt Ω u L)
    {z : G} (hz : IsUniqueInvolution K z) :
    (∃ P : Subgroup G, P.Normal ∧ IsPGroup 2 P ∧ z ∈ P) ∨
      ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ∀ u : G, IsUniqueInvolution M u →
        ¬ UAt Ω u N := by
  by_cases hall : ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ∀ u : G,
      IsUniqueInvolution M u → UAt Ω u N
  · exact Or.inl (inO2_of_maxAdj hΩ h2 hsep hK htr hgen hconn hself hall hz)
  · push Not at hall
    obtain ⟨M₀, N₀, h₀, u₀, hu₀, hU₀⟩ := hall
    exact Or.inr fun M N h u hu =>
      not_uAt_of_not_uAt hΩ h2 hsep htr hgen hconn h₀ hu₀ hU₀ h hu

theorem inO2_or_thinAt (hself : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → UAt Ω u L)
    {M₀ N₀ : Subgroup G} (h₀ : MaxAdj (nbrAdj Ω) M₀ N₀) (hE : E2At M₀ N₀)
    {z : G} (hz : IsUniqueInvolution K z) :
    (∃ P : Subgroup G, P.Normal ∧ IsPGroup 2 P ∧ z ∈ P) ∨
      ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ThinAt Ω M N := by
  rcases inO2_or_not_uAt hΩ h2 hsep hK htr hgen hconn hself hz with h | h
  · exact Or.inl h
  · exact Or.inr fun M N hMN =>
      ⟨e2At_of_e2At hΩ h2 hsep htr hgen hconn h₀ hE hMN, fun u hu => h M N hMN u hu⟩

end Tight

end CFSG.ClassicalInvolution.Q3.TC
