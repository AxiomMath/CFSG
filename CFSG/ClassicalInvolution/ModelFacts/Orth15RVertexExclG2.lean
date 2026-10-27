module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RG2Pair
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RVertexExcl

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.G2D4Models
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore)
open scoped commutatorElement MatrixGroups

section Vertex

variable {p f : ℕ} [Fact p.Prime]

theorem false_of_g2_twin_sec (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hAsec : ∀ K ∈ secFam Ω c, AEmpty (secFam Ω c) K)
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card) (hG2 : D.tag j = .G2)
    {M M' : Subgroup G} {b : G} (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hM'j : modOdd c (exactCore c M') ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range) : False := by
  have hs' : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hM⟩
  obtain ⟨R, R', z, hR, hR', hKR, hK'R', hzKR, hzK'R', hneR⟩ :=
    twin_pair_in_sec hp hq hΩ hc2 D j hM hM' hMb hM'b hne hMj hM'j
  exact false_of_twin_g2 hp hq (hypOmega_secFam hp hq hΩ hc2 hs' D) hAsec
    (LieSystemData.toOmegaLie D (omegaGen_secFam hs')) (i := j) hG2 hR hR' hKR hK'R' hzKR hzK'R'
    hneR

@[expose] def SecAEmpty (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ M ∈ Ω, AEmpty Ω M) → ∀ c : G, IsPGroup 2 (Subgroup.zpowers c) →
        (tqMembers Ω c).Nonempty → ∀ K ∈ secFam Ω c, AEmpty (secFam Ω c) K

theorem g2VertexExcl_of_secAEmpty (h : SecAEmpty p f) : G2VertexExcl p f := by
  intro hp hq G _ _ Ω hΩ hA c hc2 D j hG2 M M' b hM hM' hMb hM'b hne hMj hM'j
  exact false_of_g2_twin_sec hp hq hΩ hc2 (h hp hq G Ω hΩ hA c hc2 ⟨M, hM⟩) D j hG2 hM hM' hMb
    hM'b hne hMj hM'j

end Vertex

section Centralizing

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem restrictFamily_centralizing_eq (hΩ : HypOmegaMod p f Ω)
    (hcent : ∀ M ∈ tqMembers Ω c, M ≤ Subgroup.centralizer ({c} : Set G)) :
    restrictFamily (centralizingMembers (exactFamily Ω c) {c})
        (centralizingLayer (exactFamily Ω c) {c}) =
      restrictFamily Ω (centralizingLayer (exactFamily Ω c) {c}) := by
  have hperf : ∀ M ∈ Ω, Group.IsPerfect ↥M := fun M hM => by
    obtain ⟨z, hz⟩ := hΩ.classical M hM
    exact hz.perfect
  ext L'
  constructor
  · rintro ⟨L, ⟨⟨M, hM, rfl⟩, hLc⟩, hLY, rfl⟩
    have hMeq : exactCore c M = M := exactCore_eq_self (hperf M hM.1) (hcent M hM)
    rw [show triangleResidual M c = M from hMeq] at hLY ⊢
    exact ⟨M, hM.1, hLY, rfl⟩
  · rintro ⟨L, hL, hLY, rfl⟩
    have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
      hLY.trans (exactLayer_le_centralizer Ω c)
    have hLtq : L ∈ tqMembers Ω c := ⟨hL, mem_trivialOnQuot_of_le_centralizer hLc⟩
    have hLe : L ∈ exactFamily Ω c := ⟨L, hLtq, (exactCore_eq_self (hperf L hL) hLc).symm⟩
    exact ⟨L, ⟨hLe, hLc⟩, hLY, rfl⟩

theorem aEmpty_secFam_of_centralizing (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hcent : ∀ M ∈ tqMembers Ω c, M ≤ Subgroup.centralizer ({c} : Set G))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) : ∀ K ∈ secFam Ω c, AEmpty (secFam Ω c) K := by
  set Y := centralizingLayer (exactFamily Ω c) {c} with hY
  have hΛ : HypOmegaMod p f (restrictFamily Ω Y) := hΩ.restrict Y
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ' : HypOmegaMod p f
      (quotFamily (restrictFamily Ω Y) (classicalInvolutionOddCore ↥Y)) :=
    oddQuotHyp p f hp hq ↥Y _ hΛ _ hN
  have hAY : ∀ J ∈ restrictFamily Ω Y, AEmpty (restrictFamily Ω Y) J := by
    rintro _ ⟨K, hK, hKY, rfl⟩
    exact AEmpty.restrict hp hΩ hKY (hA K hK)
  have hfam : secFam Ω c =
      quotFamily (restrictFamily Ω Y) (classicalInvolutionOddCore ↥Y) := by
    unfold secFam oddQuotientFamily quotFamily
    rw [restrictFamily_centralizing_eq hΩ hcent]
  rw [hfam]
  exact aEmpty_quotFamily hp hq hΛ hΛ' hN hAY

theorem false_of_g2_twin_of_centralizing (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hcent : ∀ M ∈ tqMembers Ω c, M ≤ Subgroup.centralizer ({c} : Set G))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card) (hG2 : D.tag j = .G2)
    {M M' : Subgroup G} {b : G} (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hM'j : modOdd c (exactCore c M') ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range) : False :=
  false_of_g2_twin_sec hp hq hΩ hc2 (aEmpty_secFam_of_centralizing hp hq hΩ hcent hA) D j hG2
    hM hM' hMb hM'b hne hMj hM'j

theorem centralizes_of_exact (hex : ExactMembers Ω) {N : Subgroup G} (hN : N ∈ tqMembers Ω c) :
    N ≤ Subgroup.centralizer ({c} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : ⁅c, x⁆ ∈ oddCoreIn N := hN.2.2 x hx
  rw [show oddCoreIn N = ⊥ from oddCoreOf_eq_bot_of_exact hex hN.1] at h1
  have h2 := Subgroup.mem_bot.mp h1
  rw [commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

theorem false_of_g2_twin_of_exact (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M) (hex : ExactMembers Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card) (hG2 : D.tag j = .G2)
    {M M' : Subgroup G} {b : G} (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hM'j : modOdd c (exactCore c M') ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range) : False :=
  false_of_g2_twin_of_centralizing hp hq hΩ hA hc2 (fun _ hN => centralizes_of_exact hex hN) D j
    hG2 hM hM' hMb hM'b hne hMj hM'j

end Centralizing

end CFSG.ClassicalInvolution.Asc77
