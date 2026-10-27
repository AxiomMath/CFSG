module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleTwin

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

section Facts

variable {KY : Type} [Group KY]

@[expose] def TwinWithinCentralizer (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ R ∈ 𝓕, ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → Commutes A B → Commutes A R → Commutes B R →
    (∀ T ∈ 𝓕, Commutes T R → ((T = A ∨ Commutes T A) ↔ (T = B ∨ Commutes T B))) →
      IsFundTwin 𝓕 A B

@[expose] def TwinInvolutionKernel (𝓕 : Set (Subgroup KY)) : Prop :=
  ∃ ε : KY, ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, IsFundTwin 𝓕 R R' → ∀ r ∈ R, ∀ r' ∈ R', orderOf r = 2 →
    orderOf r' = 2 → r = r' ∨ r * r' = ε

@[expose] def FundHasOrthogonal (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ R ∈ 𝓕, ∃ S ∈ 𝓕, S ≠ R ∧ Commutes S R ∧ ¬ IsFundTwin 𝓕 R S

@[expose] def FundHasClique (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ R ∈ 𝓕, ∃ R₂ ∈ 𝓕, ∃ R₃ ∈ 𝓕, ∃ R₄ ∈ 𝓕, R ≠ R₂ ∧ R ≠ R₃ ∧ R ≠ R₄ ∧ R₂ ≠ R₃ ∧ R₂ ≠ R₄ ∧
    R₃ ≠ R₄ ∧ Commutes R R₂ ∧ Commutes R R₃ ∧ Commutes R R₄ ∧ Commutes R₂ R₃ ∧ Commutes R₂ R₄ ∧
      Commutes R₃ R₄

@[expose] def FundCliqueProd (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ R₃ ∈ 𝓕, ∀ R₄ ∈ 𝓕, R₁ ≠ R₂ → R₁ ≠ R₃ → R₁ ≠ R₄ → R₂ ≠ R₃ → R₂ ≠ R₄ →
    R₃ ≠ R₄ → Commutes R₁ R₂ → Commutes R₁ R₃ → Commutes R₁ R₄ → Commutes R₂ R₃ →
      Commutes R₂ R₄ → Commutes R₃ R₄ → ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, ∀ r₃ ∈ R₃, ∀ r₄ ∈ R₄,
        orderOf r₁ = 2 → orderOf r₂ = 2 → orderOf r₃ = 2 → orderOf r₄ = 2 → r₁ ≠ r₂ → r₁ ≠ r₃ →
          r₁ ≠ r₄ → r₂ ≠ r₃ → r₂ ≠ r₄ → r₃ ≠ r₄ → r₁ * r₂ * r₃ * r₄ = 1

theorem IsFundTwin.symm {𝓕 : Set (Subgroup KY)} {R R' : Subgroup KY} (h : IsFundTwin 𝓕 R R') :
    IsFundTwin 𝓕 R' R :=
  ⟨h.1.symm, h.2.1.symm, fun S hS => (h.2.2 S hS).symm⟩

end Facts

section Images

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem ctx_eq_or_commutes_iff (c : ETCtx p f tY nY Ω K z) {N N' : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hN' : N' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K} (hR : R ∈ modelFund p f tY nY)
    (hR' : R' ∈ modelFund p f tY nY) (hNR : locImg Ω z N = R.map c.d.ψ)
    (hN'R' : locImg Ω z N' = R'.map c.d.ψ) :
    (R = R' ∨ Commutes R R') ↔ (N = N' ∨ Commutes N N') := by
  refine or_congr ⟨fun h => ?_, fun h => ?_⟩ (c.commutes_iff_fund hN hN' hR hNR hN'R').symm
  · exact c.eq_of_locImg_eq hN hN' (by rw [hNR, hN'R', h])
  · subst h
    exact eq_of_map_eq_of_perfect c.d.ψ c.d.ker_le (c.hY.perfR R hR) (c.hY.perfR R' hR')
      (hNR.symm.trans hN'R')

end Images

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem twin_at_z_of_twin_at_x (c : ETCtx p f tY nY Ω K z)
    (hTC : TwinWithinCentralizer (modelFund p f tY nY)) {M : Subgroup G} {xM : G}
    (hM : M ∈ centralizingMembers Ω {z}) (hxM : IsClassicalMember p f M xM)
    (cx : ETCtx p f tY nY Ω M xM) {R₀ : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR₀ : R₀ ∈ modelFund p f tY nY) (hMR : locImg Ω z M = R₀.map c.d.ψ)
    {N N' : Subgroup G} (hN : N ∈ centralizingMembers Ω {xM}) (hNM : N ≠ M)
    (hN' : N' ∈ centralizingMembers Ω {xM}) (hN'M : N' ≠ M)
    {S S' : Subgroup (modelUniv tY nY p f Fact.out).K} (hS : S ∈ modelFund p f tY nY)
    (hS' : S' ∈ modelFund p f tY nY) (hNS : locImg Ω xM N = S.map cx.d.ψ)
    (hN'S : locImg Ω xM N' = S'.map cx.d.ψ) (htwin : IsFundTwin (modelFund p f tY nY) S S')
    (hNz : N ∈ centralizingMembers Ω {z}) (hN'z : N' ∈ centralizingMembers Ω {z})
    {A B : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hA : A ∈ modelFund p f tY nY) (hB : B ∈ modelFund p f tY nY)
    (hNA : locImg Ω z N = A.map c.d.ψ) (hN'B : locImg Ω z N' = B.map c.d.ψ) :
    IsFundTwin (modelFund p f tY nY) A B := by
  have hNN'ne : N ≠ N' := fun h =>
    htwin.1 (eq_of_map_eq_of_perfect cx.d.ψ cx.d.ker_le (cx.hY.perfR S hS) (cx.hY.perfR S' hS')
      (hNS.symm.trans (h ▸ hN'S)))
  have hNN' : Commutes N N' := (cx.commutes_iff_fund hN hN' hS hNS hN'S).mpr htwin.2.1
  have hMN : Commutes M N := cx.commutes_K_of_ne hN hNM
  refine hTC R₀ hR₀ A hA B hB
    (fun h => hNN'ne (c.eq_of_locImg_eq hNz hN'z (by rw [hNA, hN'B, h])))
    ((c.commutes_iff_fund hNz hN'z hA hNA hN'B).mp hNN')
    ((c.commutes_iff_fund hNz hM hA hNA hMR).mp hMN.symm)
    ((c.commutes_iff_fund hN'z hM hB hN'B hMR).mp (cx.commutes_K_of_ne hN' hN'M).symm)
    fun T hT' hTR => ?_
  obtain ⟨NT, hNT, hNTK, hNTT⟩ := c.exists_member_of_fund hT'
  have hNTM : Commutes NT M := (c.commutes_iff_fund hNT hM hT' hNTT hMR).mpr hTR
  have hNTx : NT ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hNT.1 hxM.mem hNTM
  have hNTMne : NT ≠ M := by
    rintro rfl
    exact not_commutes_self_of_mem c.hΩ hM.1 hNTM
  obtain ⟨RT, hRT, hNTR⟩ := cx.exists_fund_of_ne hNTx hNTMne
  rw [ctx_eq_or_commutes_iff c hNT hNz hT' hA hNTT hNA,
    ctx_eq_or_commutes_iff c hNT hN'z hT' hB hNTT hN'B,
    ← ctx_eq_or_commutes_iff cx hNTx hN hRT hS hNTR hNS,
    ← ctx_eq_or_commutes_iff cx hNTx hN' hRT hS' hNTR hN'S]
  exact htwin.2.2 RT hRT

end Main

end CFSG.ClassicalInvolution.RouteD.Exotic
