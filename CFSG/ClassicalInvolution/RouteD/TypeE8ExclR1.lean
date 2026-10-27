module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclRFrame
public import CFSG.ClassicalInvolution.RouteD.TypeE8Witness

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm)
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm)

variable {p f : ℕ} [Fact p.Prime]

namespace TypeE8

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem r1_false (hMFZ : Gaps.FundNoncentral p) (hB8 : E7FrameRelations p f)
    (hB7 : E7PerpA2StarFree p f) (c : ETCtx p f .E7 0 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .E7 0 Ω z)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    (ht : t * z * t⁻¹ = z) (g : K7 p f) {p₀ : Fin 7}
    (hp₀ : p₀ = 0 ∨ p₀ = 2 ∨ p₀ = 3 ∨ p₀ = 5) (hT : ToralNormalAt p f c ht g p₀) : False := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨γ, cc, l₁, l₂, l₃, hγ, hcc, hl₁, hl₂, hl₃, eγ, ecc, e₁, e₂, e₃, oγc, oγ₁, oγ₂, oγ₃,
    a₁, a₂, a₃, o₁₂, o₁₃, o₂₃⟩ := exists_r1_roots p f p₀ hp₀
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem htβ.mem c.hz.orderOf_eq_two
      htβ.orderOf_eq_two
  have hnormK : conjSub t K = K :=
    Gaps.conjSub_eq_of_standardPair h2 hW htβ.mem htβ.orderOf_eq_two
  obtain ⟨Nγ, hNγ⟩ := c.exists_isFrameMember hB8 g hγ
  obtain ⟨Nc, hNc⟩ := c.exists_isFrameMember hB8 g hcc
  obtain ⟨N₁, hN₁⟩ := c.exists_isFrameMember hB8 g hl₁
  obtain ⟨N₂, hN₂⟩ := c.exists_isFrameMember hB8 g hl₂
  obtain ⟨N₃, hN₃⟩ := c.exists_isFrameMember hB8 g hl₃
  have hβ' : ∀ {δ : Fin 7 → ℤ} {N : Subgroup G}, δ ∈ (D7 p f).roots →
      ((δ p₀ : ℤ) : ZMod 2) = 0 → ETCtx.IsFrameMember c g δ N → Commutes β N :=
    fun hδ he h => h.commutes_partner_of_even hMFZ hsingle hshape hβ htβ ⟨W, hW⟩ hT hδ he
  obtain ⟨x, hx⟩ := c.hΩ.classical Nγ hNγ.mem_Ω
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hshape hNγ.mem_Ω hx
  have hmem : ∀ {N : Subgroup G}, N ∈ Ω → Commutes N Nγ → N ∈ centralizingMembers Ω {x} :=
    fun hN h => mem_centralizingMembers_of_commutes hN hx.mem h
  have hKx : K ∈ centralizingMembers Ω {x} := hmem c.hK hNγ.commutes_K
  have hβx : β ∈ centralizingMembers Ω {x} := hmem hβ (hβ' hγ eγ hNγ)
  have hcx : Nc ∈ centralizingMembers Ω {x} :=
    hmem hNc.mem_Ω (hNc.commutes_of_orth hB8 hNγ hcc hγ ((iform_comm (τ := .E7) cc γ).trans oγc))
  have h1x : N₁ ∈ centralizingMembers Ω {x} :=
    hmem hN₁.mem_Ω (hN₁.commutes_of_orth hB8 hNγ hl₁ hγ ((iform_comm (τ := .E7) l₁ γ).trans oγ₁))
  have h2x : N₂ ∈ centralizingMembers Ω {x} :=
    hmem hN₂.mem_Ω (hN₂.commutes_of_orth hB8 hNγ hl₂ hγ ((iform_comm (τ := .E7) l₂ γ).trans oγ₂))
  have h3x : N₃ ∈ centralizingMembers Ω {x} :=
    hmem hN₃.mem_Ω (hN₃.commutes_of_orth hB8 hNγ hl₃ hγ ((iform_comm (τ := .E7) l₃ γ).trans oγ₃))
  have hKL := ETCtx.IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := ETCtx.IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hadj : Gaps.ModelAdj (Subgroup.center (modelUniv .E7 0 p f Fact.out).K) RK Rβ :=
    cx.modelAdj_of_adj hKx hβx hRK hRβ hKR hβR c.hz htβ hKne hnKβ hzt hnormK
  have hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W RK Rβ :=
    cx.stdPair_model_E7 hKx hβx hRK hRβ hKR hβR ⟨W, hW⟩
  have hstd₁ := hNc.stdPair_of_adj hB8 hN₁ hcc hl₁ a₁
  have hstd₂ := hNc.stdPair_of_adj hB8 hN₂ hcc hl₂ a₂
  have hstd₃ := hNc.stdPair_of_adj hB8 hN₃ hcc hl₃ a₃
  have hlay : ∀ {L L' : Subgroup G}, L ∈ centralizingMembers Ω {x} →
      L' ∈ centralizingMembers Ω {x} →
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W L L') →
      ETCtx.IsLayerMember cx L ∧ ETCtx.IsLayerMember cx L' := fun hL hL' hs => by
    obtain ⟨W₀, hW₀⟩ := hs
    exact ⟨ETCtx.IsLayerMember.of_not_commutes cx hL hL' (ne_of_linearBlockStandardPair hW₀)
      (not_commutes_of_linearBlockStandardPair hW₀),
      ETCtx.IsLayerMember.of_not_commutes cx hL' hL (ne_of_linearBlockStandardPair hW₀).symm
        (fun h => not_commutes_of_linearBlockStandardPair hW₀ (commutes_symm h))⟩
  obtain ⟨hcL, h1L⟩ := hlay hcx h1x hstd₁
  obtain ⟨-, h2L⟩ := hlay hcx h2x hstd₂
  obtain ⟨-, h3L⟩ := hlay hcx h3x hstd₃
  obtain ⟨RC, hRC, hCR⟩ := hcL.exists_fund
  obtain ⟨R₁, hR₁, h1R⟩ := h1L.exists_fund
  obtain ⟨R₂, hR₂, h2R⟩ := h2L.exists_fund
  obtain ⟨R₃, hR₃, h3R⟩ := h3L.exists_fund
  have hcomm : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .E7 0 p f Fact.out).K},
      L ∈ centralizingMembers Ω {x} → L' ∈ centralizingMembers Ω {x} →
      R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D →
      locImg Ω x L = R.map cx.d.ψ → locImg Ω x L' = R'.map cx.d.ψ → Commutes L L' →
      Commutes R R' := fun hL hL' hR hLR hLR' h =>
    (cx.commutes_iff_fund hL hL' hR hLR hLR').mp h
  refine hB7 RK hRK Rβ hRβ hadj hlin RC hRC R₁ hR₁ R₂ hR₂ R₃ hR₃
    (hcomm hcx hKx hRC hCR hKR (hNc.commutes_K).symm)
    (hcomm hcx hβx hRC hCR hβR (hβ' hcc ecc hNc).symm)
    (hcomm h1x hKx hR₁ h1R hKR (hN₁.commutes_K).symm)
    (hcomm h1x hβx hR₁ h1R hβR (hβ' hl₁ e₁ hN₁).symm)
    (hcomm h2x hKx hR₂ h2R hKR (hN₂.commutes_K).symm)
    (hcomm h2x hβx hR₂ h2R hβR (hβ' hl₂ e₂ hN₂).symm)
    (hcomm h3x hKx hR₃ h3R hKR (hN₃.commutes_K).symm)
    (hcomm h3x hβx hR₃ h3R hβR (hβ' hl₃ e₃ hN₃).symm)
    (cx.stdPair_model_E7 hcx h1x hRC hR₁ hCR h1R hstd₁)
    (cx.stdPair_model_E7 hcx h2x hRC hR₂ hCR h2R hstd₂)
    (cx.stdPair_model_E7 hcx h3x hRC hR₃ hCR h3R hstd₃)
    (hcomm h1x h2x hR₁ h1R h2R (hN₁.commutes_of_orth hB8 hN₂ hl₁ hl₂ o₁₂))
    (hcomm h1x h3x hR₁ h1R h3R (hN₁.commutes_of_orth hB8 hN₃ hl₁ hl₃ o₁₃))
    (hcomm h2x h3x hR₂ h2R h3R (hN₂.commutes_of_orth hB8 hN₃ hl₂ hl₃ o₂₃))

theorem e8R1Excluded : E8R1Excluded p f := by
  intro hMFZ hB8 hB7 G _ _ _ _ K z _ hshape c β hβ t htβ hKβ ht g p₀ hp₀ hT
  exact r1_false hMFZ hB8 hB7 c (CoreAssembly.single_class K) hshape hβ htβ hKβ ht g hp₀ hT

end TypeE8

end CFSG.ClassicalInvolution.RouteD
