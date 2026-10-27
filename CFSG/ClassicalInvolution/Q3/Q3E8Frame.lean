module

public import CFSG.ClassicalInvolution.Q3.Q3E8Facts

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Steinberg.Adjoint (iform)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


section Lift

theorem layerGeom_lift_E7_3 {X : Type} [Group X]
    (ψ : (modelUniv .E7 0 3 1 Nat.prime_three).K →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {R₁ R₂ : Subgroup (modelUniv .E7 0 3 1 Nat.prime_three).K}
    (h₁ : R₁ ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Nat.prime_three).D)
    (h₂ : R₂ ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Nat.prime_three).D)
    (hl : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂ := by
  have hY := yData3_E7 (⟨Nat.prime_three, le_rfl, rfl⟩ : StatedLieAdmissible .E7 0 3 1)
  have hfin : Finite (modelUniv .E7 0 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup _ _
  exact exists_lin_of_map3 (not_three_dvd_card_center hY.cop) ψ hψ (hY.pow3 R₁ h₁)
    (hY.pow3 R₂ h₂) hl

theorem e8LayerGeom3_of_signPerp (h : E7SignPerp3) : E8LayerGeom3 :=
  ⟨(TypeE8.signPerp_iff 3 1).2 h, fun ψ hψ _ h₁ _ h₂ hl => layerGeom_lift_E7_3 ψ hψ h₁ h₂ hl⟩

end Lift

section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

@[expose] def ETCtx3.IsFrameMember (c : ETCtx3 .E7 0 Ω K z) (g : TypeE8.K7 3 1) (δ : Fin 7 → ℤ)
    (N : Subgroup G) : Prop :=
  N ∈ centralizingMembers Ω {z} ∧ N ≠ K ∧
    locImg Ω z N = (conjSub g (TypeE8.Rroot 3 1 δ)).map c.d.ψ

theorem ETCtx3.exists_isFrameMember (c : ETCtx3 .E7 0 Ω K z) (hB8 : TypeE8.E7FrameRelations 3 1)
    (g : TypeE8.K7 3 1) {δ : Fin 7 → ℤ} (hδ : δ ∈ (TypeE8.D7 3 1).roots) :
    ∃ N : Subgroup G, c.IsFrameMember g δ N := by
  obtain ⟨N, hN, hNK, hNR⟩ := c.exists_member_of_fund (hB8 g δ δ hδ hδ).1
  exact ⟨N, hN, hNK, hNR⟩

variable {c : ETCtx3 .E7 0 Ω K z} {g : TypeE8.K7 3 1} {δ δ' : Fin 7 → ℤ} {N N' : Subgroup G}

theorem ETCtx3.IsFrameMember.mem_Ω (h : c.IsFrameMember g δ N) : N ∈ Ω := h.1.1

theorem ETCtx3.IsFrameMember.commutes_K (h : c.IsFrameMember g δ N) : Commutes K N :=
  c.commutes_K_of_ne h.1 h.2.1

theorem ETCtx3.IsFrameMember.commutes_of_orth (hB8 : TypeE8.E7FrameRelations 3 1)
    (h : c.IsFrameMember g δ N) (h' : c.IsFrameMember g δ' N')
    (hδ : δ ∈ (TypeE8.D7 3 1).roots) (hδ' : δ' ∈ (TypeE8.D7 3 1).roots)
    (ho : iform (τ := .E7) δ δ' = 0) : Commutes N N' :=
  (c.commutes_iff_fund h.1 h'.1 (hB8 g δ δ' hδ hδ').1 h.2.2 h'.2.2).mpr
    ((hB8 g δ δ' hδ hδ').2.1 ho)

theorem ETCtx3.IsFrameMember.stdPair_of_adj (hB8 : TypeE8.E7FrameRelations 3 1)
    (h : c.IsFrameMember g δ N) (h' : c.IsFrameMember g δ' N')
    (hδ : δ ∈ (TypeE8.D7 3 1).roots) (hδ' : δ' ∈ (TypeE8.D7 3 1).roots)
    (ha : iform (τ := .E7) δ δ' = -1) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N N' := by
  obtain ⟨-, W, hW⟩ := (hB8 g δ δ' hδ hδ').2.2 ha
  exact c.stdPair_of_fund h.1 h'.1 hW h.2.2 h'.2.2

theorem ETCtx3.IsFrameMember.fixed_of_even {t : G} {ht : t * z * t⁻¹ = z} {p₀ : Fin 7}
    (hT : ToralNormalAt3 c ht g p₀) (h : c.IsFrameMember g δ N)
    (hδ : δ ∈ (TypeE8.D7 3 1).roots) (he : ((δ p₀ : ℤ) : ZMod 2) = 0) :
    ∀ x ∈ locImg Ω z N, Gaps.locAut c.hΩ.conjInvariant ht x = x := by
  rw [h.2.2]
  exact ((hT δ hδ).2).mpr he

theorem ETCtx3.IsFrameMember.le_centralizer_of_even {t : G} {ht : t * z * t⁻¹ = z} {p₀ : Fin 7}
    (hT : ToralNormalAt3 c ht g p₀) (h : c.IsFrameMember g δ N)
    (hδ : δ ∈ (TypeE8.D7 3 1).roots) (he : ((δ p₀ : ℤ) : ZMod 2) = 0) :
    N ≤ Subgroup.centralizer ({t} : Set G) :=
  (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht h.1).mpr (h.fixed_of_even hT hδ he)

theorem ETCtx3.IsFrameMember.commutes_partner_of_even (hMFZ : Gaps.FundNoncentral 3)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {ht : t * z * t⁻¹ = z} {p₀ : Fin 7} (hT : ToralNormalAt3 c ht g p₀)
    (h : c.IsFrameMember g δ N) (hδ : δ ∈ (TypeE8.D7 3 1).roots)
    (he : ((δ p₀ : ℤ) : ZMod 2) = 0) : Commutes β N :=
  c.commutes_partner_of_centralizes hMFZ hsingle D hβ htβ hKβ h.1
    (h.le_centralizer_of_even hT hδ he) h.commutes_K

theorem ETCtx3.IsFrameMember.not_commutes_partner_of_odd {β : Subgroup G} {t : G}
    (htβ : IsClassicalMember3 β t) {ht : t * z * t⁻¹ = z} {p₀ : Fin 7}
    (hT : ToralNormalAt3 c ht g p₀) (h : c.IsFrameMember g δ N)
    (hδ : δ ∈ (TypeE8.D7 3 1).roots) (ho : ((δ p₀ : ℤ) : ZMod 2) ≠ 0) :
    ¬ Commutes β N := by
  intro hc
  apply ho
  refine ((hT δ hδ).2).mp ?_
  rw [← h.2.2]
  exact (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht h.1).mp fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc t htβ.mem n hn).symm

end Members

section Witness

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} {x : G}

theorem ETCtx3.stdPair_model_E7 (cx : ETCtx3 .E7 0 Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv .E7 0 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ)
    (h : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W L L') :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R' := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members cx.hP1 hL hL' hW
  rw [hLR, hLR'] at hW'
  exact layerGeom_lift_E7_3 cx.d.ψ cx.d.ker_le hR hR' ⟨W', hW'⟩

end Witness

end CFSG.ClassicalInvolution.Q3.Q3W
