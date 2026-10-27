module

public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternRows

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.LieType.Steinberg.Adjoint (iform)

variable {p f : ℕ} [Fact p.Prime]

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

@[expose] def IsFrameMember (c : ETCtx p f .E7 0 Ω K z) (g : TypeE8.K7 p f) (δ : Fin 7 → ℤ)
    (N : Subgroup G) : Prop :=
  N ∈ centralizingMembers Ω {z} ∧ N ≠ K ∧
    locImg Ω z N = (conjSub g (TypeE8.Rroot p f δ)).map c.d.ψ

theorem exists_isFrameMember (c : ETCtx p f .E7 0 Ω K z) (hB8 : TypeE8.E7FrameRelations p f)
    (g : TypeE8.K7 p f) {δ : Fin 7 → ℤ} (hδ : δ ∈ (TypeE8.D7 p f).roots) :
    ∃ N : Subgroup G, IsFrameMember c g δ N := by
  obtain ⟨N, hN, hNK, hNR⟩ := c.exists_member_of_fund (hB8 g δ δ hδ hδ).1
  exact ⟨N, hN, hNK, hNR⟩

variable {c : ETCtx p f .E7 0 Ω K z} {g : TypeE8.K7 p f} {δ δ' : Fin 7 → ℤ} {N N' : Subgroup G}

omit [Finite G] in
theorem IsFrameMember.mem_Ω (h : IsFrameMember c g δ N) : N ∈ Ω := h.1.1

theorem IsFrameMember.commutes_K (h : IsFrameMember c g δ N) : Commutes K N :=
  c.commutes_K_of_ne h.1 h.2.1

theorem IsFrameMember.commutes_of_orth (hB8 : TypeE8.E7FrameRelations p f)
    (h : IsFrameMember c g δ N) (h' : IsFrameMember c g δ' N')
    (hδ : δ ∈ (TypeE8.D7 p f).roots) (hδ' : δ' ∈ (TypeE8.D7 p f).roots)
    (ho : iform (τ := .E7) δ δ' = 0) : Commutes N N' :=
  (c.commutes_iff_fund h.1 h'.1 (hB8 g δ δ' hδ hδ').1 h.2.2 h'.2.2).mpr
    ((hB8 g δ δ' hδ hδ').2.1 ho)

theorem IsFrameMember.stdPair_of_adj (hB8 : TypeE8.E7FrameRelations p f)
    (h : IsFrameMember c g δ N) (h' : IsFrameMember c g δ' N')
    (hδ : δ ∈ (TypeE8.D7 p f).roots) (hδ' : δ' ∈ (TypeE8.D7 p f).roots)
    (ha : iform (τ := .E7) δ δ' = -1) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W N N' := by
  obtain ⟨-, W, hW⟩ := (hB8 g δ δ' hδ hδ').2.2 ha
  exact c.stdPair_of_fund h.1 h'.1 hW h.2.2 h'.2.2

omit [Finite G] in
theorem IsFrameMember.fixed_of_even {t : G} {ht : t * z * t⁻¹ = z} {p₀ : Fin 7}
    (hT : TypeE8.ToralNormalAt p f c ht g p₀) (h : IsFrameMember c g δ N)
    (hδ : δ ∈ (TypeE8.D7 p f).roots) (he : ((δ p₀ : ℤ) : ZMod 2) = 0) :
    ∀ x ∈ locImg Ω z N, Gaps.locAut c.hΩ.conjInvariant ht x = x := by
  rw [h.2.2]
  exact ((hT δ hδ).2).mpr he

theorem IsFrameMember.le_centralizer_of_even {t : G} {ht : t * z * t⁻¹ = z} {p₀ : Fin 7}
    (hT : TypeE8.ToralNormalAt p f c ht g p₀) (h : IsFrameMember c g δ N)
    (hδ : δ ∈ (TypeE8.D7 p f).roots) (he : ((δ p₀ : ℤ) : ZMod 2) = 0) :
    N ≤ Subgroup.centralizer ({t} : Set G) :=
  (Gaps.locAut_fixed_iff c.hΩ c.hP1 ht h.1).mpr (h.fixed_of_even hT hδ he)

theorem IsFrameMember.commutes_partner_of_even (hMFZ : Gaps.FundNoncentral p)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .E7 0 Ω z)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    {ht : t * z * t⁻¹ = z} {p₀ : Fin 7} (hT : TypeE8.ToralNormalAt p f c ht g p₀)
    (h : IsFrameMember c g δ N) (hδ : δ ∈ (TypeE8.D7 p f).roots)
    (he : ((δ p₀ : ℤ) : ZMod 2) = 0) : Commutes β N := by
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    have : NeZero f := ⟨c.hf⟩
    Gaps.standardPairAutAbelian_galoisField c.hp2 c.hq
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  exact c.commutes_partner_of_centralizes hsingle hMFZ hS3 hD4 hβ htβ hKβ h.1
    (h.le_centralizer_of_even hT hδ he) h.commutes_K

theorem IsFrameMember.not_commutes_partner_of_odd {β : Subgroup G} {t : G}
    (htβ : IsClassicalMember p f β t) {ht : t * z * t⁻¹ = z} {p₀ : Fin 7}
    (hT : TypeE8.ToralNormalAt p f c ht g p₀) (h : IsFrameMember c g δ N)
    (hδ : δ ∈ (TypeE8.D7 p f).roots) (ho : ((δ p₀ : ℤ) : ZMod 2) ≠ 0) :
    ¬ Commutes β N := by
  intro hc
  apply ho
  refine ((hT δ hδ).2).mp ?_
  rw [← h.2.2]
  exact (Gaps.locAut_fixed_iff c.hΩ c.hP1 ht h.1).mp fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc t htβ.mem n hn).symm

end ETCtx

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} {x : G}

omit [Finite G] in
theorem stdPair_model_E7 (cx : ETCtx p f .E7 0 Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv .E7 0 p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ)
    (h : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W L L') :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W R R' := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members cx.hP1 hL hL' hW
  rw [hLR, hLR'] at hW'
  exact TypeEPattern.layerGeom_lift_E7 cx.hq cx.d.ψ cx.d.ker_le hR hR' ⟨W', hW'⟩

end ETCtx

end CFSG.ClassicalInvolution.RouteD
