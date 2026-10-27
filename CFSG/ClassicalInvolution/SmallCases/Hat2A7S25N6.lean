module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N4
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Nu5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.C25V
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped MatrixGroups commutatorElement

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

section Models

variable {G : Type} [Group G]

@[expose] def Iso5 (K : Subgroup G) (b : G) : Prop :=
  Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
    classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ≃*
      SL(2, GaloisField 5 1))

@[expose] def Mem5 (K : Subgroup G) (b : G) : Prop :=
  ∀ x ∈ K, x ∈ Subgroup.centralizer ({b} : Set G) → IsPGroup 2 (Subgroup.zpowers x) →
    x ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))

@[expose] def Iso3 (K : Subgroup G) (b : G) : Prop :=
  Nonempty (↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ⧸
    classicalInvolutionOddCore ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ≃*
      SL(2, GaloisField 3 1))

end Models

section Model


@[expose] def W3Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R' a → FixDiv5 K' a → Iso5 K' a ∧ Mem5 K' a

end Model

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem ne_one_of_isFAut_hyp (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF' : IsFAut R' a) : a ≠ 1 := by
  obtain ⟨zc, hzc⟩ := h.hs.stand.classical K' h.hK'
  obtain ⟨π, zE, cov, -⟩ := Hat2A7.exists_cover_of_witness hzc.witness
  have haN : a ∈ Subgroup.normalizer (K' : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (fix_of_isFAut h haS hF').2.2.2
  have h1 := Hat2A7S.epsG_eq_neg_one_of_isFAut cov h.hR'syl h.hz' haN ha2 hF'
  rintro rfl
  rw [Hat2A7.epsG_one cov] at h1
  exact absurd h1 (by decide)


theorem a7_false_of_ff5 (h11 : A7C25_11) (hyp : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a) (hF' : IsFAut R' a)
    (hZ : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hiso : Iso5 K' a) (hmem : Mem5 K' a) : False := by
  classical
  obtain ⟨t', g, h, hg, hnf, hat⟩ :=
    Hat2A7M.Asc77.C25V.exists_comm_swap_of_ff (Hat2A7S.Eps.c25_11_mirror h11) hyp.toMirror haS ha2
      hFa hF'
  have ha1 : a ≠ 1 := ne_one_of_isFAut_hyp h haS ha2 hF'
  have hp : (5 : ℕ) ≠ 2 := by norm_num
  have h5 : 5 ≤ 5 ^ 1 := by norm_num
  have hzA : z ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.hyp.hzS a haS).symm
  have d' := twinCtx'_of_hyp25 h
  have hconj : ∀ y x : G, y ∈ Subgroup.centralizer ({z} : Set G) →
      x ∈ Subgroup.centralizer ({z} : Set G) → conjSub x K' = K' →
        conjSub (y * x * y⁻¹) K' = K' := fun y x hy hx hxK =>
    d'.conj_normalizer (Subgroup.mem_centralizer_singleton_iff.mp hy)
      (Subgroup.mem_centralizer_singleton_iff.mp hx) hxK
  have hL : IsClassicalMember 5 1 (perfectCoreIn K' a) ⟨z, hzA⟩ :=
    fs_isClassicalMember h.hz' (C25V.isUniqueInvolution_le_centralizer h.hz') hconj hp hzA hiso
  obtain ⟨y, hyR', hy4, hya⟩ := Hat2A7S.Eps.exists_order_four_of_isFAut hF'
  have hy : ∃ y ∈ R', orderOf y = 4 ∧ y * a = a * y ∧
      y ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) :=
    ⟨y, hyR', hy4, hya, hmem y (h.hR'syl.1 hyR') (Subgroup.mem_centralizer_singleton_iff.mpr hya)
      (IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hy4]; norm_num))⟩
  have hlt : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) < Nat.card G :=
    fs_card_centralizer_lt (exists_noncomm_of_swap h) ha1
  have hIH : CITBelowU 5 1 (Nat.card G) :=
    (citBelowT_iff_citBelowU hp h5 _).mp (h.hs.stand.below5 1 (by norm_num))
  rcases fs_typed hp h5 hIH h hat hzA hL hy hlt with hz | h5' | h6'
  · exact hZ hz
  · obtain ⟨t₀, y₁, c₁, hsw, hat₀, hcz, hc₁a, hy₁K, hy₁4, hy₁a, hy₁x, hlast⟩ :=
      typed5_data h ha2 ha1 hat hp h5 hzA hL hy h5'
    exact Hat2A7S.a7_false_of_swap_data h11 h haS ha2 hFa hF' hat hsw hat₀ hcz hc₁a hy₁K hy₁4
      hy₁a hy₁x hlast
  · exact false_of_omega6 h hat hp h5 hzA hL hy h6'

theorem a7NoFFz5_of_w3 (h11 : A7C25_11) (hW : W3Five) : A7NoFFz5 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ hdiv
  obtain ⟨hiso, hmem⟩ := hW G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa' hdiv
  exact a7_false_of_ff5 h11 hyp haS ha2 hFa hFa' hZ hiso hmem

end Main

end CFSG.ClassicalInvolution.Hat2A7S.N
