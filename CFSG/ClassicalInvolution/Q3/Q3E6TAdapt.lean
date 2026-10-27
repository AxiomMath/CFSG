module

public import CFSG.ClassicalInvolution.Q3.Q3E6TAlpha
public import CFSG.ClassicalInvolution.Q3.Q3E6TSplit
public import CFSG.ClassicalInvolution.Q3.Q3TY8
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

@[expose] def TE6AdaptedFrames3 (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) : Prop :=
  ∀ N ∈ centralizingMembers (conjClass3 K) {z * nd.w 0},
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N) →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N (nd.j 0)) →
    ∀ Θ : Su (GaloisField 3 2) 3 1 6 →* G, TE6Chart3 c nd Θ →
    ∀ v : G, IsClassicalMember3 N v →
    ∀ α : Su (GaloisField 3 2) 3 1 6 →* Su (GaloisField 3 2) 3 1 6,
      (∀ x, Θ (α x) = v * Θ x * v⁻¹) → AdaptedFrame 3 1 le_rfl α

section Perfect

variable [Finite G]


theorem commutes_partner_of_perfect_ctx3 (c : UCtx3 5 Ω K z) (hMFZ : Gaps.FundNoncentral 3)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type} [Finite ι]
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) (hD : Nat.card ι ≤ 4)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t) {S : Subgroup G}
    (hS : ⁅S, S⁆ = S) (hSt : S ≤ Subgroup.centralizer ({t} : Set G)) : Commutes β S := by
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ := involution_unique3 ht (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]
    exact Gaps.localOddCentral_conj c.hΩ.conjInvariant h z c.hP1
  have hO3t : LocalOddThreeFree3 Ω t := by
    rw [ht_eq]
    exact localOddThreeFree3_conj c.hΩ.conjInvariant h z c.hO3
  obtain ⟨Dt⟩ := exists_lieSystemData_conj3 c.hΩ.conjInvariant h z D
  rw [← ht_eq] at Dt
  have hnorm := Q3TY.perfect_le_normalizer_of_involution3 hMFZ c.hΩ c.hex hP1t hO3t Dt hD hSt hS
    hβ ht
  obtain ⟨e⟩ := ht.nonempty_equiv_sl2 (c.hex β hβ)
  have hcent := Q3TY.perfect_le_centralizer_of_normalizes_sl2 e hS hnorm
  intro b hb s hs
  exact Subgroup.mem_centralizer_iff.mp (hcent hs) b hb

end Perfect

theorem partner_involution_commutes3 {K N : Subgroup G} {z v : G} (hz : IsClassicalMember3 K z)
    (hv : IsClassicalMember3 N v)
    (hKN : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K N) : v * z * v⁻¹ = z := by
  obtain ⟨W, hW⟩ := hKN
  have := Gaps.standardPair_involutions_commute
    (two_ne_zero_of_charP_ne_two (K := GaloisField 3 1) (p := 3) (by norm_num)) hW hz.mem
    hv.mem hz.orderOf_eq_two hv.orderOf_eq_two
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

section Fixed

variable [Finite G]


theorem commutes_of_alpha_fixed3 (c : UCtx3 5 (conjClass3 K) K z)
    (hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z)
    {Θ : Su (GaloisField 3 2) 3 1 6 →* G} {N : Subgroup G} (hN : N ∈ conjClass3 K) {v : G}
    (hv : IsClassicalMember3 N v)
    {α : Su (GaloisField 3 2) 3 1 6 →* Su (GaloisField 3 2) 3 1 6}
    (hα : ∀ x, Θ (α x) = v * Θ x * v⁻¹) {S : Subgroup (Su (GaloisField 3 2) 3 1 6)}
    (hS : ⁅S, S⁆ = S) (hfix : ∀ x ∈ S, α x = x) : Commutes N (S.map Θ) := by
  classical
  obtain ⟨ι, hι, D, hcard, -⟩ := hshape
  refine commutes_partner_of_perfect_ctx3 c (Gaps.fundNoncentral 3) hsingle D (by omega) hN hv
    (S := S.map Θ) ?_ ?_
  · rw [← Subgroup.map_commutator, hS]
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (TE6Chart3.centralizes_of_fixed hα (hfix x hx)).symm

end Fixed

section Adaptation

variable [Finite G]


theorem te6Adaptation3_of_adaptedFrames (hP : Phan3Rec)
    (hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z)
    (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) (hAF : TE6AdaptedFrames3 c nd) :
    TE6Adaptation3 c nd := by
  classical
  intro N hN hNK hNj
  obtain ⟨v, hv⟩ := c.hΩ.classical N hN.1
  have hvz : v * z * v⁻¹ = z := partner_involution_commutes3 c.hz hv hNK
  have hv2 : v * v = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one v
    rwa [hv.orderOf_eq_two] at this
  obtain ⟨Θ, hΘ⟩ := UCtx3.exists_te6Chart3 hP c nd
  obtain ⟨α, g, φ, hα, -⟩ := hΘ.exists_alpha hvz hv2
  obtain ⟨F, hF1, hFS2, hFS3⟩ := hAF N hN hNK hNj Θ hΘ v hv α hα
  have hcomm : ∀ S : Subgroup (Su (GaloisField 3 2) 3 1 6), ⁅S, S⁆ = S →
      (∀ x ∈ S, α x = x) → Commutes N (S.map Θ) := fun S hS hfix =>
    commutes_of_alpha_fixed3 c hsingle hshape hN.1 hv hα hS hfix
  have h4 : 4 ≤ Nat.card (GaloisField 3 (2 * 1)) := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨h12, h23⟩ := Gaps.map_blocks_perfect h4 F.ι₃
  rw [F.ι₃_B12] at h12
  rw [F.ι₃_B23] at h23
  refine ⟨![F.R₁.map Θ, F.S₂.map Θ, F.S₃.map Θ], hΘ.isTE6Base F, ?_, hcomm _ h23 hFS2,
    hcomm _ h12 hFS3⟩
  show F.R₁.map Θ = nd.j 0
  rw [hF1, ← range_blockEmb2_eq_LcU_nodePair two_ne_zero_gf9 (by norm_num : 0 < 5)]
  exact hΘ.block ⟨0, by norm_num⟩

end Adaptation

end CFSG.ClassicalInvolution.Q3.Q3E6T
