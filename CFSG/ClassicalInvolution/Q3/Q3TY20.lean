module

public import CFSG.ClassicalInvolution.Q3.Q3TY9
public import CFSG.Assembly.RankThreeEvenDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open scoped MatrixGroups commutatorElement


section Base

variable {G : Type} [Group G]

theorem locAut_fixed_iff_of_perfect3 [Finite G] {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {t z : G} (hP1 : LocalOddCentral Ω {z}) (ht : t * z * t⁻¹ = z) {N : Subgroup G}
    (hN : N ≤ locLayer Ω z) (hNp : N ≤ ⁅N, N⁆) :
    N ≤ Subgroup.centralizer ({t} : Set G) ↔
      ∀ a ∈ locImg Ω z N, Gaps.locAut hΩ ht a = a := by
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    show Gaps.locMk Ω z (Gaps.layerAut hΩ ht b) = Gaps.locMk Ω z b
    congr 1
    apply Subtype.ext
    show t * (b : G) * t⁻¹ = b
    have := Subgroup.mem_centralizer_singleton_iff.mp (h (Subgroup.mem_subgroupOf.mp hb))
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  · intro h n hn
    have hperf := isPerfect_subgroupOf hN hNp
    set Y := locLayer Ω z
    set O := classicalInvolutionOddCore ↥Y
    have hOc : ∀ b ∈ N.subgroupOf Y, b⁻¹ * Gaps.layerAut hΩ ht b ∈ O := by
      intro b hb
      have := h _ ⟨b, hb, rfl⟩
      have h2 : Gaps.locMk Ω z (Gaps.layerAut hΩ ht b) = Gaps.locMk Ω z b := this
      exact QuotientGroup.eq.mp h2.symm
    have key := Gaps.fixed_of_perfect_of_central (Gaps.layerAut hΩ ht).toMonoidHom
      (N := N.subgroupOf Y) hperf hP1 hOc
    have := key ⟨n, hN hn⟩ (Subgroup.mem_subgroupOf.mpr hn)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h4 := congrArg Subtype.val this
    have h5 : t * n * t⁻¹ = n := h4
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5.symm

theorem PartnerPatternMinus3.of_conj {m : ℕ} {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K β : Subgroup G} {t : G} {j : Fin (m - 1) → Subgroup G} (hjK : ∀ a, Commutes K (j a))
    (hjΩ : ∀ a : Fin (m - 1), a.val + 2 < m → j a ∈ Ω)
    (hjperf : ∀ a : Fin (m - 1), ¬ a.val + 2 < m → j a ≤ ⁅j a, j a⁆)
    (hjc : ∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u)
    (hjp : ∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b))
    (hjtw : ∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (j a) (j b))
    {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hfix : ∀ a : Fin (m - 1), 1 ≤ a.val → conjSub y (j a) ≤ Subgroup.centralizer ({t} : Set G))
    (hpair0 : ∀ a : Fin (m - 1), a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (conjSub y (j a))) :
    PartnerPatternMinus3 m Ω K β t :=
  ⟨fun a => conjSub y (j a), fun a => commutes_conjSub_of_mem_normalizer hy (hjK a),
    fun a ha => hΩ y _ (hjΩ a ha), fun a ha => conjSub_perfect (hjperf a ha) y, hfix,
    fun a b hab u hu v hv => (Commutes.conjSub (fun x hx y' hy' => hjc a b hab x hx y' hy') y) u hu
      v hv,
    fun a b hab hb => by
      obtain ⟨W, hW⟩ := hjp a b hab hb
      exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW y⟩,
    fun a b ha hb => by
      obtain ⟨W, hW⟩ := hjtw a b ha hb
      exact ⟨_, twistedB2BlockPair_map _ hW (MulAut.conj y).toMonoidHom (MulAut.conj y).injective⟩,
    hpair0⟩


end Base

section Pattern

variable {G : Type} [Group G] [Finite G]

theorem PartnerPatternMinus3.of_locAut {m : ℕ} {Ω : Set (Subgroup G)} {z : G} {K β : Subgroup G}
    (c : TCtx3 .POmegaMinus m Ω K z) {j : Fin (m - 1) → Subgroup G}
    (hjK : ∀ a, Commutes K (j a)) (hjY : ∀ a, j a ≤ locLayer Ω z)
    (hjΩ : ∀ a : Fin (m - 1), a.val + 2 < m → j a ∈ centralizingMembers Ω {z})
    (hjperf : ∀ a : Fin (m - 1), ¬ a.val + 2 < m → j a ≤ ⁅j a, j a⁆)
    (hjc : ∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u)
    (hjp : ∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b))
    (hjtw : ∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (j a) (j b))
    {y : G} (hy : y ∈ locLayer Ω z) {t : G} (ht : t * z * t⁻¹ = z)
    (hfix : ∀ a : Fin (m - 1), 1 ≤ a.val → ∀ x ∈ locImg Ω z (conjSub y (j a)),
      Gaps.locAut c.hΩ.conjInvariant ht x = x)
    (hpair0 : ∀ a : Fin (m - 1), a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (conjSub y (j a))) :
    PartnerPatternMinus3 m Ω K β t := by
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  refine PartnerPatternMinus3.of_conj c.hΩ.conjInvariant hjK (fun a ha => (hjΩ a ha).1)
    hjperf hjc hjp hjtw (c.locLayer_le_normalizer hy) (fun a ha => ?_) hpair0
  by_cases hlong : a.val + 2 < m
  · have hmem : conjSub y (j a) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj c.hΩ.conjInvariant y z
      rw [hyz] at this
      rw [this]
      exact ⟨j a, hjΩ a hlong, rfl⟩
    exact (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht hmem).mpr (hfix a ha)
  · have hN : conjSub y (j a) ≤ locLayer Ω z := by
      rintro _ ⟨u, hu, rfl⟩
      exact (locLayer Ω z).mul_mem ((locLayer Ω z).mul_mem hy (hjY a hu))
        ((locLayer Ω z).inv_mem hy)
    exact (locAut_fixed_iff_of_perfect3 c.hΩ.conjInvariant c.hP1 ht hN
      (conjSub_perfect (hjperf a hlong) y)).mpr (hfix a ha)


end Pattern

end CFSG.ClassicalInvolution.Q3.Q3TY
