module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDNodes
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDMain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub InClass IsClassicalMember LocalOddCentral
  ExactMembers centralizingMembers LieSystemData ConjInvariant centralizingLayer_le_centralizer)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def PartnerPatternMinus (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (K β : Subgroup G) (t : G) : Prop :=
  ∃ j : Fin (m - 1) → Subgroup G, (∀ a, Commutes K (j a)) ∧ (∀ a, ⁅j a, j a⁆ = j a) ∧
    (∀ a : Fin (m - 1), a.val + 2 < m → j a ∈ Ω) ∧
    (∀ a : Fin (m - 1), 1 ≤ a.val → j a ≤ Subgroup.centralizer ({t} : Set G)) ∧
    (∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u) ∧
    (∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
    (∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (j a) (j b)) ∧
    (∀ a : Fin (m - 1), a.val = 0 → ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j a))

theorem PartnerPatternMinus.of_conj {m : ℕ} {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K β : Subgroup G} {t : G} {j : Fin (m - 1) → Subgroup G} (hjK : ∀ a, Commutes K (j a))
    (hjperf : ∀ a, ⁅j a, j a⁆ = j a) (hjΩ : ∀ a : Fin (m - 1), a.val + 2 < m → j a ∈ Ω)
    (hjc : ∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u)
    (hjp : ∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hjtw : ∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (j a) (j b))
    {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hfix : ∀ a : Fin (m - 1), 1 ≤ a.val → conjSub y (j a) ≤ Subgroup.centralizer ({t} : Set G))
    (hpair0 : ∀ a : Fin (m - 1), a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j a))) :
    PartnerPatternMinus p f m Ω K β t :=
  ⟨fun a => conjSub y (j a), fun a => commutes_conjSub_of_mem_normalizer hy (hjK a),
    fun a => le_antisymm (commutator_self_le _) (conjSub_perfect (hjperf a).ge y),
    fun a ha => hΩ y _ (hjΩ a ha), hfix,
    fun a b hab u hu v hv => (Commutes.conjSub (fun x hx y' hy' => hjc a b hab x hx y' hy') y) u hu
      v hv,
    fun a b hab hb => by
      obtain ⟨W, hW⟩ := hjp a b hab hb
      exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW y⟩,
    fun a b ha hb => by
      obtain ⟨W, hW⟩ := hjtw a b ha hb
      exact ⟨_, twistedB2BlockPair_map _ hW (MulAut.conj y).toMonoidHom (MulAut.conj y).injective⟩,
    hpair0⟩

theorem PartnerPatternMinus.of_locAut [Finite G] {m : ℕ} {Ω : Set (Subgroup G)} {z : G}
    {K β : Subgroup G} (c : TCtx p f .POmegaMinus m Ω K z) {j : Fin (m - 1) → Subgroup G}
    (hjK : ∀ a, Commutes K (j a)) (hjperf : ∀ a, ⁅j a, j a⁆ = j a)
    (hjY : ∀ a, j a ≤ locLayer Ω z) (hjΩ : ∀ a : Fin (m - 1), a.val + 2 < m → j a ∈ Ω)
    (hjc : ∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u)
    (hjp : ∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hjtw : ∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (j a) (j b))
    {y : G} (hy : y ∈ locLayer Ω z) {t : G} (ht : t * z * t⁻¹ = z)
    (hfix : ∀ a : Fin (m - 1), 1 ≤ a.val → ∀ x ∈ locImg Ω z (conjSub y (j a)),
      Gaps.locAut c.hΩ.conjInvariant ht x = x)
    (hpair0 : ∀ a : Fin (m - 1), a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j a))) :
    PartnerPatternMinus p f m Ω K β t := by
  refine PartnerPatternMinus.of_conj c.hΩ.conjInvariant hjK hjperf hjΩ hjc hjp hjtw
    (c.locLayer_le_normalizer hy) (fun a ha => ?_) hpair0
  have hN : conjSub y (j a) ≤ locLayer Ω z := by
    rintro _ ⟨u, hu, rfl⟩
    exact (locLayer Ω z).mul_mem ((locLayer Ω z).mul_mem hy (hjY a hu))
      ((locLayer Ω z).inv_mem hy)
  exact (locAut_fixed_iff_of_perfect c.hΩ c.hP1 ht hN
    (conjSub_perfect (hjperf a).ge y)).mpr (hfix a ha)

theorem routeD_typeTwistedD_of_pattern [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) (hMFZ : Gaps.FundNoncentral p)
    (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {n : ℕ} (hn : 6 ≤ n)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    {z : G} (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeT p f 2 .POmegaMinus (n - 2) Ω z) (hP1 : LocalOddCentral Ω {z})
    (hpat : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) → HasFixedMember Ω K β z →
      PartnerPatternMinus p f (n - 2) Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaMinus ∧ D.rank i = n := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus (n - 2) p f :=
    ⟨Fact.out, hf, by show 4 ≤ n - 2; omega⟩
  obtain ⟨c⟩ := TCtx.nonempty_minus (m := n - 2) (by omega) hp2 hq hΩ hex hK hz hP1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_minus (by omega) hp2 hadm hsingle hshape
  obtain ⟨j, hjK, hjperf, -, hjt, hjc, hjp, hjtw, hβj⟩ := hpat β hβ t ht hKβ hfix
  exact routeD_typeTwistedD hp2 hq hn hg6 hMFZ hS3 hΩ hK hsingle hconn hz hshape hP1 hβ ht hKβ j
    hjK (fun a _ => hjperf a) hjt hjc hjp hjtw (hβj ⟨0, by omega⟩ rfl)

end CFSG.ClassicalInvolution.RouteD
