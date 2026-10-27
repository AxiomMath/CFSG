module

public import CFSG.ClassicalInvolution.Q3.Q3TD3Chain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3.exists_nodes_plus3 {m : ℕ} (hm : 4 ≤ m)
    (c : TCtx3 .POmegaPlus m Ω K z)
    (e : Fin (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rank ≃ Fin m)
    (he : ∀ a b, (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.cartan a b =
      cartanD m (e a) (e b)) :
    ∃ j : Fin (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rank → Subgroup G,
      (∀ a, j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧ ¬ locImg Ω z (j a) ≤ c.d.Q₁) ∧
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ) ∧
      (∀ a, Commutes K (j a)) ∧
      (∀ a b, a ≠ b → ¬ edgeD m (e a) (e b) → ¬ edgeD m (e b) (e a) → Commutes (j a) (j b)) ∧
      (∀ a b, edgeD m (e a) (e b) → ∃ W : Subgroup G,
        LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b)) := by
  have hm3 : 3 ≤ m := by omega
  have hR : ∀ a, rankOne (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup a ∈
      fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D := by
    rw [modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3]
    exact fun a => rankOne_mem_fundamentalSubgroups_plusDatum hm3 a
  have hcomm : ∀ a b : Fin (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rank,
      (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.cartan a b = 0 →
      Commutes (rankOne (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup a)
        (rankOne (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup b) := by
    rw [modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3]
    exact fun a b h => commutes_rankOne_plusDatum hm3 h
  have hstd : ∀ a b : Fin (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rank,
      (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.cartan a b = -1 →
      ∃ W : Subgroup (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K,
        LinearBlockStandardPair (GaloisField 3 1) W
          (rankOne (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup a)
          (rankOne (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup b) := by
    rw [modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3]
    exact fun a b h => standardPair_plusDatum_of_cartan hm3 h
  have heinj : ∀ a b, a ≠ b → e a ≠ e b := fun a b hab h => hab (e.injective h)
  obtain ⟨j, hj, hjc, hjp, hjK⟩ := c.exists_nodes_gen3
    (fun a => rankOne (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.rootGroup a) hR
    (fun a b => edgeD m (e a) (e b))
    (fun a b hab h1 h2 => hcomm a b (by rw [he]; exact (LevisSpin.cartanD_of_not_edgeD
      (heinj a b hab) h1 h2).1))
    (fun a b h => hstd a b (by rw [he]; exact (LevisSpin.cartanD_of_edgeD h).1))
  exact ⟨j, fun a => ⟨(hj a).1, (hj a).2.1, (hj a).2.2.1⟩, fun a => (hj a).2.2.2, hjK, hjc, hjp⟩

theorem PartnerPatternPlus3.of_conj {m : ℕ} {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K β : Subgroup G} {t : G} {j : Fin m → Subgroup G} (hjΩ : ∀ a, j a ∈ Ω)
    (hjK : ∀ a, Commutes K (j a))
    (hjc : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (j a) (j b))
    (hjp : ∀ a b, edgeD m a b → ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b))
    {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hfix : ∀ a : Fin m, 1 ≤ a.val → conjSub y (j a) ≤ Subgroup.centralizer ({t} : Set G))
    (hpair0 : ∀ a : Fin m, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (conjSub y (j a))) :
    PartnerPatternPlus3 m Ω K β t :=
  PartnerPatternD.of_conj hΩ hjΩ hjK hjc hjp hy hfix hpair0

theorem PartnerPatternPlus3.of_locAut {m : ℕ} {Ω : Set (Subgroup G)} {z : G} {K β : Subgroup G}
    (c : TCtx3 .POmegaPlus m Ω K z) {j : Fin m → Subgroup G}
    (hj : ∀ a, j a ∈ centralizingMembers Ω {z}) (hjK : ∀ a, Commutes K (j a))
    (hjc : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (j a) (j b))
    (hjp : ∀ a b, edgeD m a b → ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b))
    {y : G} (hy : y ∈ locLayer Ω z) {t : G} (ht : t * z * t⁻¹ = z)
    (hfix : ∀ a : Fin m, 1 ≤ a.val → ∀ x ∈ locImg Ω z (conjSub y (j a)),
      Gaps.locAut c.hΩ.conjInvariant ht x = x)
    (hpair0 : ∀ a : Fin m, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (conjSub y (j a))) :
    PartnerPatternPlus3 m Ω K β t := by
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  refine PartnerPatternPlus3.of_conj c.hΩ.conjInvariant (fun a => (hj a).1) hjK hjc hjp
    (c.locLayer_le_normalizer hy) (fun a ha => ?_) hpair0
  have hmem : conjSub y (j a) ∈ centralizingMembers Ω {z} := by
    have := centralizingMembers_conj c.hΩ.conjInvariant y z
    rw [hyz] at this
    rw [this]
    exact ⟨j a, hj a, rfl⟩
  exact (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht hmem).mpr (hfix a ha)

end Nodes

end CFSG.ClassicalInvolution.Q3.Q3TD
