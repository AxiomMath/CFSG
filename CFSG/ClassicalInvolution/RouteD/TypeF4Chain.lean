module

public import CFSG.ClassicalInvolution.RouteD.TypeF4Nodes
public import CFSG.ClassicalInvolution.RouteD.TypeF4Main
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
public import CFSG.ClassicalInvolution.ModelFacts.StandardPair

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  symplecticBlockStandardPair_map)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def PartnerPatternF4 (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (K β : Subgroup G) (t : G) : Prop :=
  ∃ j : Fin 3 → Subgroup G, j 0 ∈ Ω ∧ (∀ i, Commutes K (j i)) ∧ ⁅j 1, j 1⁆ = j 1 ∧
    ⁅j 2, j 2⁆ = j 2 ∧ j 1 ≤ Subgroup.centralizer ({t} : Set G) ∧
    j 2 ≤ Subgroup.centralizer ({t} : Set G) ∧ Commutes (j 0) (j 2) ∧
    (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 1) (j 2)) ∧
    (∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j 0) (j 1)) ∧
    (∃ W, LinearBlockStandardPair (GaloisField p f) W β (j 0))

theorem PartnerPatternF4.of_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K β : Subgroup G} {t : G} {j : Fin 3 → Subgroup G} (hj0 : j 0 ∈ Ω)
    (hjK : ∀ i, Commutes K (j i)) (hj1 : ⁅j 1, j 1⁆ = j 1) (hj2 : ⁅j 2, j 2⁆ = j 2)
    (hj02 : Commutes (j 0) (j 2))
    (hj12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (j 1) (j 2))
    (hj01 : ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j 0) (j 1)) {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hfix1 : conjSub y (j 1) ≤ Subgroup.centralizer ({t} : Set G))
    (hfix2 : conjSub y (j 2) ≤ Subgroup.centralizer ({t} : Set G))
    (hpair0 : ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j 0))) :
    PartnerPatternF4 p f Ω K β t := by
  refine ⟨fun i => conjSub y (j i), hΩ y _ hj0, fun i => commutes_conjSub_of_mem_normalizer hy
    (hjK i), le_antisymm (commutator_self_le _) (conjSub_perfect hj1.ge y),
    le_antisymm (commutator_self_le _) (conjSub_perfect hj2.ge y), hfix1, hfix2,
    hj02.conjSub y, ?_, ?_, hpair0⟩
  · obtain ⟨W, hW⟩ := hj12
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW y⟩
  · obtain ⟨W, hW⟩ := hj01
    exact ⟨_, symplecticBlockStandardPair_map hW (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective⟩

theorem PartnerPatternF4.of_locAut [Finite G] (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f 3 Ω z)
    {β : Subgroup G} {j : Fin 3 → Subgroup G} (hj0 : j 0 ∈ Ω) (hjK : ∀ i, Commutes K (j i))
    (hj1 : ⁅j 1, j 1⁆ = j 1) (hj2 : ⁅j 2, j 2⁆ = j 2) (hjY : ∀ i, j i ≤ locLayer Ω z)
    (hj02 : Commutes (j 0) (j 2))
    (hj12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (j 1) (j 2))
    (hj01 : ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j 0) (j 1)) {y : G}
    (hy : y ∈ locLayer Ω z) {t : G} (ht : t * z * t⁻¹ = z)
    (hfix1 : ∀ x ∈ locImg Ω z (conjSub y (j 1)), Gaps.locAut hΩ.conjInvariant ht x = x)
    (hfix2 : ∀ x ∈ locImg Ω z (conjSub y (j 2)), Gaps.locAut hΩ.conjInvariant ht x = x)
    (hpair0 : ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j 0))) :
    PartnerPatternF4 p f Ω K β t := by
  have hnorm : y ∈ Subgroup.normalizer (K : Set G) := by
    have hle : locLayer Ω z ≤ Subgroup.normalizer (K : Set G) := by
      refine iSup₂_le fun L hL => ?_
      by_cases hLK : L = K
      · subst hLK
        exact Subgroup.le_normalizer
      · refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer (K : Set G))
        exact Subgroup.mem_centralizer_iff.mpr fun k hk =>
          typeC_commutes_K_of_ne (by norm_num) hq hΩ hex hK hz hP1 d hL hLK k hk x hx
    exact hle hy
  have hN : ∀ i, conjSub y (j i) ≤ locLayer Ω z := fun i => by
    rintro _ ⟨u, hu, rfl⟩
    exact (locLayer Ω z).mul_mem ((locLayer Ω z).mul_mem hy (hjY i hu)) ((locLayer Ω z).inv_mem hy)
  refine PartnerPatternF4.of_conj hΩ.conjInvariant hj0 hjK hj1 hj2 hj02 hj12 hj01 hnorm ?_ ?_ hpair0
  · exact (locAut_fixed_iff_of_perfect hΩ hP1 ht (hN 1) (conjSub_perfect hj1.ge y)).mpr hfix1
  · exact (locAut_fixed_iff_of_perfect hΩ hP1 ht (hN 2) (conjSub_perfect hj2.ge y)).mpr hfix2

theorem routeD_typeF4_of_pattern [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeC p f 3 Ω z)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hpat : PartnerPatternF4 p f Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .F4 := by
  obtain ⟨j, -, hjK, hj₁, hj₂, hjt₁, hjt₂, hj₀₂, hj₁₂, hj₀₁, hβj₀⟩ := hpat
  exact routeD_typeF4 hp2 hq hMFZ hS3 hΩ hK hsingle hconn hz hshape hP1 hβ ht hKβ j hjK hj₁ hj₂
    hjt₁ hjt₂ hj₀₂ hj₁₂ hj₀₁ hβj₀

end CFSG.ClassicalInvolution.RouteD
