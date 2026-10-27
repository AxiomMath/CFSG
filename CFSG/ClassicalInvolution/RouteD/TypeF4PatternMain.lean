module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternPartner
public import CFSG.ClassicalInvolution.RouteD.TypeF4Chain
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternNodes

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock shortBlock longInv form)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def TwinProductP1 (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (z : G) : Prop :=
  ∀ M ∈ Ω, ∀ w : G, IsClassicalMember p f M w → M ≠ K → Commutes K M →
    LocalOddCentral Ω {z * w}

@[expose] def TwinProductNoExotic (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) : Prop :=
  ∀ M ∈ Ω, ∀ w : G, IsClassicalMember p f M w → M ≠ K → Commutes K M →
    ∀ (D : LieSystemData p f (locQuot Ω (z * w)) (locFamily Ω (z * w))) (c : Fin D.card),
      locImg Ω (z * w) K ≤ (D.hom c).range → locImg Ω (z * w) M ≤ (D.hom c).range →
      D.tag c ≠ .G2 ∧ D.tag c ≠ .trialityD4

@[expose] def F4Linked (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (z : G) : Prop :=
  ∀ M ∈ Ω, ∀ w : G, IsClassicalMember p f M w → M ≠ K → Commutes K M →
    ∀ R ∈ centralizingMembers Ω {z * w, z}, Linked Ω (z * w) K R

@[expose] def AdaptedF4 [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {z : G}
    (j : Fin 3 → Subgroup G) {t : G} (ht : t * z * t⁻¹ = z) : Prop :=
  ∃ y ∈ locLayer Ω z, conjSub y (j 0) = j 0 ∧
    (∀ x ∈ locImg Ω z (conjSub y (j 1)), Gaps.locAut hΩ.conjInvariant ht x = x) ∧
    (∀ x ∈ locImg Ω z (conjSub y (j 2)), Gaps.locAut hΩ.conjInvariant ht x = x)

section Main

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem routeD_typeF4_of_twin_data (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : DeltaConnected Ω) (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeC p f 3 Ω z) (hP1 : LocalOddCentral Ω {z}) (hIH : LocalLieSystems p f Ω)
    (hP1x : TwinProductP1 p f Ω K z) (hexc : TwinProductNoExotic p f Ω K z)
    (hlink : F4Linked p f Ω K z) (hTable : F4PerpTableR p f)
    (hTwin : TwinPartnerFactTwin p f .POmegaOdd 4 f)
    (hAdapt : ∀ (d : ShapeCDict p f 3 Ω z) (j : Fin 3 → Subgroup G),
      j 0 ∈ centralizingMembers Ω {z} →
      locImg Ω z (j 0) = (planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))).map d.ψ →
      locImg Ω z (j 1) =
        (shortBlock (GaloisField p f) (by decide : (1 : Fin 3) ≠ 2)).range.map d.ψ →
      locImg Ω z (j 2) =
        (shortBlock (GaloisField p f) (by decide : (0 : Fin 3) ≠ 1)).range.map d.ψ →
      ∀ (N : Subgroup G) (t : G), IsClassicalMember p f N t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K N) →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W N (j 0)) →
        ∀ ht : t * z * t⁻¹ = z, AdaptedF4 hΩ j ht) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .F4 := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict hΩ hK hz hshape
  obtain ⟨j, hj0Ω, hj0z, hj0K, hjK, hj1, hj2, hj02, hj12, hj01, hjY, himg0, himg1, himg2⟩ :=
    exists_nodes_typeF4_img hp2 hq hΩ hK hz hP1 d
  obtain ⟨w₀, hw₀⟩ := hΩ.classical (j 0) hj0Ω
  obtain ⟨Dz, -⟩ := id hshape
  obtain ⟨N, hNx, hKN, hNj⟩ := exists_f4_twin_partner hp2 hq (Gaps.fundNoncentral p) hΩ hex hsingle
    hK hz hP1 hIH Dz d hj0z hj0K himg0 hw₀ (hjK 0) (hP1x _ hj0Ω w₀ hw₀ hj0K (hjK 0))
    (hexc _ hj0Ω w₀ hw₀ hj0K (hjK 0)) hTable hTwin (hlink _ hj0Ω w₀ hw₀ hj0K (hjK 0))
  have hNΩ : N ∈ Ω := hNx.1
  obtain ⟨t, ht⟩ := hΩ.classical N hNΩ
  have htz : t * z * t⁻¹ = z := by
    obtain ⟨W, hW⟩ := hKN
    have hzt : z * t = t * z := standardPair_involutions_commute h2 hW hz.mem ht.mem
      hz.orderOf_eq_two ht.orderOf_eq_two
    rw [mul_inv_eq_iff_eq_mul]
    exact hzt.symm
  obtain ⟨y, hy, hyj0, hfix1, hfix2⟩ := hAdapt d j hj0z himg0 himg1 himg2 N t ht hKN hNj htz
  have hpat : PartnerPatternF4 p f Ω K N t := by
    refine PartnerPatternF4.of_locAut hq hΩ hex hK hz hP1 d hj0Ω hjK hj1 hj2 hjY hj02 hj12 hj01 hy
      htz hfix1 hfix2 ?_
    rw [hyj0]
    exact hNj
  exact routeD_typeF4_of_pattern hp2 hq (Gaps.fundNoncentral p)
    (standardPairAutAbelian_galoisField hp2 hq) hΩ hK hsingle hconn hz hshape hP1 hNΩ ht hKN hpat

end Main

end CFSG.ClassicalInvolution.RouteD.NonClassical
