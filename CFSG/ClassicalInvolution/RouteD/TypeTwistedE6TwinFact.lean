module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.RouteD.NonClassicalLocal

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def TwinPartnerFactTwin (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
    ∀ R' ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R ≠ R' → Commutes R R' →
      (∃ r ∈ R, r ≠ 1 ∧ ∃ r' ∈ R', r' ≠ 1 ∧ ∀ y : (modelUniv t n p e Fact.out).K,
        r * r' * y * (r * r')⁻¹ * y⁻¹ ∈ Subgroup.center (modelUniv t n p e Fact.out).K) →
      ∃ R'' ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
        (∃ W, LinearBlockStandardPair (GaloisField p f) W R R'') ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W R'' R'

section Partner

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem ne_one_of_hom_eq_locMk {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card} {z : G} (hz : z ∈ locLayer Ω x) (hz2 : orderOf z = 2)
    {k : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hk : D.hom i k = locMk Ω x ⟨z, hz⟩) : k ≠ 1 := by
  rintro rfl
  set zY : ↥(locLayer Ω x) := ⟨z, hz⟩ with hzYdef
  have hzY : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := by
    rw [← QuotientGroup.eq_one_iff]
    exact hk.symm.trans (map_one _)
  have h2 : orderOf zY = 2 := by
    rw [hzYdef, Subgroup.orderOf_mk]
    exact hz2
  have h3 : orderOf (⟨zY, hzY⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  have h4 := orderOf_dvd_natCard (⟨zY, hzY⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
  rw [h3] at h4
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
    (even_iff_two_dvd.mpr h4)

theorem exists_twin_partner_of_twin (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hTwin : TwinPartnerFactTwin p f (D.tag i) (D.rank i) (D.exp i))
    {K M : Subgroup G} (hK : K ∈ compMembers Ω x D i) (hM : M ∈ compMembers Ω x D i) (hKM : K ≠ M)
    (hcomm : Commutes K M) {z w : G} (hz : z ∈ K) (hw : w ∈ M) (hz2 : orderOf z = 2)
    (hw2 : orderOf w = 2) (hx : z * w = x) :
    ∃ N ∈ compMembers Ω x D i,
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K N) ∧
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W N M := by
  obtain ⟨R, hR⟩ := exists_corr_left hΩ hex D hK
  obtain ⟨R', hR'⟩ := exists_corr_left hΩ hex D hM
  obtain ⟨k, hkR, hk⟩ := exists_model_elt hR hz
  obtain ⟨k', hkR', hk'⟩ := exists_model_elt hR' hw
  have hne : R ≠ R' := by
    rintro rfl
    exact hKM (corr_unique_right hΩ hP1 hR hR')
  have hcR : Commutes R R' := (corr_commutes hΩ hP1 hperf hR hR').mp hcomm
  have hKY : z ∈ locLayer Ω x := le_centralizingLayer hK.1 hz
  have hMY : w ∈ locLayer Ω x := le_centralizingLayer hM.1 hw
  have hcentral : ∀ a : locQuot Ω x, locMk Ω x ⟨z, hKY⟩ * locMk Ω x ⟨w, hMY⟩ * a =
      a * (locMk Ω x ⟨z, hKY⟩ * locMk Ω x ⟨w, hMY⟩) := by
    intro a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← map_mul]
    show QuotientGroup.mk' _ (_ * y) = QuotientGroup.mk' _ (y * _)
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {x} y.2)
    show z * w * (y : G) = (y : G) * (z * w)
    rw [hx]
    exact this.symm
  obtain ⟨R'', hR''fund, hp1, hp2⟩ := hTwin R hR.2.1 R' hR'.2.1 hne hcR
    ⟨k, hkR, ne_one_of_hom_eq_locMk hKY hz2 hk, k', hkR', ne_one_of_hom_eq_locMk hMY hw2 hk',
      fun y => by
        apply D.ker_le_center i
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hk, hk']
        rw [hcentral (D.hom i y)]
        group⟩
  obtain ⟨N, hN⟩ := exists_corr_right hΩ D hsc hR''fund
  have hNc : N ∈ compMembers Ω x D i := ⟨hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩
  exact ⟨N, hNc, linearBlockStandardPair_of_corr hq hΩ hP1 hR hN hp1,
    linearBlockStandardPair_of_corr hq hΩ hP1 hN hR' hp2⟩

end Partner

end CFSG.ClassicalInvolution.RouteD.NonClassical
