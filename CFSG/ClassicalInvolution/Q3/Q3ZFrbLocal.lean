module

public import CFSG.ClassicalInvolution.Q3.Q3ZFrbModel
public import CFSG.ClassicalInvolution.Q3.Q3ZLiftLayer
public import CFSG.ClassicalInvolution.Q3.Q3WARoot

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane)
open CFSG.ClassicalInvolution.Q3.Q3W (LocalOddThreeFree3)
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups commutatorElement

section Central

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}

theorem mk_eq_one_of_plane_central (d : ShapeCDict3 Ω z)
    {P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1)} (hP : IsHyperbolicPlane P)
    {y : ↥(locLayer Ω z)}
    (hy : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) y ∈
      (planeGroup P).map d.ψ)
    (hcentral : ∀ w : locQuot Ω z,
      w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) y =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) y * w) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) y = 1 := by
  obtain ⟨r, hrP, hr⟩ := hy
  have hrc : r ∈ Subgroup.center (StatedSp 2 (GaloisField 3 1)) := by
    refine Models.SymplecticPairs.mem_center_of_forall_commutator_mem_center isPerfect_sp4_three
      fun s => d.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hr]
    rw [commutatorElement_def, ← hcentral (d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
  rw [← hr, planeGroup_central_eq_one hP hrP hrc, map_one]

theorem false_of_involution_mem_plane_member [Finite G] (d : ShapeCDict3 Ω z) {L : Subgroup G}
    (hL : L ≤ locLayer Ω z) (hzL : z ∈ L) (hz2 : orderOf z = 2)
    {P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1)} (hP : IsHyperbolicPlane P)
    (hLP : locImg Ω z L = (planeGroup P).map d.ψ) : False := by
  let zY : ↥(locLayer Ω z) := ⟨z, hL hzL⟩
  have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY ∈
      locImg Ω z L := ⟨zY, Subgroup.mem_subgroupOf.mpr hzL, rfl⟩
  rw [hLP] at hzK
  have hcentral : ∀ w : locQuot Ω z,
      w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY * w := by
    intro w
    obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} w'.2)
  have h1 := mk_eq_one_of_plane_central d hP hzK hcentral
  have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
    (QuotientGroup.eq_one_iff _).mp h1
  have h2 : orderOf zY = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hz2
  have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
  have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  rw [h4] at h3
  have := CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z))
  exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)

theorem ne_of_commutes_member {L M : Subgroup G} (hΩ : Q3.InClass3 Ω) (hL : L ∈ Ω)
    (h : Commutes L M) : L ≠ M := by
  rintro rfl
  obtain ⟨w, hw⟩ := hΩ.classical L hL
  exact Q3W.not_commutes_self3 hw h

end Central

section Members

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}

structure CCore3 {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) where
  hΩ : Q3.InClass3 Ω
  hex : Q3.ExactMembers3 Ω
  hK : K ∈ Ω
  hz : Q3.IsClassicalMember3 K z
  hP1 : LocalOddCentral Ω {z}
  hO3 : LocalOddThreeFree3 Ω z
  d : ShapeCDict3 Ω z

namespace CCore3

variable [Finite G] {K : Subgroup G} (c : CCore3 Ω K z)

include c

omit [Finite G] in
theorem hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, isSubnormal_le c.hz.subnormal⟩

theorem locImg_self_le_Q₀ : locImg Ω z K ≤ c.d.Q₀ := by
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, c.hKz, rfl⟩
  rcases c.d.fam_cases _ hmem with h | ⟨P, hP, hPK⟩
  · exact h
  · exact (false_of_involution_mem_plane_member c.d (le_centralizingLayer c.hKz) c.hz.mem
      c.hz.orderOf_eq_two hP hPK).elim

theorem eq_of_locImg_le_Q₀ {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLQ : locImg Ω z L ≤ c.d.Q₀) : L = K := by
  have hKQ := c.locImg_self_le_Q₀
  have hcL := Q3W.card_locImg3 c.hΩ c.hex hL
  have hcK := Q3W.card_locImg3 c.hΩ c.hex c.hKz
  have hcard := c.d.card_le
  rw [Q3W.card_sl2_gf3] at hcard
  have e1 : locImg Ω z L = c.d.Q₀ := Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact hcard)
  have e2 : locImg Ω z K = c.d.Q₀ := Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcK]; exact hcard)
  exact Q3W.locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL c.hKz (e1.trans e2.symm)

theorem exists_plane_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    ∃ P, IsHyperbolicPlane P ∧ locImg Ω z L = (planeGroup P).map c.d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases c.d.fam_cases _ hmem with h | h
  · exact absurd (c.eq_of_locImg_le_Q₀ hL h) hLK
  · exact h

theorem commutes_K_of_plane {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    {P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1)}
    (hLP : locImg Ω z L = (planeGroup P).map c.d.ψ) : Commutes K L := by
  refine Q3W.commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 c.hKz hL ?_
  intro a ha b hb
  rw [hLP] at hb
  obtain ⟨r, -, rfl⟩ := hb
  exact (c.d.commutes (c.d.ψ r) ⟨r, rfl⟩ a (c.locImg_self_le_Q₀ ha)).symm

end CCore3

structure Layer3 [Finite G] {K : Subgroup G} (c : CCore3 Ω K z) where
  Θ : StatedSp 2 (GaloisField 3 1) →* G
  mem : ∀ g, Θ g ∈ locLayer Ω z
  ker_le : Θ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField 3 1))
  comp_eq : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))).comp
    (Θ.codRestrict (locLayer Ω z) mem) = c.d.ψ
  plane : ∀ P, IsHyperbolicPlane P → (planeGroup P).map Θ ∈ centralizingMembers Ω {z} ∧
    locImg Ω z ((planeGroup P).map Θ) = (planeGroup P).map c.d.ψ

theorem CCore3.nonempty_layer [Finite G] {K : Subgroup G} (c : CCore3 Ω K z) :
    Nonempty (Layer3 c) := by
  obtain ⟨Θ, hΘ, hker, hcomp, hpl⟩ := exists_layer_lift c.hΩ c.hex c.hP1 c.hO3 c.d
  exact ⟨⟨Θ, hΘ, hker, hcomp, hpl⟩⟩

namespace Layer3

variable [Finite G] {K : Subgroup G} {c : CCore3 Ω K z} (l : Layer3 c)

include l

theorem eq_member {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    {P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1)} (hP : IsHyperbolicPlane P)
    (hLP : locImg Ω z L = (planeGroup P).map c.d.ψ) : L = (planeGroup P).map l.Θ :=
  Q3W.locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL (l.plane P hP).1 (hLP.trans (l.plane P hP).2.symm)

theorem exists_plane_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    ∃ P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1),
      IsHyperbolicPlane P ∧ L = (planeGroup P).map l.Θ := by
  obtain ⟨P, hP, hLP⟩ := c.exists_plane_of_ne hL hLK
  exact ⟨P, hP, l.eq_member hL hP hLP⟩

theorem commutes_K (s : StatedSp 2 (GaloisField 3 1)) {k : G} (hk : k ∈ K) :
    l.Θ s * k = k * l.Θ s := by
  set Y := locLayer Ω z with hY
  let A : Subgroup ↥Y := (l.Θ.codRestrict Y l.mem).range
  let B : Subgroup ↥Y := K.subgroupOf Y
  have hperf : ⁅(⊤ : Subgroup (StatedSp 2 (GaloisField 3 1))),
      (⊤ : Subgroup (StatedSp 2 (GaloisField 3 1)))⁆ = ⊤ := by
    have := Group.isPerfect_def.1 isPerfect_sp4_three
    rwa [commutator_def] at this
  have hA : A ≤ ⁅A, A⁆ := by
    have h1 : A = (⊤ : Subgroup (StatedSp 2 (GaloisField 3 1))).map (l.Θ.codRestrict Y l.mem) :=
      MonoidHom.range_eq_map _
    rw [h1, ← Subgroup.map_commutator, hperf]
  have hc : ⁅A, B⁆ ≤ Subgroup.center ↥Y := by
    rw [Subgroup.commutator_le]
    rintro a ⟨s', rfl⟩ b hb
    have hO : ⁅l.Θ.codRestrict Y l.mem s', b⁆ ∈ classicalInvolutionOddCore ↥Y := by
      rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥Y)]
      change QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⁅_, b⁆ = 1
      rw [map_commutatorElement,
        show QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (l.Θ.codRestrict Y l.mem s') =
          c.d.ψ s' from DFunLike.congr_fun l.comp_eq s', commutatorElement_eq_one_iff_mul_comm]
      exact c.d.commutes (c.d.ψ s') ⟨s', rfl⟩ _ (c.locImg_self_le_Q₀ ⟨b, hb, rfl⟩)
    exact c.hP1 hO
  have h0 := Models.SymplecticPairs.commutator_eq_bot_of_perfect hA hc
  have hmem : ⁅(⟨l.Θ s, l.mem s⟩ : ↥Y), (⟨k, le_centralizingLayer c.hKz hk⟩ : ↥Y)⁆ ∈ ⁅A, B⁆ :=
    Subgroup.commutator_mem_commutator ⟨s, rfl⟩ (Subgroup.mem_subgroupOf.mpr hk)
  rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact congrArg Subtype.val hmem

theorem commutes_K_map (R : Subgroup (StatedSp 2 (GaloisField 3 1))) : Commutes K (R.map l.Θ) := by
  rintro k hk _ ⟨r, -, rfl⟩
  exact (l.commutes_K r hk).symm

theorem map_planeGroup_ne {P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1)} :
    (planeGroup P).map l.Θ ≠ K := fun h =>
  ne_of_commutes_member c.hΩ c.hK (l.commutes_K_map (planeGroup P)) (h.symm)

end Layer3

end Members

end CFSG.ClassicalInvolution.Q3.Q3Z
