module

public import CFSG.ClassicalInvolution.Q3.Q3TPCtx
public import CFSG.ClassicalInvolution.Q3.Q3ZLiftLayer
public import CFSG.ClassicalInvolution.RouteD.GapsAut
public import CFSG.ClassicalInvolution.Q3.Q3TCCtx
public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3WAETLocal
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TPS

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane longBlock
  mem_fundamentalSubgroups_PSp_iff)
open CFSG.ClassicalInvolution.Q3.Q3W (LocalOddThreeFree3 Pow3 card_gf3 pow3_range_sl2
  eq_of_map_eq_of_pow3 pow_three_mem_commutator_of_equiv)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (exists_lift_of_noCover)
open CFSG.ClassicalInvolution.Q3.Q3Z (isPerfect_sp4_three sp4_three_noCover pow3_planeGroup)
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Q3.Q3TP (TCtxS3)
open scoped MatrixGroups commutatorElement

local notation "F₃" => GaloisField 3 1

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}


theorem exists_layer_liftS (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) (hP1 : LocalOddCentral Ω {z})
    (hO3 : LocalOddThreeFree3 Ω z) (ψ : StatedSp 2 F₃ →* locQuot Ω z)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F₃))
    (hmem : ∀ P, IsHyperbolicPlane P → (planeGroup P).map ψ ∈ locFamily Ω z) :
    ∃ (Θ : StatedSp 2 F₃ →* G) (hΘ : ∀ g, Θ g ∈ locLayer Ω z),
      Θ.ker ≤ Subgroup.center (StatedSp 2 F₃) ∧
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))).comp
        (Θ.codRestrict (locLayer Ω z) hΘ) = ψ ∧
      ∀ P, IsHyperbolicPlane P → (planeGroup P).map Θ ∈ centralizingMembers Ω {z} ∧
        locImg Ω z ((planeGroup P).map Θ) = (planeGroup P).map ψ := by
  set O := classicalInvolutionOddCore ↥(locLayer Ω z) with hOdef
  have hker0 : (QuotientGroup.mk' O).ker ≤ Subgroup.center ↥(locLayer Ω z) := by
    rw [QuotientGroup.ker_mk']
    exact hP1
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card _
  have hcop : ∀ w ∈ (QuotientGroup.mk' O).ker, ¬ 3 ∣ orderOf w := by
    intro w hw h
    rw [QuotientGroup.ker_mk'] at hw
    exact hO3 (h.trans (Subgroup.orderOf_dvd_natCard O hw))
  have : Group.IsPerfect (StatedSp 2 F₃) := isPerfect_sp4_three
  have hdiv : ∀ m n : ℕ, m ∣ n → (Odd n ∧ ¬ 3 ∣ n) → (Odd m ∧ ¬ 3 ∣ m) :=
    fun m n hmn ⟨ho, hn⟩ => ⟨ho.of_dvd_nat hmn, fun h => hn (h.trans hmn)⟩
  obtain ⟨β, hβ⟩ := exists_lift_of_noCover (Q := fun n => Odd n ∧ ¬ 3 ∣ n) hdiv sp4_three_noCover
    (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O) hker0
    (by rw [QuotientGroup.ker_mk']; exact ⟨hOodd, hO3⟩) ψ
  have hβ' : ∀ g, QuotientGroup.mk' O (β g) = ψ g := fun g => DFunLike.congr_fun hβ g
  have hΘ : ∀ g, ((locLayer Ω z).subtype.comp β) g ∈ locLayer Ω z := fun g => (β g).2
  have hcodRestrict : ((locLayer Ω z).subtype.comp β).codRestrict (locLayer Ω z) hΘ = β :=
    MonoidHom.ext fun g => Subtype.ext rfl
  refine ⟨(locLayer Ω z).subtype.comp β, hΘ, ?_, by rw [hcodRestrict]; exact hβ, ?_⟩
  · intro g hg
    apply hker
    have h1 : β g = 1 := Subtype.ext (MonoidHom.mem_ker.mp hg)
    rw [MonoidHom.mem_ker, ← hβ', h1, map_one]
  · intro P hP
    obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (hmem P hP)
    have hLY : L ≤ locLayer Ω z := le_centralizingLayer hL
    have hA : Pow3 ((planeGroup P).map β) := (pow3_planeGroup hP).map β
    have hB : Pow3 (L.subgroupOf (locLayer Ω z)) := by
      obtain ⟨zL, hzL⟩ := hΩ.classical L hL.1
      obtain ⟨e⟩ := hzL.nonempty_equiv_sl2 (hex L hL.1)
      exact pow_three_mem_commutator_of_equiv (Nat.card_zmod 3)
        ((Subgroup.subgroupOfEquivOfLe hLY).trans e)
    have hAB : ((planeGroup P).map β).map (QuotientGroup.mk' O) =
        (L.subgroupOf (locLayer Ω z)).map (QuotientGroup.mk' O) := by
      rw [Subgroup.map_map, hβ]
      exact hLR.symm
    have hEq := eq_of_map_eq_of_pow3 (QuotientGroup.mk' O) hker0 hcop hA hB hAB
    have hmap : (planeGroup P).map ((locLayer Ω z).subtype.comp β) = L := by
      rw [← Subgroup.map_map, hEq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLY]
    rw [hmap]
    exact ⟨hL, hLR⟩

structure LayerS3 {K : Subgroup G} (c : TCtxS3 .PSp 2 Ω K z) where
  Θ : StatedSp 2 F₃ →* G
  mem : ∀ g, Θ g ∈ locLayer Ω z
  ker_le : Θ.ker ≤ Subgroup.center (StatedSp 2 F₃)
  comp_eq : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))).comp
    (Θ.codRestrict (locLayer Ω z) mem) = c.d.ψ
  plane : ∀ P, IsHyperbolicPlane P → (planeGroup P).map Θ ∈ centralizingMembers Ω {z} ∧
    locImg Ω z ((planeGroup P).map Θ) = (planeGroup P).map c.d.ψ

theorem nonempty_layerS3 {K : Subgroup G} (c : TCtxS3 .PSp 2 Ω K z) : Nonempty (LayerS3 c) := by
  have hadmP := Q3Z.statedLieAdmissible_psp2
  obtain ⟨Θ, hΘ, hker, hcomp, hpl⟩ := exists_layer_liftS c.hΩ c.hex c.hP1 c.hO3 c.d.ψ c.d.ker_le
    (fun P hP => c.d.mem_fam _ ((mem_fundamentalSubgroups_PSp_iff hadmP _).mpr ⟨P, hP, rfl⟩))
  exact ⟨⟨Θ, hΘ, hker, hcomp, hpl⟩⟩

namespace LayerS3

variable {K : Subgroup G} {c : TCtxS3 .PSp 2 Ω K z} (l : LayerS3 c)

include l

theorem eq_member {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    {P : Submodule F₃ (Fin 2 ⊕ Fin 2 → F₃)} (hP : IsHyperbolicPlane P)
    (hLP : locImg Ω z L = (planeGroup P).map c.d.ψ) : L = (planeGroup P).map l.Θ :=
  c.eq_of_locImg_eq hL (l.plane P hP).1 (hLP.trans (l.plane P hP).2.symm)

theorem commutes_K (s : StatedSp 2 F₃) {k : G} (hk : k ∈ K) : l.Θ s * k = k * l.Θ s := by
  set Y := locLayer Ω z with hY
  let A : Subgroup ↥Y := (l.Θ.codRestrict Y l.mem).range
  let B : Subgroup ↥Y := K.subgroupOf Y
  have hperf : ⁅(⊤ : Subgroup (StatedSp 2 F₃)), (⊤ : Subgroup (StatedSp 2 F₃))⁆ = ⊤ := by
    have := Group.isPerfect_def.1 isPerfect_sp4_three
    rwa [commutator_def] at this
  have hA : A ≤ ⁅A, A⁆ := by
    have h1 : A = (⊤ : Subgroup (StatedSp 2 F₃)).map (l.Θ.codRestrict Y l.mem) :=
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
      exact (c.d.comm₀ _ (c.hQ₀ ⟨b, hb, rfl⟩) (c.d.ψ s') ⟨s', rfl⟩).symm
    exact c.hP1 hO
  have h0 := Models.SymplecticPairs.commutator_eq_bot_of_perfect hA hc
  have hmem : ⁅(⟨l.Θ s, l.mem s⟩ : ↥Y), (⟨k, le_centralizingLayer c.hKz hk⟩ : ↥Y)⁆ ∈ ⁅A, B⁆ :=
    Subgroup.commutator_mem_commutator ⟨s, rfl⟩ (Subgroup.mem_subgroupOf.mpr hk)
  rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact congrArg Subtype.val hmem

theorem conj_fixed {t : G} (ht : t * z * t⁻¹ = z) {x : StatedSp 2 F₃} (hx3 : x ^ 3 = 1)
    (hfix : Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ x) = c.d.ψ x) :
    t * l.Θ x * t⁻¹ = l.Θ x := by
  set Y := locLayer Ω z with hY
  set O := classicalInvolutionOddCore ↥Y with hOdef
  set y : ↥Y := ⟨l.Θ x, l.mem x⟩ with hydef
  set y' : ↥Y := Gaps.layerAut c.hΩ.conjInvariant ht y with hy'def
  have hmk : QuotientGroup.mk' O y = c.d.ψ x := DFunLike.congr_fun l.comp_eq x
  have hmk' : QuotientGroup.mk' O y' = c.d.ψ x := by
    have : QuotientGroup.mk' O y' = Gaps.locAut c.hΩ.conjInvariant ht (QuotientGroup.mk' O y) :=
      (Gaps.locAut_mk c.hΩ.conjInvariant ht y).symm
    rw [this, hmk, hfix]
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    show l.Θ x ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  have hy'3 : y' ^ 3 = 1 := by
    rw [hy'def, ← map_pow, hy3, map_one]
  have ho : y⁻¹ * y' ∈ O := by
    rw [← QuotientGroup.eq_one_iff (N := O)]
    change QuotientGroup.mk' O (y⁻¹ * y') = 1
    rw [map_mul, map_inv, hmk, hmk', inv_mul_cancel]
  have hoc : y⁻¹ * y' ∈ Subgroup.center ↥Y := c.hP1 ho
  have h3 : (y⁻¹ * y') ^ 3 = 1 := by
    have e : y' = y * (y⁻¹ * y') := by group
    have h1 : y' ^ 3 = y ^ 3 * (y⁻¹ * y') ^ 3 := by
      conv_lhs => rw [e]
      exact Commute.mul_pow (Subgroup.mem_center_iff.mp hoc y) 3
    rw [hy'3, hy3, one_mul] at h1
    exact h1.symm
  have hone : y⁻¹ * y' = 1 := by
    have hdvd : orderOf (y⁻¹ * y') ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ Subgroup.orderOf_dvd_natCard O ho) c.hO3
  have hyy : y' = y := (inv_mul_eq_one.mp hone).symm
  exact congrArg Subtype.val hyy

end LayerS3

end CFSG.ClassicalInvolution.Q3.Q3TPS
