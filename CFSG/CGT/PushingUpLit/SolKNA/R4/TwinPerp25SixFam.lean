module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25SixLift
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinD2Leaves2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin

section Defs

variable {Y : Type} [Group Y]

variable (a : Y) in
abbrev CentTop : Type := ↥(⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y)))

variable (a : Y) in
abbrev CentBar : Type := CentTop a ⧸ classicalInvolutionOddCore (CentTop a)

abbrev centBarMk (a : Y) {y : Y} (hy : y ∈ Subgroup.centralizer ({a} : Set Y)) : CentBar a :=
  QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a)) (topMk ⟨y, hy⟩)

end Defs

section Fam

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {a : Y}

theorem twinT4Hyp_famX {r : ℕ} (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (X : Subgroup ↥(Subgroup.centralizer ({a} : Set Y))) :
    TwinT4Hyp r (↥X ⧸ classicalInvolutionOddCore ↥X) (famX Ω a X) :=
  ⟨famX_hyp hΩ hc2 X, famX_twoGroup h2 X, famX_quat hc2 hq X,
    TwinADescent3.aEmpty_quot_coreFamily hΩ hA hc2 X,
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥X⟩

theorem isUniqueInvolution_imgX (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    {J : Subgroup Y} (hJ : J ∈ tqMembers3 Ω a) {w : Y} (hw : w ∈ coreAt a J)
    (hwC : w ∈ Subgroup.centralizer ({a} : Set Y)) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    IsUniqueInvolution (imgX a (⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y))) J)
      (centBarMk a hwC) := by
  have hmem := imgX_mem_famX (X := (⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y)))) hJ le_top
  obtain ⟨⟨u, hu⟩, -⟩ :=
    (famX_hyp hΩ hc2 (⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y)))).omega1 _ hmem
  have hwmem : centBarMk a hwC ∈ imgX a (⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y))) J :=
    Subgroup.mem_map.mpr ⟨topMk ⟨w, hwC⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
  have hsq : topMk (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({a} : Set Y))) *
      topMk (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({a} : Set Y))) = 1 :=
    Subtype.ext (Subtype.ext hw2)
  have hne : topMk (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({a} : Set Y))) ≠ 1 := by
    intro h
    have h1 := congrArg (fun t : ↥(⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y))) =>
      (((t : ↥(Subgroup.centralizer ({a} : Set Y)))) : Y)) h
    exact hw1 (by simpa using h1)
  have hodd := CFSG.ComponentClassification.OddCore.odd_card (CentTop a)
  have h1 : centBarMk a hwC ≠ 1 := mk_ne_one_of_involution_of_odd hodd hsq hne
  have h2 : centBarMk a hwC * centBarMk a hwC = 1 := by
    rw [← map_mul, hsq, map_one]
  rcases hu.unique _ hwmem h2 with h | h
  · exact absurd h h1
  · rw [h]
    exact hu

theorem exists_order_four_cent {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) {J L : Subgroup Y} (hJ : J ∈ tqMembers3 Ω a)
    (hL : L ∈ tqMembers3 Ω a) {u v : Y} (hu : IsUniqueInvolution J u)
    (hv : IsUniqueInvolution L v) (huC : u ∈ Subgroup.centralizer ({a} : Set Y))
    (hvC : v ∈ Subgroup.centralizer ({a} : Set Y)) {Q : Subgroup (CentBar a)} (hQn : Q.Normal)
    (hQ2 : IsPGroup 2 Q) (huQ : centBarMk a huC ∈ Q) (hvQ : centBarMk a hvC ∈ Q) :
    ∃ m : CentTop a, (((m : ↥(Subgroup.centralizer ({a} : Set Y))) : Y) ∈ coreAt a J) ∧
      orderOf m = 4 ∧
      centBarMk a hvC * QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a)) m =
        QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a)) m * centBarMk a hvC := by
  classical
  have hT4 := twinT4Hyp_famX hΩ hc2 h2 hq hA (⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y)))
  have hJΔ := imgX_mem_famX (X := (⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y)))) hJ le_top
  have hLΔ := imgX_mem_famX (X := (⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y)))) hL le_top
  have huJ : u ∈ coreAt a J :=
    TwinLayer.mem_exactCore_of_uniqueInvolution hΩ hc2 hJ.1 hJ.2 hu
  have hvL : v ∈ coreAt a L :=
    TwinLayer.mem_exactCore_of_uniqueInvolution hΩ hc2 hL.1 hL.2 hv
  have hu₁ := isUniqueInvolution_imgX hΩ hc2 hJ huJ huC hu.sq hu.ne_one
  have hv₁ := isUniqueInvolution_imgX hΩ hc2 hL hvL hvC hv.sq hv.ne_one
  have hnorm : centBarMk a hvC ∈ Subgroup.normalizer
      ((imgX a (⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y))) J : Subgroup (CentBar a)) :
        Set (CentBar a)) := by
    by_contra hnm
    have := hT4.le_three_of_not_mem_normalizer hJΔ hLΔ hu₁ hv₁ ⟨Q, hQn, hQ2, huQ⟩
      ⟨Q, hQn, hQ2, hvQ⟩ hnm
    omega
  obtain ⟨X, hXle, hX2, hX4⟩ := hT4.exists_le_centralizer hJΔ hLΔ hu₁ hv₁ hQn hQ2 huQ hvQ hnorm
  obtain ⟨x, hxX, hx4⟩ :=
    exists_orderOf_four_of_uniqueInvolution hu₁ (hXle.trans inf_le_left) hX2 hX4
  have hxJ := (hXle hxX).1
  have hxc := (hXle hxX).2
  obtain ⟨m, hmL, hm4, hmx⟩ := exists_order_four_lift (N := classicalInvolutionOddCore (CentTop a))
    (CFSG.ComponentClassification.OddCore.odd_card (CentTop a))
    (L := (((coreAt a J).subgroupOf (Subgroup.centralizer ({a} : Set Y))).subgroupOf
      (⊤ : Subgroup ↥(Subgroup.centralizer ({a} : Set Y))))) hxJ hx4
  refine ⟨m, Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hmL), hm4, ?_⟩
  rw [hmx]
  exact (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm

end Fam

end CFSG.CGT.PushingUpLit.SolKNA.R4
