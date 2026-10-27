module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF16

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 (imgX)
open scoped commutatorElement

section Odd

variable {G : Type} [Group G] [Finite G]

theorem mem_oddCore_of_mem_oddCore {H : Subgroup G} {u : ↥H}
    (hu : (u : G) ∈ classicalInvolutionOddCore G) : u ∈ classicalInvolutionOddCore ↥H := by
  set S : Subgroup G := Balance.oddCoreIn (⊤ : Subgroup G) ⊓ H with hS
  have hSH : S ≤ H := inf_le_right
  have hnorm : H ≤ Subgroup.normalizer (S : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ H, ∀ m ∈ S, g * m * g⁻¹ ∈ S := fun g hg m hm =>
      ⟨Balance.conj_mem_oddCoreIn (Subgroup.mem_top g) hm.1, H.mul_mem (H.mul_mem hg (hSH hm))
        (H.inv_mem hg)⟩
    intro m
    refine ⟨fun hm => key g hg m hm, fun hm => ?_⟩
    have := key g⁻¹ (H.inv_mem hg) _ hm
    simpa [mul_assoc] using this
  have hodd : Odd (Nat.card S) :=
    (Balance.odd_card_oddCoreIn (⊤ : Subgroup G)).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_left : S ≤ Balance.oddCoreIn (⊤ : Subgroup G)))
  have hSO : S ≤ Balance.oddCoreIn H := Balance.le_oddCoreIn_of_normalizes hSH hnorm hodd
  have hu' : (u : G) ∈ S := by
    refine ⟨?_, u.2⟩
    have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant
      (Subgroup.topEquiv (G := G)).symm
    have h2 : (Subgroup.topEquiv (G := G)).symm (u : G) ∈
        classicalInvolutionOddCore ↥(⊤ : Subgroup G) := by
      have hu0 : (u : G) ∈ componentClassificationOddCore G := hu
      have h3 := Subgroup.mem_map_of_mem (Subgroup.topEquiv (G := G)).symm.toMonoidHom hu0
      rwa [h1] at h3
    exact ⟨_, h2, rfl⟩
  obtain ⟨y, hy, hyu⟩ := hSO hu'
  have : y = u := Subtype.ext hyu
  rw [this] at hy
  exact hy

end Odd

section TD


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ b : Y}

theorem oddCore_le_comap_inclusion {H : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    (hH : IsSubnormal H ⊤) :
    classicalInvolutionOddCore ↥H ≤ (classicalInvolutionOddCore (CentTop b)).comap
      (Subgroup.inclusion (le_top : H ≤ (⊤ : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))))) := by
  intro m hm
  have h1 : (m : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ Balance.oddCoreIn H := ⟨m, hm, rfl⟩
  obtain ⟨y, hy, hym⟩ := Balance.oddCoreIn_le_of_isSubnormal hH h1
  have : y = Subgroup.inclusion (le_top : H ≤ ⊤) m := Subtype.ext hym
  show Subgroup.inclusion (le_top : H ≤ ⊤) m ∈ classicalInvolutionOddCore (CentTop b)
  rw [← this]
  exact hy

@[expose] noncomputable def toCentBar {H : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    (hH : IsSubnormal H ⊤) : ↥H ⧸ classicalInvolutionOddCore ↥H →* CentBar b :=
  QuotientGroup.map (classicalInvolutionOddCore ↥H) (classicalInvolutionOddCore (CentTop b))
    (Subgroup.inclusion (le_top : H ≤ ⊤)) (oddCore_le_comap_inclusion hH)

theorem toCentBar_mk {H : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))} (hH : IsSubnormal H ⊤)
    (h : ↥H) : toCentBar hH (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h) =
      QuotientGroup.mk' (classicalInvolutionOddCore (CentTop b)) (Subgroup.inclusion le_top h) :=
  rfl

theorem noCentFour_quot (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b)
    {H : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))} (hH : IsSubnormal H ⊤)
    (htH : (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ H) :
    NoCentFour (imgX b H (tightCore R))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
        (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H)) := by
  classical
  intro g hne k hk hk4 hcomm
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ g
  set tH : ↥H := ⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ with htHdef
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥H) with hπ
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  set cY : Y := (((h : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) : Y) with hcY
  have hcC : cY ∈ Subgroup.centralizer ({b} : Set Y) := ((h : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))).2
  have hsC : cY * t * cY⁻¹ ∈ Subgroup.centralizer ({b} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC F.htC) (Subgroup.inv_mem _ hcC)
  have hcon : ¬ t⁻¹ * (cY * t * cY⁻¹) ∈ oddCoreOf (Subgroup.centralizer ({b} : Set Y)) := by
    intro hmem
    apply hne
    obtain ⟨o, ho, hot⟩ := hmem
    have hu : ((tH⁻¹ * (h * tH * h⁻¹) : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) = o := by
      apply Subtype.ext
      have h1 : ((o : ↥(Subgroup.centralizer ({b} : Set Y))) : Y) = t⁻¹ * (cY * t * cY⁻¹) := hot
      rw [h1]
      rfl
    have hu' : tH⁻¹ * (h * tH * h⁻¹) ∈ classicalInvolutionOddCore ↥H :=
      mem_oddCore_of_mem_oddCore (by rw [hu]; exact ho)
    have h2 : π tH = π (h * tH * h⁻¹) := (QuotientGroup.eq (s := classicalInvolutionOddCore ↥H)).mpr hu'
    rw [map_mul, map_mul, map_inv] at h2
    exact h2.symm
  obtain ⟨m, hmL, hm4, hmk⟩ := exists_order_four_lift hodd
    (L := ((coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y))).subgroupOf H) hk hk4
  have hmL' : (Subgroup.inclusion (le_top : H ≤ ⊤) m) ∈
      ((coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y))).subgroupOf (⊤ : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hmL)
  have hm4' : orderOf (Subgroup.inclusion (le_top : H ≤ ⊤) m) = 4 := by
    rw [orderOf_injective _ (Subgroup.inclusion_injective le_top), hm4]
  have hmc : centBarMk b hsC * QuotientGroup.mk' (classicalInvolutionOddCore (CentTop b))
        (Subgroup.inclusion (le_top : H ≤ ⊤) m) =
      QuotientGroup.mk' (classicalInvolutionOddCore (CentTop b))
        (Subgroup.inclusion (le_top : H ≤ ⊤) m) * centBarMk b hsC := by
    have h1 := congrArg (toCentBar hH) hcomm
    rw [map_mul, map_mul, ← hmk] at h1
    simp only [map_mul, map_inv, toCentBar_mk] at h1
    exact h1
  exact false_of_cent_order_four F hcC hsC hcon _ hmL' hm4' hmc

end TD

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four
