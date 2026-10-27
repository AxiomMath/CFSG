module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.Generic.S45.LDiagPerm
public import CFSG.GH74.Generic.S45.PumpC1

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump306

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.L5U5 CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.GH74.GLS Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K A T : Subgroup G}

omit [Finite G] in
theorem mem_conjSub_iff {g : G} {J : Subgroup G} {z : G} : z ∈ conjSub g J ↔ g⁻¹ * z * g ∈ J := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk
  · intro hz
    exact ⟨g⁻¹ * z * g, hz, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite G] in
theorem conjSub_eq_of_mem_normalizer {g : G} {J : Subgroup G} (hg : g ∈ normalizer (J : Set G)) :
    conjSub g J = J := by
  ext z
  rw [mem_conjSub_iff]
  have h := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * z * g)
  have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
  rw [e] at h
  exact h

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq {g : G} {J : Subgroup G} (h : conjSub g J = J) :
    g ∈ normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h1 : g * z * g⁻¹ ∈ conjSub g J ↔ g * z * g⁻¹ ∈ J := by rw [h]
  rw [mem_conjSub_iff] at h1
  have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
  rw [e] at h1
  exact h1

omit [Finite G] in
theorem mem_conjSub_barSub_iff {g : G} (hg : g ∈ centralizer ({y} : Set G)) {J : Subgroup G}
    (b : CentralizerBar y) :
    b ∈ conjSub (proj y ⟨g, hg⟩)⁻¹ (barSub y J) ↔ b ∈ barSub y (conjSub g⁻¹ J) := by
  rw [mem_conjSub_iff, inv_inv]
  constructor
  · intro hb
    obtain ⟨j, hjC, hjJ, hj⟩ := mem_barSub.1 hb
    have hc : g⁻¹ * j * g ∈ centralizer ({y} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hg) hjC) hg
    refine mem_barSub.2 ⟨g⁻¹ * j * g, hc, ?_, ?_⟩
    · rw [mem_conjSub_iff, inv_inv]
      have e : g * (g⁻¹ * j * g) * g⁻¹ = j := by group
      rw [e]
      exact hjJ
    · have e : (⟨g⁻¹ * j * g, hc⟩ : ↥(centralizer ({y} : Set G))) =
          (⟨g, hg⟩ : ↥(centralizer ({y} : Set G)))⁻¹ * ⟨j, hjC⟩ * ⟨g, hg⟩ := Subtype.ext rfl
      have hj' : proj y ⟨j, hjC⟩ = (proj y ⟨g, hg⟩) * b * (proj y ⟨g, hg⟩)⁻¹ := by
        rw [hj]
      rw [e, map_mul, map_mul, map_inv, hj']
      group
  · intro hb
    obtain ⟨c, hcC, hcJ, hc⟩ := mem_barSub.1 hb
    rw [mem_conjSub_iff, inv_inv] at hcJ
    have hgc : g * c * g⁻¹ ∈ centralizer ({y} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcC) (inv_mem hg)
    have hmem := proj_mem_barSub (v := y) (J := J) hgc hcJ
    have e : (⟨g * c * g⁻¹, hgc⟩ : ↥(centralizer ({y} : Set G))) =
        (⟨g, hg⟩ : ↥(centralizer ({y} : Set G))) * ⟨c, hcC⟩ *
          (⟨g, hg⟩ : ↥(centralizer ({y} : Set G)))⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, hc] at hmem
    exact hmem

theorem barMk_eq_one_of_mem {J : Subgroup G} (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J)
    {k : G} (hk : k ∈ pPrimeCoreOf 2 J) (hky : k ∈ centralizer ({y} : Set G)) :
    proj y ⟨k, hky⟩ = 1 := by
  have hsub := B1.isSubnormal_of_isPCompIn hJ
  rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hJ.1] at hk
  obtain ⟨a, ha, hak⟩ := hk
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  have h1 : a₀ ∈ ((QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({y} : Set G)))).comp
      (J.subgroupOf (centralizer ({y} : Set G))).subtype).ker := by
    rw [ker_restrict_eq_pPrimeCore hsub]
    exact ha₀
  have h2 : (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({y} : Set G))))
      ((a₀ : ↥(J.subgroupOf (centralizer ({y} : Set G)))) : ↥(centralizer ({y} : Set G))) = 1 := h1
  have e : (⟨k, hky⟩ : ↥(centralizer ({y} : Set G))) =
      ((a₀ : ↥(J.subgroupOf (centralizer ({y} : Set G)))) : ↥(centralizer ({y} : Set G))) :=
    Subtype.ext hak.symm
  rw [e]
  exact h2

theorem bar_comm_of_mem_cSec {J : Subgroup G} (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J)
    {q : G} (hq : q ∈ centralizer ({y} : Set G))
    (hqJ : q ∈ centralizerSection J (pPrimeCoreOf 2 J)) :
    ∀ b ∈ barSub y J, proj y ⟨q, hq⟩ * b = b * proj y ⟨q, hq⟩ := by
  intro b hb
  obtain ⟨k, hkC, hkJ, rfl⟩ := mem_barSub.1 hb
  have hc : ⁅k, q⁆ ∈ pPrimeCoreOf 2 J := hqJ.2.2 k hkJ
  have hcC : ⁅k, q⁆ ∈ centralizer ({y} : Set G) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hkC hq) (inv_mem hkC)) (inv_mem hq)
  have h1 := barMk_eq_one_of_mem hJ hc hcC
  have e : (⟨⁅k, q⁆, hcC⟩ : ↥(centralizer ({y} : Set G))) = ⁅(⟨k, hkC⟩ : ↥(centralizer ({y} : Set G))), ⟨q, hq⟩⁆ :=
    Subtype.ext rfl
  rw [e, map_commutatorElement] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

theorem comm_of_commutator_eq_bot {Z : Type} [Group Z] {A B : Subgroup Z} (h : ⁅A, B⁆ = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

end S3Pump306

end CFSG.GH74.Generic.BProg.B3
