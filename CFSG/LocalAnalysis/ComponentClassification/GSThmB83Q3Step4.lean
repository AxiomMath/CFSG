module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step3

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace Q3Data

variable (d : Q3Data H)
include d

abbrev R0 : Subgroup X := d.R ⊓ centralizer ({d.z} : Set X)

theorem z_mem_M3 : d.z ∈ h.M3 := H.D_le_M3 d.z_D

theorem z_mem_RM : d.z ∈ d.RM := d.Q1_le_RM ⟨h.sec8_D_le_Q d.z_D, d.z_mem_M3⟩

theorem b_comm_z : d.b * d.z = d.z * d.b :=
  (mem_centralizer_iff.mp d.b_mem_centralizer_M3 d.z d.z_mem_M3).symm

theorem map_RM_inf_centralizer_z (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    ((d.RM ⊓ centralizer ({d.z} : Set X)).subgroupOf h.M3).map H.rho = d.c.R0 := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [d.c_R]
      exact mem_map_of_mem _ hm.1
    · show H.rho m ∈ centralizer ({d.c.z} : Set _)
      rw [mem_centralizer_singleton_iff, d.c_z, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hm.2)
  · rintro y ⟨hyR, hyz⟩
    rw [d.c_R] at hyR
    obtain ⟨m, hm, rfl⟩ := mem_map.mp hyR
    refine mem_map_of_mem _ ⟨hm, ?_⟩
    show (m : X) ∈ centralizer ({d.z} : Set X)
    rw [mem_centralizer_singleton_iff]
    have hmz := mem_centralizer_singleton_iff.mp
      (show H.rho m ∈ centralizer ({d.c.z} : Set _) from hyz)
    rw [d.c_z, ← map_mul, ← map_mul] at hmz
    have hmR : (m : X) ∈ d.RM := hm
    exact congrArg Subtype.val (Eight.injOn_of_isPGroup (H.not_two_dvd_card_ker_modelHom hCF1 hCF2)
      d.isPGroup_RM.comap_subtype (mul_mem hm d.z_mem_RM) (mul_mem d.z_mem_RM hm) hmz)

theorem card_RM_inf_centralizer_z (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    Nat.card ↥(d.RM ⊓ centralizer ({d.z} : Set X)) = 64 := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have h2 : IsPGroup 2 ((d.RM ⊓ centralizer ({d.z} : Set X)).subgroupOf h.M3) :=
    (d.isPGroup_RM.to_le inf_le_left).comap_subtype
  have h1 := d.c_props.R0_sylow.1
  rw [← d.map_RM_inf_centralizer_z hCF1 hCF2, Eight.card_map_of_isPGroup hker h2,
    ← card_map_of_injective h.M3.subtype_injective,
    map_subgroupOf_eq_of_le (inf_le_left.trans d.RM_le)] at h1
  exact h1

theorem R0_eq : d.R0 = (d.RM ⊓ centralizer ({d.z} : Set X)) ⊔ h.B := by
  have hbz : d.b ∈ centralizer ({d.z} : Set X) := mem_centralizer_singleton_iff.mpr d.b_comm_z
  apply le_antisymm
  · rintro r ⟨hrR, hrz⟩
    have hrz : r ∈ centralizer ({d.z} : Set X) := hrz
    have hbN : d.b ∈ normalizer (d.RM : Set X) := centralizer_le_normalizer _ (by
      rw [mem_centralizer_iff]
      intro y hy
      exact (mem_centralizer_iff.mp d.b_mem_centralizer_M3 y (d.RM_le hy)))
    rw [R, d.B_eq] at hrR
    obtain ⟨m, hm, hrm⟩ := Eight.mem_sup_zpowers_cases hbN d.b_mul_self hrR
    rcases hrm with hrm | hrm
    · rw [hrm] at hrz ⊢
      exact mem_sup_left ⟨hm, hrz⟩
    · have hmz : m ∈ centralizer ({d.z} : Set X) := by
        have := mul_mem hrz (inv_mem hbz)
        rwa [hrm, mul_inv_cancel_right] at this
      rw [hrm]
      exact mul_mem_sup ⟨hm, hmz⟩ (d.B_eq ▸ mem_zpowers d.b)
  · refine sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right ?_)
    rw [d.B_eq, zpowers_le]
    exact hbz

theorem card_R0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : Nat.card d.R0 = 128 := by
  rw [d.R0_eq, d.card_sup_B hCF1 hCF2 (inf_le_left.trans d.RM_le),
    d.card_RM_inf_centralizer_z hCF1 hCF2]

theorem isPGroup_R0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : IsPGroup 2 d.R0 :=
  (d.isPGroup_R hCF1 hCF2).to_le inf_le_left

theorem R0_le_centralizer_bz : d.R0 ≤ centralizer ({d.b * d.z} : Set X) := by
  rintro r ⟨hrR, hrz⟩
  rw [mem_centralizer_singleton_iff]
  have hrb := mem_centralizer_singleton_iff.mp (d.R_le_centralizer_b hrR)
  have hrz' := mem_centralizer_singleton_iff.mp hrz
  rw [← mul_assoc, hrb, mul_assoc, hrz', ← mul_assoc]

theorem commutator_R0_le : ⁅d.R0, d.R0⁆ ≤ h.M3 := by
  have h4 : ⁅d.R, d.R⁆ ≤ d.RM := by
    rw [R, d.B_eq]
    exact commutator_sup_zpowers_le (by
      rw [mem_centralizer_iff]
      intro y hy
      exact (mem_centralizer_iff.mp d.b_mem_centralizer_M3 y (d.RM_le hy))) d.b_mul_self
  exact (commutator_mono inf_le_left inf_le_left).trans (h4.trans d.RM_le)

theorem a_mem_commutator_S : h.a ∈ ⁅h.S, h.S⁆ := by
  have hbS : d.b ∈ h.S := (h.B_le (d.B_eq ▸ mem_zpowers d.b)).1
  have h1 : ⁅d.b, h.x⁆ = h.a := by
    rw [commutatorElement_def]
    have hx : h.x * d.b⁻¹ * h.x⁻¹ = (h.a * d.b)⁻¹ := by
      rw [← d.xbx']
      group
    rw [mul_assoc, mul_assoc, ← mul_assoc h.x, hx, mul_inv_rev,
      inv_eq_of_mul_eq_one_right d.b_mul_self,
      inv_eq_of_mul_eq_one_right (Six.a_mul_a_self h), ← mul_assoc, d.b_mul_self, one_mul]
  rw [← h1]
  exact commutator_mem_commutator hbS h.x_mem

theorem a_not_conj_bz (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (w : X) :
    w⁻¹ * h.a * w ≠ d.b * d.z := by
  intro hw
  have hbound : ∀ P' : Subgroup X, P' ≤ centralizer ({d.b * d.z} : Set X) → IsPGroup 2 P' →
      Nat.card P' ≤ Nat.card d.R0 := by
    intro P' hP' hP'2
    rw [d.card_R0 hCF1 hCF2, ← Eight.card_conjugate_eq P' w⁻¹]
    rw [← hw] at hP'
    exact d.card_le_of_le_centralizer_a hCF1 hCF2 (hP'2.map _) (conjugate_le_centralizer hP')
  obtain ⟨T, hT⟩ := sylow_of_card_ge d.R0_le_centralizer_bz (d.isPGroup_R0 hCF1 hCF2) hbound
  have hSw : conjugate h.S w ≤ centralizer ({d.b * d.z} : Set X) := by
    intro y hy
    rw [mem_conjugate_iff] at hy
    have hc := Six.comm_a H.C_eq hy
    rw [mem_centralizer_singleton_iff, ← hw]
    calc y * (w⁻¹ * h.a * w) = w⁻¹ * ((w * y * w⁻¹) * h.a) * w := by group
      _ = w⁻¹ * (h.a * (w * y * w⁻¹)) * w := by rw [hc]
      _ = w⁻¹ * h.a * w * y := by group
  obtain ⟨c, hc, hcle⟩ := exists_conjugate_le_of_sylow ⟨T, hT⟩ hSw
    ((Six.isPGroup_S h).map _)
  have hceq : conjugate (conjugate h.S w) c = d.R0 := by
    refine eq_of_le_of_card_ge hcle ?_
    rw [d.card_R0 hCF1 hCF2, Eight.card_conjugate_eq, Eight.card_conjugate_eq, d.card_S hCF1 hCF2]
  have h1 : h.a ∈ ⁅h.S, h.S⁆ := d.a_mem_commutator_S
  have h2 : (w * c)⁻¹ * h.a * (w * c) ∈ ⁅d.R0, d.R0⁆ := by
    rw [← hceq, conjugate_conjugate]
    have : ⁅conjugate h.S (w * c), conjugate h.S (w * c)⁆ = conjugate ⁅h.S, h.S⁆ (w * c) := by
      unfold conjugate
      rw [map_commutator]
    rw [this, mem_conjugate_iff, show w * c * ((w * c)⁻¹ * h.a * (w * c)) * (w * c)⁻¹ = h.a by
      group]
    exact h1
  have hcbz : c⁻¹ * (d.b * d.z) * c = d.b * d.z := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hc, inv_mul_cancel_left]
  have h3 : (w * c)⁻¹ * h.a * (w * c) = d.b * d.z := by
    rw [show (w * c)⁻¹ * h.a * (w * c) = c⁻¹ * (w⁻¹ * h.a * w) * c by group, hw, hcbz]
  rw [h3] at h2
  apply d.b_not_mem_M3 hCF1 hCF2
  have := mul_mem (d.commutator_R0_le h2) (inv_mem d.z_mem_M3)
  rwa [mul_inv_cancel_right] at this

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
