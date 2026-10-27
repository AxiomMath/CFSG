module

public import CFSG.GF2Type.Aschbacher1976Full.LeafBigCenterTI
public import CFSG.GF2Type.Aschbacher1976Common.NotWeaklyClosed
import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicRootTI
public import CFSG.GF2Type.Aschbacher1976Common.CyclicTICommute
public import CFSG.GF2Type.Aschbacher1976Common.CyclicTIWeakClosure
public import CFSG.GF2Type.Aschbacher1976HigherCenter.PowFourCentralizes

public section

namespace CFSG.GF2Type.Aschbacher1976Full

namespace LeafBigCenter

open Subgroup CFSG CFSG.LocalAnalysis.GorensteinLyons CFSG.GF2Type.Aschbacher1976Common

variable {G : Type} [Group G] [Finite G]

theorem not_twoGen_of_bigCenter {z : G} (hB : BigCenterData z) :
    ¬ ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = Fz z := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := hB
  exact h

theorem false_of_bigCenter_of_four_three {z : G} (hz2 : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) (hB : BigCenterData z)
    (h43 : ∀ x : G, orderOf x = 4 → x ^ 2 = z →
      ∃ g : G, conjugate (zpowers x) g ≤ Hz z ∧ conjugate (zpowers x) g ≠ zpowers x) :
    False := by
  obtain ⟨Y, P, hYcyc, hY8, hzY, hYF, hYH, hPF, hPH, hP4, hC, -⟩ := hB
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY2 : IsPGroup 2 Y := hF2.to_le hYF
  have hY4 : 4 ≤ Nat.card Y := by omega
  have hHN : Hz z ≤ normalizer (Y : Set G) := fun h hh =>
    mem_normalizer_iff_conjugate_eq.mpr (hYH h hh)
  have hNY : normalizer (Y : Set G) ≤ Hz z :=
    normalizer_le_centralizer_of_isCyclic hYcyc hzY hz2
  have hTI := ti_of_bigCenter hYcyc hY2 hzY hz2 (fun g hg => hYH g hg)
  have hHF : Hz z ≤ normalizer ((Fz z : Subgroup G) : Set G) := centralizer_le_normalizer_fz z
  obtain ⟨x, hxY, hx4, hx2⟩ := exists_order_four_of_isCyclic hYcyc hY2 hY8 hzY hz2
  obtain ⟨g, hgH, hgne⟩ := h43 x hx4 hx2
  have hYg : conjugate Y g ≠ Y := by
    intro hYg'
    apply hgne
    have hmono : conjugate (zpowers x) g ≤ conjugate Y g := by
      unfold CFSG.conjugate
      exact Subgroup.map_mono (zpowers_le.mpr hxY)
    have hle : conjugate (zpowers x) g ≤ Y := hmono.trans hYg'.le
    exact CFSG.DisconnectedInvolutionGraph.Helpers.cyclic_overgroup_equal_card_subgroups Y
      (conjugate (zpowers x) g) (zpowers x) hle (zpowers_le.mpr hxY)
      (card_conjugate_eq (zpowers x) g)
  have hk : g⁻¹ * x * g ∈ conjugate Y g := inv_mul_mul_mem_conjugate hxY
  have hkH : g⁻¹ * x * g ∈ Hz z := hgH (inv_mul_mul_mem_conjugate (mem_zpowers x))
  have hkN : g⁻¹ * x * g ∈ normalizer (Y : Set G) := hHN hkH
  have hkord : orderOf (g⁻¹ * x * g) = 4 := by
    have h := orderOf_conj_eq g⁻¹ x
    rw [inv_inv] at h
    rw [h, hx4]
  have hk2 : (g⁻¹ * x * g) ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hkord] at hd
    norm_num at hd
  have hBH : conjugate Y g⁻¹ ≤ Hz z :=
    (conjugate_inv_le_normalizer hYcyc hY2 hTI hYg hk hkN hk2).trans hNY
  have hBne : conjugate Y g⁻¹ ≠ Y := by
    intro h
    apply hYg
    calc conjugate Y g = conjugate (conjugate Y g⁻¹) g := by rw [h]
      _ = conjugate Y (g⁻¹ * g) := conjugate_conjugate Y g⁻¹ g
      _ = Y := by
        rw [inv_mul_cancel]
        exact conjugate_one_eq Y
  have hTIB : Y ⊓ conjugate Y g⁻¹ = ⊥ := (hTI g⁻¹).resolve_left hBne
  obtain ⟨y₀, hy₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Y)
  have hyo : orderOf (y₀ : G) = Nat.card Y := by
    rw [Subgroup.orderOf_coe, hy₀]
  obtain ⟨b, hbdef⟩ : ∃ b : G, b = g * (y₀ : G) * g⁻¹ := ⟨_, rfl⟩
  have hb : b ∈ conjugate Y g⁻¹ := by
    rw [mem_conjugate_iff_conj_mem, inv_inv, hbdef]
    have e : g⁻¹ * (g * (y₀ : G) * g⁻¹) * g = y₀ := by group
    rw [e]
    exact y₀.2
  have hbo : orderOf b = Nat.card Y := by
    rw [hbdef, orderOf_conj_eq, hyo]
  have hb4 : b ^ 4 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hbo] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hbH : b ∈ Hz z := hBH hb
  have hbN : b ∈ normalizer (P : Set G) := mem_normalizer_iff_conjugate_eq.mpr (hPH b hbH)
  have hB2 : IsPGroup 2 (conjugate Y g⁻¹) := hY2.map (MulAut.conj g⁻¹⁻¹).toMonoidHom
  have hBF : conjugate Y g⁻¹ ≤ normalizer ((Fz z : Subgroup G) : Set G) := hBH.trans hHF
  have hS2 : IsPGroup 2 (conjugate Y g⁻¹ ⊔ Fz z : Subgroup G) :=
    hB2.to_sup_of_normal_right' hF2 hBF
  have hcomm : ∀ p ∈ P, b * (p⁻¹ * b * p) = (p⁻¹ * b * p) * b := by
    intro p hp
    have hle1 : conjugate Y g⁻¹ ≤ (conjugate Y g⁻¹ ⊔ Fz z : Subgroup G) :=
      (le_sup_left : conjugate Y g⁻¹ ≤ (conjugate Y g⁻¹ ⊔ Fz z : Subgroup G))
    have hpS : p ∈ (conjugate Y g⁻¹ ⊔ Fz z : Subgroup G) :=
      (le_sup_right : Fz z ≤ (conjugate Y g⁻¹ ⊔ Fz z : Subgroup G)) (hPF hp)
    have hle2 : conjugate Y (g⁻¹ * p) ≤ (conjugate Y g⁻¹ ⊔ Fz z : Subgroup G) := by
      intro c hc
      rw [← conjugate_conjugate, mem_conjugate_iff_conj_mem] at hc
      have h1 := mul_mem (mul_mem (inv_mem hpS) (hle1 hc)) hpS
      have h2 : p⁻¹ * (p * c * p⁻¹) * p = c := by group
      rwa [h2] at h1
    have hc : p⁻¹ * b * p ∈ conjugate Y (g⁻¹ * p) := by
      rw [← conjugate_conjugate, mem_conjugate_iff_conj_mem]
      have e : p * (p⁻¹ * b * p) * p⁻¹ = b := by group
      rw [e]
      exact hb
    exact commute_of_conjugate_le hYcyc hY2 hY4 hTI hS2 hle1 hle2 b hb _ hc
  have hcent : ∀ p ∈ P, b ^ 4 * p = p * b ^ 4 :=
    CFSG.GF2Type.Aschbacher1976HigherCenter.pow_four_commute_of_commute_conj hP4 hbN hcomm
  have hb4Y : b ^ 4 ∈ Y := hC (b ^ 4) (pow_mem hbH 4) hcent
  have hbot : b ^ 4 ∈ Y ⊓ conjugate Y g⁻¹ :=
    Subgroup.mem_inf.mpr ⟨hb4Y, pow_mem hb 4⟩
  rw [hTIB, Subgroup.mem_bot] at hbot
  exact hb4 hbot

end LeafBigCenter

section Certified


namespace LeafBigCenter

open Subgroup CFSG CFSG.LocalAnalysis.GorensteinLyons CFSG.GF2Type.Aschbacher1976Common
  CFSG.EvenSporadicStandard.Finkelstein77

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_centralizer_ne [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz2 : orderOf z = 2) {x : G} (hx4 : orderOf x = 4) (hxz : x ^ 2 = z)
    (hF2 : IsPGroup 2 (Fz z))
    (hnot : ¬ ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = Fz z) :
    ∃ g : G, conjugate (zpowers x) g ≤ Hz z ∧ conjugate (zpowers x) g ≠ zpowers x := by
  have hwc : ¬ WeaklyClosedInNormalizer (zpowers x) := fun h =>
    hnot (twoGen_of_isPGroup (dihedral_or_semidihedral_of_weaklyClosed hnab hx4 h) hF2)
  unfold WeaklyClosedInNormalizer at hwc
  push Not at hwc
  obtain ⟨h, hle, hne⟩ := hwc
  have hzZ : z ∈ zpowers x := by
    rw [← hxz]
    exact pow_mem (mem_zpowers x) 2
  have hN : normalizer (zpowers x : Set G) ≤ centralizer ({z} : Set G) :=
    normalizer_le_centralizer_of_isCyclic (Subgroup.isCyclic_zpowers x) hzZ hz2
  have hc : conjugate (zpowers x) h⁻¹ = (zpowers x).map (MulAut.conj h).toMonoidHom := by
    unfold CFSG.conjugate
    rw [inv_inv]
  refine ⟨h⁻¹, ?_, ?_⟩
  · rw [hc]
    exact le_trans hle hN
  · rw [hc]
    exact hne

end LeafBigCenter

theorem leafBigCenter_holds : Asc76LeafBigCenter := by
  intro G _ _ z hS hB
  obtain ⟨hsimp, hnab, hz2, hsymp⟩ := hS
  haveI := hsimp
  obtain ⟨hF2, -⟩ := hsymp
  exact LeafBigCenter.false_of_bigCenter_of_four_three hz2 hF2 hB
    (fun x hx4 hxz => LeafBigCenter.exists_conj_le_centralizer_ne hnab hz2 hx4 hxz hF2
      (LeafBigCenter.not_twoGen_of_bigCenter hB))

end Certified

end CFSG.GF2Type.Aschbacher1976Full
