module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53T1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y53_Z_le_A {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    c.s.fr.Z ≤ c.s.fr.A := by
  show Subgroup.zpowers c.s.fr.z ≤ c.s.fr.A
  exact Subgroup.zpowers_le.mpr (lfactsA_of_setting hH.hS hH.hZ c.s).z_mem

private lemma y53_Z_le_C0 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    c.s.fr.Z ≤ C0 c.e := by
  show Subgroup.zpowers c.s.fr.z ≤ C0 c.e
  exact Subgroup.zpowers_le.mpr (y5_z_mem_C0 hH)

private lemma y53_C0_le_T {c : Ctx5 G L} : C0 c.e ≤ c.e.T₁ :=
  show c.e.T₁ ⊓ Subgroup.centralizer (c.s.fr.A : Set G) ≤ c.e.T₁ from inf_le_left

private lemma isElemAbelian_map_mk'_of_comm_sq {T H Z : Subgroup G}
    [(Z.subgroupOf T).Normal]
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, ⁅a, b⁆ ∈ Z)
    (hsq : ∀ a ∈ H, a ^ 2 ∈ Z) :
    IsElemAbelian 2 ((H.subgroupOf T).map (QuotientGroup.mk' (Z.subgroupOf T))) := by
  refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have haH : (a : G) ∈ H := ha
    have hbH : (b : G) ∈ H := hb
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq).mpr
    have hconj : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hconj]
    show ((⁅b⁻¹, a⁻¹⁆ : ↥T) : G) ∈ Z
    rw [show ((⁅b⁻¹, a⁻¹⁆ : ↥T) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ from
      map_commutatorElement (f := T.subtype) b⁻¹ a⁻¹]
    exact hcomm ((b : G)⁻¹) (H.inv_mem hbH) ((a : G)⁻¹) (H.inv_mem haH)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have haH : (a : G) ∈ H := ha
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (a ^ 2)).mpr
    show ((a ^ 2 : ↥T) : G) ∈ Z
    simpa using hsq (a : G) haH

abbrev y53Abar (c : Ctx5 G L) [(c.s.fr.Z.subgroupOf c.e.T₁).Normal] :
    Subgroup (↥c.e.T₁ ⧸ c.s.fr.Z.subgroupOf c.e.T₁) :=
  (c.s.fr.A.subgroupOf c.e.T₁).map (QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁))

abbrev y53Kbar (c : Ctx5 G L) [(c.s.fr.Z.subgroupOf c.e.T₁).Normal] :
    Subgroup (↥c.e.T₁ ⧸ c.s.fr.Z.subgroupOf c.e.T₁) :=
  ((C0 c.e).subgroupOf c.e.T₁).map (QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁))

theorem y53_barA {c : Ctx5 G L} (hH : F33Hyp c.s c.e)
    [(c.s.fr.Z.subgroupOf c.e.T₁).Normal] : IsE 4 ↥(y53Abar c) := by
  have hA := lfactsA_of_setting hH.hS hH.hZ c.s
  have hZ2 : Nat.card ↥c.s.fr.Z = 2 := by
    rw [SFrame.Z, Nat.card_zpowers, hA.z_order]
  refine ⟨?_, ?_⟩
  · have h := (isElemAbelian_map_mk'_of_comm_sq (T := c.e.T₁) (H := c.s.fr.A)
        (Z := c.s.fr.Z) hA.comm_A hA.sq_A).subgroupOf (y53Abar c)
    rwa [Subgroup.subgroupOf_self] at h
  · have hcard : Nat.card ↥(y53Abar c) = c.s.fr.Z.relIndex c.s.fr.A := by
      rw [y53Abar, ← Subgroup.relIndex_ker (c.s.fr.A.subgroupOf c.e.T₁)
            (QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁)), QuotientGroup.ker_mk',
          Subgroup.relIndex_subgroupOf (H := c.s.fr.Z) (K := c.s.fr.A) (L := c.e.T₁)
            hH.h32.1.1]
    rw [hcard, show (2 : ℕ) ^ 4 = 16 by norm_num]
    have hmul := Subgroup.relIndex_mul_card (H := c.s.fr.Z) (K := c.s.fr.A)
    rw [inf_eq_left.mpr (y53_Z_le_A hH), hA.card_A, hZ2] at hmul
    omega

theorem y53_barK {c : Ctx5 G L} (hH : F33Hyp c.s c.e)
    [(c.s.fr.Z.subgroupOf c.e.T₁).Normal] : IsE 2 ↥(y53Kbar c) := by
  have hZ2 : Nat.card ↥c.s.fr.Z = 2 := by
    rw [SFrame.Z, Nat.card_zpowers, (lfactsA_of_setting hH.hS hH.hZ c.s).z_order]
  refine ⟨?_, ?_⟩
  · have h := (isElemAbelian_map_mk'_of_comm_sq (T := c.e.T₁) (H := C0 c.e)
        (Z := c.s.fr.Z) (y5_C0_comm_Z hH) (y5_C0_sq_Z hH)).subgroupOf (y53Kbar c)
    rwa [Subgroup.subgroupOf_self] at h
  · have hcard : Nat.card ↥(y53Kbar c) = c.s.fr.Z.relIndex (C0 c.e) := by
      rw [y53Kbar, ← Subgroup.relIndex_ker ((C0 c.e).subgroupOf c.e.T₁)
            (QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁)), QuotientGroup.ker_mk',
          Subgroup.relIndex_subgroupOf (H := c.s.fr.Z) (K := C0 c.e) (L := c.e.T₁)
            (y53_C0_le_T (c := c))]
    rw [hcard, show (2 : ℕ) ^ 2 = 4 by norm_num]
    have hmul := Subgroup.relIndex_mul_card (H := c.s.fr.Z) (K := C0 c.e)
    rw [inf_eq_left.mpr (y53_Z_le_C0 hH), y5_C0_card c, hZ2] at hmul
    omega

theorem y53_bar_cent {c : Ctx5 G L} (hH : F33Hyp c.s c.e)
    [(c.s.fr.Z.subgroupOf c.e.T₁).Normal] :
    ∀ k ∈ y53Kbar c, ∀ a ∈ y53Abar c, k * a = a * k := by
  intro k hk a ha
  obtain ⟨y, hy, rfl⟩ := hk
  obtain ⟨x, hx, rfl⟩ := ha
  have hyC : (y : G) ∈ centIn c.e.T₁ c.s.fr.A := hy
  have hxA : (x : G) ∈ c.s.fr.A := hx
  have hcomm : (y : G) * (x : G) = (x : G) * (y : G) :=
    (Subgroup.mem_centralizer_iff.mp hyC.2 (x : G) hxA).symm
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm

theorem y53_bar_inf {c : Ctx5 G L} (hH : F33Hyp c.s c.e)
    [(c.s.fr.Z.subgroupOf c.e.T₁).Normal] : y53Abar c ⊓ y53Kbar c = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨ha, hk⟩ := hx
  obtain ⟨a, haA, rfl⟩ := ha
  obtain ⟨k, hkC0, hkπ⟩ := hk
  have hkA : (k : G) ∈ c.s.fr.A := by
    obtain ⟨z, hz, hazk⟩ := (QuotientGroup.mk'_eq_mk' (c.s.fr.Z.subgroupOf c.e.T₁)).mp hkπ.symm
    have hzZ : (z : G) ∈ c.s.fr.Z := hz
    rw [← hazk, Subgroup.coe_mul]
    exact c.s.fr.A.mul_mem haA (y53_Z_le_A hH hzZ)
  have hkZ : (k : G) ∈ c.s.fr.Z := by
    have h : (k : G) ∈ C0 c.e ⊓ c.s.fr.A := ⟨hkC0, hkA⟩
    rwa [y5_C0_inf_A hH] at h
  have hkone : QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁) k = 1 :=
    (QuotientGroup.eq_one_iff k).mpr hkZ
  rw [← hkπ]
  exact hkone

theorem y53_bar_sup {c : Ctx5 G L} (hH : F33Hyp c.s c.e)
    [(c.s.fr.Z.subgroupOf c.e.T₁).Normal] :
    y53Abar c ⊔ y53Kbar c =
      ((C1 c.e).subgroupOf c.e.T₁).map (QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁)) := by
  rw [show C1 c.e = c.s.fr.A ⊔ C0 c.e from rfl,
    Subgroup.subgroupOf_sup hH.h32.1.1 (y53_C0_le_T (c := c)), Subgroup.map_sup]

end CFSG.OddStandard.HigherRank.YamadaG23
