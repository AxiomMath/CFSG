module

public import CFSG.GH74.Uniqueness.SU.SU8BK1
public import CFSG.GH74.Uniqueness.SU.SU8Lift

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU8.Setup
  CFSG.GH74.Uniqueness.SU.SU8.LocA CFSG.GH74.Uniqueness.SU.SU8.BLift
open scoped commutatorElement

namespace BK

section Pre

variable {X : Type} [Group X] {O L A : Subgroup X} [O.Normal] [L.Normal]

structure PreHyp (O L A : Subgroup X) [O.Normal] [L.Normal] : Prop where
  odd : Odd (Nat.card O)
  exp : ∀ a ∈ A, a * a = 1
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  split : ∀ a ∈ A, ∃ l ∈ L, ∃ c : X, (∀ m ∈ L, ⁅c, m⁆ ∈ O) ∧ a = l * c
  omega : ∃ S : Sylow 2 X, ∀ s ∈ (S : Subgroup X) ⊓ L, s * s = 1 → s ∈ A

end Pre

variable {X : Type} [Group X] {O L A : Subgroup X} [O.Normal] [L.Normal]

theorem theta_O {o : X} (ho : o ∈ O) : theta O L o = 1 := by
  have h1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  rw [theta_apply, h1, map_one]

@[expose] def rho (O L : Subgroup X) [O.Normal] [L.Normal] :
    ↥(Kb O L) →* ↥(L.map (theta O L)) :=
  ((QuotientGroup.mk' (Z0 (Kb O L))).comp (Kb O L).subtype).codRestrict _ (fun k => by
    obtain ⟨l, hl, hlk⟩ := k.2
    exact ⟨l, hl, by rw [theta_apply, hlk]; rfl⟩)

theorem rho_surjective : Function.Surjective (rho O L) := by
  rintro ⟨y, l, hl, rfl⟩
  exact ⟨⟨QuotientGroup.mk' O l, l, hl, rfl⟩, rfl⟩

theorem rho_ker : (rho O L).ker = center ↥(Kb O L) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h1 : QuotientGroup.mk' (Z0 (Kb O L)) (k : X ⧸ O) = 1 := congrArg Subtype.val h
    have h2 : (k : X ⧸ O) ∈ Z0 (Kb O L) := (QuotientGroup.eq_one_iff _).mp h1
    exact Subtype.ext ((mem_Z0.mp h2).2 g g.2).symm
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (k : X ⧸ O)).mpr
      (mem_Z0.mpr ⟨k.2, fun g hg => congrArg Subtype.val (h ⟨g, hg⟩).symm⟩)

noncomputable def khatEquiv : (↥(Kb O L) ⧸ center ↥(Kb O L)) ≃* ↥(L.map (theta O L)) :=
  (QuotientGroup.quotientMulEquivOfEq (rho_ker (O := O) (L := L)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (rho O L) rho_surjective)

theorem benderType_khat
    (hSz : Nonempty ((↥(Kb O L) ⧸ center ↥(Kb O L)) ≃* CFSG.Theory.Comparator.SzModel 1)) :
    BenderType ↥(L.map (theta O L)) (2 * 1 + 1) 2 1 :=
  BenderType.suzuki 1 le_rfl (khatEquiv.symm.trans hSz.some)

variable [Finite X]

theorem isPGroup_center (hO : pPrimeCore 2 (X ⧸ O) = ⊥) : IsPGroup 2 ↥(center ↥(Kb O L)) := by
  have h1 : IsPGroup 2 ↥(Z0 (Kb O L)) :=
    isPGroup_two_of_normal_comm hO (Z0 (Kb O L))
      (fun a ha b hb => (mem_Z0.mp ha).2 b (mem_Z0.mp hb).1)
  exact h1.of_equiv (Subgroup.equivMapOfInjective (center ↥(Kb O L)) (Kb O L).subtype
    (Kb O L).subtype_injective).symm

theorem Z0_le_map (pre : PreHyp O L A) (hO : pPrimeCore 2 (X ⧸ O) = ⊥)
    (hsq : ∀ P : Sylow 2 ↥(Kb O L), ∀ g ∈ (P : Subgroup ↥(Kb O L)), g ^ 2 ∈ center ↥(Kb O L) →
      g ^ 2 = 1) :
    ∀ c ∈ Z0 (Kb O L), c ∈ A.map (QuotientGroup.mk' O) := by
  obtain ⟨S, hS⟩ := pre.omega
  obtain ⟨P, hP⟩ := Lift.exists_sylow_image (O := O) (L := L) S
  intro c hc
  have hcK : c ∈ Kb O L := Z0_le _ hc
  let u : ↥(Kb O L) := ⟨c, hcK⟩
  have huc : u ∈ center ↥(Kb O L) :=
    Subgroup.mem_center_iff.mpr (fun g => Subtype.ext ((mem_Z0.mp hc).2 g g.2).symm)
  have huP : u ∈ (P : Subgroup ↥(Kb O L)) := (isPGroup_center hO).le_sylow_of_normal P huc
  have hu1 : u ^ 2 = 1 := hsq P u huP ((center _).pow_mem huc 2)
  obtain ⟨s, hs, hsu⟩ := (hP u).mp huP
  have hcc : c * c = 1 := by
    have := congrArg Subtype.val hu1
    simpa [sq] using this
  have hss : QuotientGroup.mk' O (s * s) = 1 := by
    rw [map_mul, ← hsu]
    exact hcc
  have hssO : s * s ∈ O := (QuotientGroup.eq_one_iff _).mp hss
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs.1⟩
  have hk' : (s * s) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    calc (s * s) ^ (2 ^ k) = (s ^ (2 ^ k)) ^ 2 := by
          rw [← sq, ← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [this]; simp
  have hss1 : s * s = 1 := eq_one_of_mem_odd pre.odd hssO hk'
  exact ⟨s, hS s hs hss1, hsu.symm⟩

theorem exists_omega (pre : PreHyp O L A)
    (hsq : ∀ P : Sylow 2 ↥(Kb O L), ∀ g ∈ (P : Subgroup ↥(Kb O L)), g ^ 2 ∈ center ↥(Kb O L) →
      g ^ 2 = 1) :
    ∃ (P : Sylow 2 ↥(Kb O L)) (P' : Sylow 2 ↥(L.map (theta O L))),
      (∀ g ∈ (P' : Subgroup ↥(L.map (theta O L))), g * g = 1 →
        (g : (X ⧸ O) ⧸ Z0 (Kb O L)) ∈ A.map (theta O L)) ∧
      (P' : Subgroup ↥(L.map (theta O L))) = (P : Subgroup ↥(Kb O L)).map (rho O L) := by
  obtain ⟨S, hS⟩ := pre.omega
  obtain ⟨P, hP⟩ := Lift.exists_sylow_image (O := O) (L := L) S
  refine ⟨P, P.mapSurjective rho_surjective, ?_, Sylow.coe_mapSurjective rho_surjective P⟩
  intro g hg hgg
  rw [Sylow.coe_mapSurjective rho_surjective P] at hg
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
  have hp2 : p ^ 2 ∈ center ↥(Kb O L) := by
    rw [← rho_ker, MonoidHom.mem_ker, sq, map_mul]
    exact hgg
  have hp1 : p ^ 2 = 1 := hsq P p hp hp2
  obtain ⟨s, hs, hsp⟩ := (hP p).mp hp
  have hpp : (p : X ⧸ O) * p = 1 := by
    have := congrArg Subtype.val hp1
    simpa [sq] using this
  have hss : QuotientGroup.mk' O (s * s) = 1 := by
    rw [map_mul, ← hsp]
    exact hpp
  have hssO : s * s ∈ O := (QuotientGroup.eq_one_iff _).mp hss
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs.1⟩
  have hk' : (s * s) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    calc (s * s) ^ (2 ^ k) = (s ^ (2 ^ k)) ^ 2 := by
          rw [← sq, ← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [this]; simp
  have hss1 : s * s = 1 := eq_one_of_mem_odd pre.odd hssO hk'
  refine ⟨s, hS s hs hss1, ?_⟩
  rw [theta_apply, ← hsp]
  rfl

theorem locHyp_of_omega {n i e : ℕ} (pre : PreHyp O L A)
    (hBT : BenderType ↥(L.map (theta O L)) n i e)
    (homega : ∃ P : Sylow 2 ↥(L.map (theta O L)), ∀ g ∈ (P : Subgroup ↥(L.map (theta O L))),
      g * g = 1 → (g : (X ⧸ O) ⧸ Z0 (Kb O L)) ∈ A.map (theta O L)) :
    LocHyp (L.map (theta O L)) (A.map (theta O L)) n i e := by
  refine LocHyp.of_benderType hBT ?_ ?_ homega ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, pre.exp a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, pre.comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨l, hl, c, hc, rfl⟩ := pre.split a ha
    refine ⟨theta O L l, ⟨l, hl, rfl⟩, theta O L c, ?_, by rw [map_mul]⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨m, hm, rfl⟩
    have h1 : theta O L ⁅c, m⁆ = 1 := theta_O (hc m hm)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

end BK

end CFSG.GH74.Uniqueness.SU.SU8
