module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B514Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private lemma s888parF_zpow_eq_one_or_self {a : G} (ha : a * a = 1) {x : G}
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : a ^ (2 : ℕ) = 1 := by rwa [pow_two]
  rw [zpow_eq_zpow_emod' k h2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    show a ^ (k % (2 : ℤ)) = 1
    rw [hk]; simp
  · right
    show a ^ (k % (2 : ℤ)) = a
    rw [hk]; simp

private lemma s888parF_t_not_mem_zpowers_z (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t ∉ zpowers z := by
  intro ht
  rcases s888parF_zpow_eq_one_or_self c.z_mul_self ht with h1 | hz
  · exact c.t_ne_one h1
  · exact c.t_ne_z h37 hz

private lemma s888parF_z_not_mem_zpowers_t (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : z ∉ zpowers t := by
  intro hz
  rcases s888parF_zpow_eq_one_or_self c.t_mul_self hz with h1 | ht
  · exact c.z_ne_one h1
  · exact c.t_ne_z h37 ht.symm

private lemma s888parF_z_not_mem_centralizer (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : z ∉ centralizer (L : Set G) := by
  intro hzC
  have hzL : z ∈ L := (c.pocket₁.2.1 c.pocket₁.1).1
  have hzZ : z ∈ centerIn L := by
    rw [sec5_mem_centerIn_iff]
    exact ⟨hzL, fun y hy => (Subgroup.mem_centralizer_iff.mp hzC y hy).symm⟩
  rw [c.centre] at hzZ
  exact s888parF_z_not_mem_zpowers_t h37 c hzZ

theorem par_t_mem_centralizer (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    t ∈ centralizer (L : Set G) := by
  have ht : t ∈ centerIn L := by
    rw [c.centre]
    exact Subgroup.mem_zpowers t
  rw [sec5_mem_centerIn_iff] at ht
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (ht.2 y hy).symm

theorem par_inf_cent_le (h52a : Asc82Lemma52a) (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {K : Fin 4 → Subgroup G} (hq : Sec5B517Quad K z)
    {i j : Fin 4} (hij : i ≠ j) (ht : t ∈ Sec5B517Q8.pair hq i j) :
    ∀ x ∈ Sec5B517Q8.pair hq i j, x * t = t * x → x ∈ centralizer (L : Set G) →
      x = 1 ∨ x = t := by
  classical
  set R : Subgroup G := Sec5B517Q8.pair hq i j with hRdef
  set E : Subgroup G := R ⊓ centralizer ({t} : Set G) with hEdef
  set D : Subgroup G := centralizer (L : Set G) with hDdef
  have hRcard : Nat.card ↥R = 32 := by
    rw [hRdef]
    exact Sec5B517Q8.card_pair hq hij
  have hzR : z ∈ R := by
    rw [hRdef]
    exact ⟨z_mem_Q8 hq, Subgroup.mem_sup_left (hq.z_mem i)⟩
  have ht_not_zpow : t ∉ zpowers z := s888parF_t_not_mem_zpowers_z h37 c
  have hEcard : Nat.card ↥E = 16 := by
    rw [hEdef]
    exact card_inf_centralizer_of_extra (R := R) (z := z) (e := t) hRcard hzR c.z_mul_self
      (fun x hx y hy => Sec5B517Q8.commutator_mem_zpowers hq hij hx hy)
      (fun x hx h => Sec5B517Q8.central_pair hq hij hx h) ht ht_not_zpow
  have hEinf_le : Nat.card ↥(E ⊓ D) ≤ 2 := by
    refine card_le_two_of_sq_eq_one (C := D) (P := E ⊓ D) inf_le_right ?_ ?_
    · exact h52a G t L c.toSec5Setting
    · intro x hx
      have hxsq : x * x ∈ zpowers z :=
        Sec5B517Q8.sq_mem_zpowers hq hij hx.1.1
      rcases s888parF_zpow_eq_one_or_self c.z_mul_self hxsq with h1 | hz
      · exact h1
      · exact absurd (hz ▸ mul_mem hx.2 hx.2) (s888parF_z_not_mem_centralizer h37 c)
  intro x hxR hxt hxD
  have hxED : x ∈ E ⊓ D :=
    ⟨⟨hxR, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩, hxD⟩
  have htED : t ∈ E ⊓ D :=
    ⟨⟨ht, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, par_t_mem_centralizer c⟩
  by_contra hcon
  push Not at hcon
  haveI : Fintype ↥(E ⊓ D) := Fintype.ofFinite _
  have h1t : (⟨1, one_mem _⟩ : ↥(E ⊓ D)) ≠ ⟨t, htED⟩ := fun h =>
    c.t_ne_one (congrArg Subtype.val h).symm
  have h1x : (⟨1, one_mem _⟩ : ↥(E ⊓ D)) ≠ ⟨x, hxED⟩ := fun h =>
    hcon.1 (congrArg Subtype.val h).symm
  have htx : (⟨t, htED⟩ : ↥(E ⊓ D)) ≠ ⟨x, hxED⟩ := fun h =>
    hcon.2 (congrArg Subtype.val h).symm
  have h3 : 3 ≤ Nat.card ↥(E ⊓ D) := by
    rw [Nat.card_eq_fintype_card]
    calc 3 = ({⟨1, one_mem _⟩, ⟨t, htED⟩, ⟨x, hxED⟩} : Finset ↥(E ⊓ D)).card :=
          (Finset.card_eq_three.mpr ⟨_, _, _, h1t, h1x, htx, rfl⟩).symm
      _ ≤ Fintype.card ↥(E ⊓ D) := Finset.card_le_univ _
  omega

end CFSG.OddStandard.SmallF3.Omega
