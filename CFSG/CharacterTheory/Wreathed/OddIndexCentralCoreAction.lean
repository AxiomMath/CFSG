module

public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift

public noncomputable section
open scoped Classical Pointwise
namespace CFSG.Wreathed.OddIndexCentralCoreAction
universe u
variable {X : Type u} [Group X]

theorem two_subgroup_le_normal_of_odd_index
    (L A : Subgroup X) [L.Normal] (hindex : Odd L.index)
    (hA : IsPGroup 2 A) : A ≤ L := by
  let q := QuotientGroup.mk' L
  have hquotient : Odd (Nat.card (X ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hindex
  have himage : Odd (Nat.card (A.map q)) :=
    hquotient.of_dvd_nat (Subgroup.card_subgroup_dvd_card (A.map q))
  have hle := PrimewisePerfectLift.two_subgroup_le_kernel_of_odd_image A hA q himage
  simpa only [q, QuotientGroup.ker_mk'] using hle

theorem normal_odd_target_fixed_factorization
    (R N A : Subgroup X) [R.Normal] [N.Normal]
    (hR : Odd (Nat.card R)) (hA : IsPGroup 2 A) (hAN : A ≤ N)
    (r : X) (hr : r ∈ R) :
    ∃ c ∈ R ⊓ Subgroup.centralizer (A : Set X),
      ∃ d ∈ R ⊓ N, c * d = r := by
  let q := QuotientGroup.mk' N
  have hmapA : A.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff A).mpr
    simpa only [q, QuotientGroup.ker_mk'] using hAN
  have himage := CFSG.SignalizerFunctor.Helpers.coprime_centralizer_image
    2 Nat.prime_two q A R hA (by simp [Subgroup.normalizer_eq_top])
    (Nat.coprime_two_left.mpr hR)
  have hfixed : q r ∈ (R ⊓ Subgroup.centralizer (A : Set X)).map q := by
    rw [himage, hmapA]
    refine ⟨Subgroup.mem_map_of_mem q hr, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro a ha
    rw [Subgroup.mem_bot.mp ha]
    simp only [one_mul, mul_one]
  obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp hfixed
  refine ⟨c, hc, c⁻¹ * r, ⟨R.mul_mem (R.inv_mem hc.1) hr, ?_⟩, ?_⟩
  · exact QuotientGroup.eq.mp hcq
  · simp only [← mul_assoc, mul_inv_cancel, one_mul]

theorem two_subgroup_centralizes_normal_odd_target
    (R N A : Subgroup X) [R.Normal] [N.Normal]
    (hR : Odd (Nat.card R)) (hA : IsPGroup 2 A) (hAN : A ≤ N)
    (hintersection : R ⊓ N ≤ Subgroup.centralizer (A : Set X)) :
    A ≤ Subgroup.centralizer (R : Set X) := by
  intro a ha
  apply Subgroup.mem_centralizer_iff.mpr
  intro r hr
  obtain ⟨c, hc, d, hd, hcd⟩ := normal_odd_target_fixed_factorization R N A hR hA hAN r hr
  have hccomm := Subgroup.mem_centralizer_iff.mp hc.2 a ha
  have hdcomm := Subgroup.mem_centralizer_iff.mp (hintersection hd) a ha
  calc
    r * a = (c * d) * a := by rw [hcd]
    _ = c * (d * a) := mul_assoc _ _ _
    _ = c * (a * d) := by rw [hdcomm]
    _ = (c * a) * d := (mul_assoc _ _ _).symm
    _ = (a * c) * d := by rw [hccomm]
    _ = a * (c * d) := mul_assoc _ _ _
    _ = a * r := by rw [hcd]

theorem central_local_odd_core_controls_two_action [Finite X]
    (L : Subgroup X) [L.Normal] (hindex : Odd L.index)
    (t : X) (htL : t ∈ L)
    (hcentral : CFSG.oddCore (Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)) ≤
      Subgroup.center (Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)))
    (A : Subgroup X) (hA : IsPGroup 2 A)
    (hAC : A ≤ Subgroup.centralizer ({t} : Set X)) :
    A ≤ Subgroup.centralizer
      (((CFSG.oddCore (Subgroup.centralizer ({t} : Set X))).map
        (Subgroup.centralizer ({t} : Set X)).subtype) : Set X) := by
  let C := Subgroup.centralizer ({t} : Set X)
  let H := Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)
  let N := L.subgroupOf C
  let R := CFSG.oddCore C
  let actor := A.subgroupOf C
  have hAL : A ≤ L := two_subgroup_le_normal_of_odd_index L A hindex hA
  have hRodd : Odd (Nat.card R) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := C)
    rw [CFSG.pPrimeCore_eq_piCore, ← CFSG.oddCore_eq_piCore] at hcop
    exact Nat.coprime_two_left.mp hcop
  let f : H →* C := (L.subtype.comp H.subtype).codRestrict C fun h =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg L.subtype (Subgroup.mem_centralizer_singleton_iff.mp h.property))
  have hf : Function.Injective f := by
    intro h k heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg C.subtype heq
  let D := R.comap f
  have hDnormal : D.Normal := Subgroup.Normal.comap inferInstance f
  have hDodd : Odd (Nat.card D) := by
    rw [← Subgroup.card_map_of_injective hf]
    apply hRodd.of_dvd_nat
    apply Subgroup.card_dvd_of_le
    rintro r ⟨h, hh, rfl⟩
    exact hh
  have hDcore : D ≤ CFSG.oddCore H := le_sSup ⟨hDnormal, hDodd⟩
  have hintersection : R ⊓ N ≤ Subgroup.centralizer (actor : Set C) := by
    intro r hr
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    let rL : L := ⟨(r : X), hr.2⟩
    let aL : L := ⟨(a : X), hAL ha⟩
    let rH : H := ⟨rL, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp r.property))⟩
    let aH : H := ⟨aL, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp a.property))⟩
    have hrD : rH ∈ D := hr.1
    have heq := Subgroup.mem_center_iff.mp (hcentral (hDcore hrD)) aH
    exact Subtype.ext (congrArg (fun h : H => ((h : L) : X)) heq)
  have hactorN : actor ≤ N := fun _ ha => hAL ha
  have hfixed := two_subgroup_centralizes_normal_odd_target R N actor hRodd
    hA.comap_subtype hactorN hintersection
  intro a ha
  apply Subgroup.mem_centralizer_iff.mpr
  rintro r ⟨rC, hrC, rfl⟩
  let aC : C := ⟨a, hAC ha⟩
  have haC : aC ∈ actor := ha
  exact congrArg C.subtype (Subgroup.mem_centralizer_iff.mp (hfixed haC) rC hrC)

theorem odd_index_normal_subgroup_central_core_controls_local_two_action [Finite X]
    (L : Subgroup X) [L.Normal] (hindex : Odd L.index)
    (t : X) (htL : t ∈ L) (_htwo : orderOf t = 2)
    (hcentral : CFSG.oddCore (Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)) ≤
      Subgroup.center (Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)))
    (A : Subgroup X) (hA : IsPGroup 2 A)
    (hAC : A ≤ Subgroup.centralizer ({t} : Set X)) :
    A ≤ Subgroup.centralizer
      (((CFSG.oddCore (Subgroup.centralizer ({t} : Set X))).map
        (Subgroup.centralizer ({t} : Set X)).subtype) : Set X) :=
  central_local_odd_core_controls_two_action L hindex t htL hcentral A hA hAC

end CFSG.Wreathed.OddIndexCentralCoreAction
