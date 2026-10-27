module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTHullA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTL4

public section

namespace CFSG.OddStandard.SmallF3.Omega

private theorem l34g_odd_orderOf_of_mem_oddCore {Y : Type} [Group Y] [Finite Y] {y : Y}
    (hy : y ∈ oddCore Y) : Odd (orderOf y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Odd (Nat.card (oddCore Y)) := by
    have h : oddCore Y = pPrimeCore 2 Y :=
      (oddCore_eq_piCore Y).trans (pPrimeCore_eq_piCore Y 2).symm
    rw [h]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := Y))
  exact hcard.of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCore Y) hy)

theorem l34g_odd_card_oddHull_inf_ker {A C : Type} [Group A] [Group C] [Finite A] (φ : A →* C)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A)
    (h2 : ∀ P : Subgroup A, IsPGroup 2 P → P ≤ φ.ker → Nat.card P ≤ 2) {B : Subgroup C}
    (hB : IsSL23Mod ↥B) : Odd (Nat.card ↥(l34g_oddHull φ B ⊓ φ.ker)) := by
  classical
  haveI : Finite C := Finite.of_surjective φ hφ
  let H : Subgroup A := l34g_oddHull φ B
  let X : Subgroup A := B.comap φ
  change Odd (Nat.card ↥(H ⊓ φ.ker))
  have hHle : H ≤ X := l34g_oddHull_le φ B
  obtain ⟨e⟩ := hB
  let π : X →* ↥B := (φ.comp X.subtype).codRestrict B (fun x => x.2)
  let ρ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (oddCore ↥B)).comp π)
  have hπsurj : Function.Surjective π := by
    intro b
    obtain ⟨a, ha⟩ := hφ (b : C)
    refine ⟨⟨a, ?_⟩, ?_⟩
    · show φ a ∈ B
      rw [ha]
      exact b.2
    · apply Subtype.ext
      exact ha
  have hρsurj : Function.Surjective ρ :=
    (e.surjective).comp (((QuotientGroup.mk'_surjective (oddCore ↥B))).comp hπsurj)
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hdvd : 2 ∣ Nat.card ↥(H ⊓ φ.ker) := even_iff_two_dvd.mp heven
  obtain ⟨ζ₀, hζ₀⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  let ζ : X := ⟨(ζ₀ : A), hHle ζ₀.2.1⟩
  have hζ2 : orderOf ζ = 2 := by
    change orderOf (⟨(ζ₀ : A), hHle ζ₀.2.1⟩ : X) = 2
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hζ₀]
  have hπζ : π ζ = 1 := by
    apply Subtype.ext
    show φ (ζ : A) = 1
    exact ζ₀.2.2
  have hρζ : ρ ζ = 1 := by
    change e (QuotientGroup.mk' (oddCore ↥B) (π ζ)) = 1
    rw [hπζ]
    simp
  have hζc : ∀ x : X, x * ζ = ζ * x := by
    intro x
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hker ζ₀.2.2)) (x : A)
  have hk : ∀ P : Subgroup X, IsPGroup 2 P → P ≤ ρ.ker → Nat.card P ≤ 2 := by
    intro P hP hPker
    have hmap_le : P.map X.subtype ≤ φ.ker := by
      rintro a ⟨p, hp, rfl⟩
      have hρp : ρ p = 1 := hPker hp
      have hmk : QuotientGroup.mk' (oddCore ↥B) (π p) = 1 := by
        apply e.injective
        rw [map_one]
        change ρ p = 1
        exact hρp
      have hπmem : π p ∈ oddCore ↥B := by
        rw [← QuotientGroup.ker_mk' (oddCore ↥B)]
        exact MonoidHom.mem_ker.mpr hmk
      have hπodd : Odd (orderOf (π p)) := l34g_odd_orderOf_of_mem_oddCore hπmem
      have hdvd' : orderOf (π p) ∣ orderOf p := orderOf_map_dvd π p
      obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨p, hp⟩ : ↥P)
      have hpow : orderOf (π p) ∣ 2 ^ k := by
        rw [← hk, ← Subgroup.orderOf_coe (⟨p, hp⟩ : ↥P)]
        exact hdvd'
      have hcop : Nat.Coprime (orderOf (π p)) (2 ^ k) :=
        (Nat.coprime_two_right.mpr hπodd).pow_right k
      have hone : orderOf (π p) = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hpow
      have hπp : π p = 1 := orderOf_eq_one_iff.mp hone
      have hval : (π p).val = 1 := by simpa using congrArg Subtype.val hπp
      show φ (p : A) = 1
      exact hval
    have hP' : IsPGroup 2 (P.map X.subtype) := hP.map X.subtype
    have hcard := h2 (P.map X.subtype) hP' hmap_le
    rwa [Subgroup.card_map_of_injective X.subtype_injective] at hcard
  have hζnot := l34g_not_mem_closure_odd_of_cover ρ hρsurj hζ2 hρζ hζc hk
  have hH_le : H ≤ (Subgroup.closure {x : X | Odd (orderOf x)}).map X.subtype := by
    change Subgroup.closure {a : A | φ a ∈ B ∧ Odd (orderOf a)} ≤
      (Subgroup.closure {x : X | Odd (orderOf x)}).map X.subtype
    rw [Subgroup.closure_le]
    rintro a ⟨haB, haodd⟩
    have hmemX : a ∈ X := haB
    have hgen : (⟨a, hmemX⟩ : X) ∈ Subgroup.closure {x : X | Odd (orderOf x)} :=
      Subgroup.subset_closure (by
        show Odd (orderOf (⟨a, hmemX⟩ : X))
        rwa [Subgroup.orderOf_mk])
    exact Subgroup.mem_map_of_mem X.subtype hgen
  have hmem : (ζ₀ : A) ∈ (Subgroup.closure {x : X | Odd (orderOf x)}).map X.subtype :=
    hH_le ζ₀.2.1
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmem
  have hxζ : x = ζ := Subtype.ext hxeq
  exact hζnot (hxζ ▸ hx)

theorem l34g_isSL23Mod_oddHull {A C : Type} [Group A] [Group C] [Finite A] (φ : A →* C)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A)
    (h2 : ∀ P : Subgroup A, IsPGroup 2 P → P ≤ φ.ker → Nat.card P ≤ 2) {B : Subgroup C}
    (hB : IsSL23Mod ↥B) : IsSL23Mod ↥(l34g_oddHull φ B) := by
  classical
  let H : Subgroup A := l34g_oddHull φ B
  change IsSL23Mod ↥H
  have hHle : H ≤ B.comap φ := l34g_oddHull_le φ B
  let ψ : ↥H →* ↥B := (φ.comp H.subtype).codRestrict B (fun x => hHle x.2)
  have hψsurj : Function.Surjective ψ := by
    intro b
    have hb : (b : C) ∈ (l34g_oddHull φ B).map φ := by
      rw [l34g_map_oddHull φ hφ hB]
      exact b.2
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hb
    exact ⟨⟨a, ha⟩, by apply Subtype.ext; exact haeq⟩
  have hcard : Nat.card ψ.ker = Nat.card ↥(H ⊓ φ.ker) := by
    have hker_eq : ψ.ker = (φ.ker).subgroupOf H := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [hker_eq]
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hodd : Odd (Nat.card ψ.ker) := by
    rw [hcard]
    change Odd (Nat.card ↥(l34g_oddHull φ B ⊓ φ.ker))
    exact l34g_odd_card_oddHull_inf_ker φ hφ hker h2 hB
  exact l34g_isSL23Mod_of_odd_ker ψ hψsurj hodd hB

end CFSG.OddStandard.SmallF3.Omega
