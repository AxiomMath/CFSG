module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Q8Lin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem false_of_central_quaternion (hS : Asc82SchurU43) {J : Type} [Group J] [Finite J]
    (hJ : CFSG.IsQuasisimple J) (hJt : IsTwoU43 (J ⧸ oddCore J))
    {f : QuaternionGroup 2 →* J} (hf : Function.Injective f)
    (hz : f (QuaternionGroup.a 2) ∈ Subgroup.center J) : False := by
  classical
  have hodd : Odd (Nat.card (CFSG.oddCore J)) := odd_card_oddCore' J
  let fbar : QuaternionGroup 2 →* J ⧸ oddCore J :=
    (QuotientGroup.mk' (oddCore J)).comp f
  have hfbar : Function.Injective fbar :=
    injective_mk_comp_of_odd (oddCore J) hodd hf
  have hcover : IsOmegaCover (J ⧸ oddCore J) 6 (-1) :=
    isOmegaCover_oddCore_quotient hS hJ hJt
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨e⟩⟩ := hcover
  letI := i1
  letI := i2
  letI := i3
  let g : QuaternionGroup 2 →* OGroup Q :=
    (omegaGroup hQ).subtype.comp (e.toMonoidHom.comp fbar)
  let q : OGroup Q := g (QuaternionGroup.a 1)
  let r : OGroup Q := g (QuaternionGroup.xa 0)
  let y0 : OGroup Q := g (QuaternionGroup.a 2)
  let ω : omegaGroup hQ := e (fbar (QuaternionGroup.a 2))
  have hfc : fbar (QuaternionGroup.a 2) ∈ Subgroup.center (J ⧸ oddCore J) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (oddCore J))
      ⟨f (QuaternionGroup.a 2), hz, rfl⟩
  have hω_center : ω ∈ Subgroup.center (omegaGroup hQ) :=
    Subgroup.map_center_le_center e.surjective
      ⟨fbar (QuaternionGroup.a 2), hfc, rfl⟩
  have hω_ne : ω ≠ 1 := by
    intro h
    have h1 : fbar (QuaternionGroup.a 2) = 1 := by
      apply e.injective
      show e (fbar (QuaternionGroup.a 2)) = e 1
      rw [map_one]
      exact h
    have h2 : QuaternionGroup.a 2 = (1 : QuaternionGroup 2) := by
      refine hfbar ?_
      rw [h1, map_one]
    exact (by decide +kernel : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1) h2
  have hpi_mem : piOrth Q ∈ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ]
    exact ⟨by rw [hdim]; decide, by rw [hs, hdim]; decide⟩
  let p : omegaGroup hQ := ⟨piOrth Q, hpi_mem⟩
  have hp_ne : p ≠ 1 := by
    intro h
    exact piOrth_ne_one (by rw [hdim]; norm_num) (Subtype.ext_iff.mp h)
  have hp_sq : p * p = 1 := by
    apply Subtype.ext
    change piOrth Q * piOrth Q = (1 : OGroup Q)
    rw [piOrth_mul_self]
  have hp_order : orderOf p = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hp_sq) hp_ne
  have hp_center : p ∈ Subgroup.center (omegaGroup hQ) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (z : OGroup Q)
  have hcardz : Nat.card (Subgroup.zpowers p) = 2 := by
    rw [Nat.card_zpowers, hp_order]
  have hle : Subgroup.zpowers p ≤ Subgroup.center (omegaGroup hQ) :=
    Subgroup.zpowers_le_of_mem hp_center
  have hcenter_eq : Subgroup.center (omegaGroup hQ) = Subgroup.zpowers p :=
    (Subgroup.eq_of_le_of_card_ge hle
      (by rw [natCard_center_omegaGroup_six_minus hQ hdim hs, hcardz])).symm
  have hω_z : ω ∈ Subgroup.zpowers p := by
    rw [← hcenter_eq]
    exact hω_center
  have hω_eq : ω = p := by
    have hrange := (mem_zpowers_iff_mem_range_orderOf (x := p) (y := ω)).mp hω_z
    rw [hp_order] at hrange
    rw [Finset.mem_image] at hrange
    obtain ⟨k, hk, hkω⟩ := hrange
    rw [Finset.mem_range] at hk
    interval_cases k
    · simp at hkω
      exact absurd hkω.symm hω_ne
    · simpa using hkω.symm
  have hy0_eq : y0 = piOrth Q := by
    change (ω : OGroup Q) = piOrth Q
    rw [hω_eq]
  have ha1 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide +kernel
  have hxa0 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by decide +kernel
  have ha2 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
    decide +kernel
  have hxa1 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      (QuaternionGroup.a 1)⁻¹ * QuaternionGroup.xa 0 := by decide +kernel
  have hq2 : q * q = y0 := by
    change g (QuaternionGroup.a 1) * g (QuaternionGroup.a 1) = g (QuaternionGroup.a 2)
    rw [← map_mul, ha1]
  have hr2 : r * r = y0 := by
    change g (QuaternionGroup.xa 0) * g (QuaternionGroup.xa 0) = g (QuaternionGroup.a 2)
    rw [← map_mul, hxa0]
  have hyy : y0 * y0 = 1 := by
    change g (QuaternionGroup.a 2) * g (QuaternionGroup.a 2) = 1
    rw [← map_mul, ha2, map_one]
  have hrq : r * q = q⁻¹ * r := by
    change g (QuaternionGroup.xa 0) * g (QuaternionGroup.a 1) =
      (g (QuaternionGroup.a 1))⁻¹ * g (QuaternionGroup.xa 0)
    rw [← map_mul, hxa1, map_mul, map_inv]
  have hq8 := four_dvd_invDim_of_quaternion hQ (q := q) (r := r)
    (by rw [hq2, hr2]) (by rw [hq2, hyy]) hrq
  have h6 : invDim (piOrth Q) = 6 :=
    (congrArg Prod.fst (invType_piOrth hQ)).trans (by rw [hdim])
  have h4 : (4 : ℕ) ∣ 6 := by
    rw [hq2, hy0_eq] at hq8
    rw [h6] at hq8
    exact hq8.1
  exact absurd h4 (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
