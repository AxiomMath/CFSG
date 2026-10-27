module

public import CFSG.GH74.Uniqueness.SU.SU13TB1Core
public import CFSG.GH74.Uniqueness.SU.SU13TB1Conj
public import CFSG.GH74.Uniqueness.SU.SU4Quot2
public import CFSG.GH74.Uniqueness.SU.KI8B
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TB

open Subgroup CFSG.GH74.Uniqueness.SU.SU4

theorem exists_involution_lift {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] (π : Y →* Y')
    (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker)) {u : Y'} (hu : orderOf u = 2) :
    ∃ y : Y, orderOf y = 2 ∧ π y = u := by
  obtain ⟨x, rfl⟩ := hπ u
  have hdvd : 2 ∣ orderOf x := hu ▸ orderOf_map_dvd π x
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm
      exact absurd hm (orderOf_pos x).ne'
    · exact h0
  have hx2 : x ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    rw [← hu]; exact pow_orderOf_eq_one _
  have hord2 : orderOf (x ^ 2) = m := by
    rw [orderOf_pow_of_dvd (by norm_num) ⟨m, hm⟩, hm]
    omega
  have hmodd : Odd m := by
    have h1 : orderOf (x ^ 2) ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hx2
    rw [hord2] at h1
    exact Odd.of_dvd_nat hker h1
  refine ⟨x ^ m, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hm0.ne' ⟨2, by rw [hm]; ring⟩, hm, Nat.mul_div_cancel 2 hm0]
  · rw [map_pow]
    obtain ⟨k, hk⟩ := hmodd
    have hu2 : (π x) ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one _
    rw [hk, pow_succ, pow_mul, hu2, one_pow, one_mul]

variable {G : Type} [Group G] [Finite G]

theorem oneInvClass_mbar {C : Subgroup G}
    (h : ∀ u v : G, u ∈ C → v ∈ C → orderOf u = 2 → orderOf v = 2 → ∃ c ∈ C, c * u * c⁻¹ = v) :
    K.OneInvClass (Mbar C) := by
  intro u v hu hv
  obtain ⟨u', hu', rfl⟩ := exists_involution_lift (proj C) (proj_surjective C) (odd_card_ker_proj C) hu
  obtain ⟨v', hv', rfl⟩ := exists_involution_lift (proj C) (proj_surjective C) (odd_card_ker_proj C) hv
  have hu2 : orderOf (u' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu'
  have hv2 : orderOf (v' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hv'
  obtain ⟨c, hc, hcuv⟩ := h u' v' u'.2 v'.2 hu2 hv2
  refine isConj_iff.mpr ⟨proj C ⟨c, hc⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simpa using hcuv

theorem oc_inf_centralizer (hKI8b : K.KI8b) {C : Subgroup G}
    (hone : K.OneInvClass (Mbar C))
    {z : G} (hzC : z ∈ C) (hz : orderOf z = 2)
    {R : Subgroup G} (hR : IsSylowIn C R) (hzR : z ∈ R) (hRz : ∀ r ∈ R, r * z = z * r)
    (hGL : Nonempty (Mbar (C ⊓ centralizer ({z} : Set G)) ≃* GL (Fin 2) (ZMod 3))) :
    oc C ⊓ centralizer ({z} : Set G) = oc (C ⊓ centralizer ({z} : Set G)) := by
  set M : Subgroup G := C ⊓ centralizer ({z} : Set G) with hM
  have hMC : M ≤ C := inf_le_left
  let zc : ↥C := ⟨z, hzC⟩
  have hzc2 : zc * zc = 1 := by
    apply Subtype.ext
    change z * z = 1
    rw [← sq]; exact sq_eq_one_of_orderOf_eq_two hz
  have hzcord : orderOf zc = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hz
  set zb : Mbar C := proj C zc with hzb
  have hzb1 : zb ≠ 1 := by
    intro h
    have h1 : zc ∈ pPrimeCore 2 ↥C := by
      rw [← ker_proj C]; exact h
    have h2 : z ∈ oc C := mem_oc.mpr ⟨hzC, h1⟩
    have h3 := orderOf_dvd_natCard (⟨z, h2⟩ : oc C)
    rw [Subgroup.orderOf_mk, hz] at h3
    exact (Nat.not_even_iff_odd.mpr (odd_card_oc C)) (even_iff_two_dvd.mpr h3)
  have hzb2 : orderOf zb = 2 := by
    refine orderOf_eq_prime ?_ hzb1
    rw [hzb, ← map_pow]
    have : zc ^ 2 = 1 := by rw [pow_two]; exact hzc2
    rw [this, map_one]
  obtain ⟨T, hT⟩ := exists_sylow_barImage C hR
  have hzbT : zb ∈ (T : Subgroup (Mbar C)) := by
    rw [hT]; exact (mem_barImage C).mpr ⟨zc, hzR, rfl⟩
  have hTc : ∀ t ∈ (T : Subgroup (Mbar C)), t * zb = zb * t := by
    intro t ht
    rw [hT] at ht
    obtain ⟨r, hr, rfl⟩ := (mem_barImage C).mp ht
    rw [hzb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hRz r hr
  have hcomm : ∀ m : ↥M, proj C (Subgroup.inclusion hMC m) * zb = zb * proj C (Subgroup.inclusion hMC m) := by
    intro m
    rw [hzb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp m.2).2)
  let Φ : ↥M →* ↥(centralizer ({zb} : Set (Mbar C))) :=
    ((proj C).comp (Subgroup.inclusion hMC)).codRestrict (centralizer ({zb} : Set (Mbar C)))
      (fun m => mem_centralizer_singleton_iff.mpr (hcomm m))
  have hΦ : Function.Surjective Φ := by
    intro y
    have hy : y.1 ∈ (centralizer ({zc} : Set ↥C)).map (proj C) :=
      (centralizer_map_eq (proj C) (proj_surjective C) (odd_card_ker_proj C) hzc2).le y.2
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
    have hcM : (c : G) ∈ M := mem_inf.mpr ⟨c.2, by
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.mp hc
      exact congrArg Subtype.val this⟩
    refine ⟨⟨c, hcM⟩, Subtype.ext ?_⟩
    exact hcy
  have hΦker : ∀ m : ↥M, Φ m = 1 ↔ (⟨(m : G), hMC m.2⟩ : ↥C) ∈ pPrimeCore 2 ↥C := by
    intro m
    constructor
    · intro h
      have h1 : proj C (Subgroup.inclusion hMC m) = 1 := congrArg Subtype.val h
      rw [← ker_proj C]; exact h1
    · intro h
      apply Subtype.ext
      have : proj C (Subgroup.inclusion hMC m) = 1 := by
        rw [← MonoidHom.mem_ker, ker_proj C]; exact h
      exact this
  have hkerodd : ¬ 2 ∣ Nat.card Φ.ker := by
    let κ : ↥Φ.ker →* ↥(pPrimeCore 2 ↥C) :=
      ((Subgroup.inclusion hMC).comp Φ.ker.subtype).codRestrict (pPrimeCore 2 ↥C)
        (fun m => (hΦker m.1).mp m.2)
    have hinj : Function.Injective κ := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥(pPrimeCore 2 ↥C) => ((w : ↥C) : G)) hab
    have hdvd := Subgroup.card_dvd_of_injective _ hinj
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥C)) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥C))
    have := Odd.of_dvd_nat hodd hdvd
    intro h2
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
  have hpre := (CFSG.prime_complement_kernel_core_preimage (p := 2) Φ hΦ hkerodd).1
  let ψ : ↥M →* K.CBar (Mbar C) zb :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({zb} : Set (Mbar C))))).comp Φ
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(centralizer ({zb} : Set (Mbar C))))).comp hΦ
  have hψker : ψ.ker = pPrimeCore 2 ↥M := by
    rw [← hpre]
    ext m
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_comap]
  let e1 : Mbar M ≃* K.CBar (Mbar C) zb :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  obtain ⟨e2⟩ := hGL
  have hGL' : Nonempty (K.CBar (Mbar C) zb ≃* GL (Fin 2) (ZMod 3)) := ⟨e1.symm.trans e2⟩
  have hO : pPrimeCore 2 (Mbar C) = ⊥ := GLS.pPrimeCore_quotient_eq_bot (↥C)
  obtain ⟨-, hbot⟩ := hKI8b (Mbar C) hO hone T zb hzbT hzb2 hTc hGL'
  have hbot' : pPrimeCore 2 ↥M = Φ.ker := by
    rw [← hpre, hbot]; rfl
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨hxC, hxc⟩ := mem_oc.mp hx1
    have hxM : x ∈ M := mem_inf.mpr ⟨hxC, hx2⟩
    refine mem_oc.mpr ⟨hxM, ?_⟩
    rw [hbot']
    exact (hΦker ⟨x, hxM⟩).mpr hxc
  · intro hx
    obtain ⟨hxM, hxc⟩ := mem_oc.mp hx
    rw [hbot'] at hxc
    exact ⟨mem_oc.mpr ⟨hMC hxM, (hΦker ⟨x, hxM⟩).mp hxc⟩, (mem_inf.mp hxM).2⟩

end CFSG.GH74.Uniqueness.SU.SU13.TB
