module

public import CFSG.GH74.Uniqueness.SU.SU10Hyp

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU8

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_self (z : G) : z ∈ centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem hbar_orderOf {Hh : Subgroup G} {w : G} (hw : orderOf w = 2) (hwH : w ∈ Hh) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨w, hwH⟩) = 2 := by
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  have h2 : orderOf (⟨w, hwH⟩ : ↥Hh) = 2 :=
    (Subgroup.orderOf_coe (⟨w, hwH⟩ : ↥Hh)).symm.trans hw
  have hsq := map_mul_self_eq_one hwH hww
  have hne : QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨w, hwH⟩ ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥Hh) h1
    rw [h2] at hdvd
    exact (Nat.prime_two.coprime_iff_not_dvd.mp coprime_card_pPrimeCore) hdvd
  exact orderOf_eq_prime (by rw [sq]; exact hsq) hne

theorem zbar_orderOf {z : G} (hz : orderOf z = 2) : orderOf (zbar z) = 2 :=
  hbar_orderOf hz (mem_centralizer_self z)

omit [Finite G] in
theorem zbar_central (z : G) (x : Hbar (centralizer ({z} : Set G))) : x * zbar z = zbar z * x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 (centralizer ({z} : Set G))) x
  show QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set G))) y *
      QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set G))) ⟨z, mem_centralizer_self z⟩ =
    QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set G))) ⟨z, mem_centralizer_self z⟩ *
      QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set G))) y
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)

omit [Finite G] in
theorem zbar_mem_hbarImage {z : G} {X : Subgroup G} (hz : z ∈ X) :
    zbar z ∈ hbarImage (centralizer ({z} : Set G)) X :=
  Subgroup.mem_map.mpr ⟨⟨z, mem_centralizer_self z⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩

end CFSG.GH74.Uniqueness.SU.SU10
