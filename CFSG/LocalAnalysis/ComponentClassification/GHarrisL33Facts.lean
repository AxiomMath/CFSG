module

public import Certificates.Certificate22603

public section

namespace CFSG.ComponentClassification.GHarris.SCert.SE

theorem mul_gen0_comm : ∀ s : SE, s * gen 0 = gen 0 * s := by decide +kernel

theorem x_comm_a : invRep 5 * invRep 7 = invRep 7 * invRep 5 := by decide

theorem a3a4_comm_a : invRep 3 * invRep 7 = invRep 7 * invRep 3 := by decide

theorem a3a4_comm_t : invRep 3 * invRep 1 = invRep 1 * invRep 3 := by decide

theorem comm_x_a3a4 : invRep 1 = (invRep 5)⁻¹ * (invRep 3)⁻¹ * invRep 5 * invRep 3 := by decide

theorem invRep_mul_self' : ∀ i : Fin 9, invRep i * invRep i = 1 := by decide

theorem a3a4_ne_gen0 : invRep 3 ≠ gen 0 := by decide

theorem a3a4_ne_t : invRep 3 ≠ invRep 1 := by decide

theorem a3a4_ne_tz : invRep 3 ≠ invRep 1 * gen 0 := by decide

theorem conj_x_xt : (invRep 3)⁻¹ * gen 6 * invRep 3 = gen 6 * invRep 1 := by decide

theorem conj_x_xtz : (gen 2 * invRep 3)⁻¹ * gen 6 * (gen 2 * invRep 3) =
    gen 6 * invRep 1 * gen 0 := by decide

theorem comm_inv_X (u v : SE) (hu : u * gen 6 = gen 6 * u)
    (hv : v * gen 6 = gen 6 * v) (h2 : u⁻¹ * v⁻¹ * u * v * (u⁻¹ * v⁻¹ * u * v) = 1)
    (h1 : u⁻¹ * v⁻¹ * u * v ≠ 1) : u⁻¹ * v⁻¹ * u * v = gen 0 :=
  Certificates.certificate22603.1 u v hu hv h2 h1

theorem large_cent_X (w : SE) (h2 : w * w = 1) (h1 : w ≠ 1)
    (hx : w * gen 6 = gen 6 * w)
    (hc : 32 ≤ (Finset.univ.filter fun c : SE => c * gen 6 = gen 6 * c ∧ c * w = w * c).card) :
    w = gen 0 ∨ w = invRep 1 ∨ w = invRep 1 * gen 0 ∨ w = gen 6 ∨ w = gen 6 * gen 0 ∨
      w = gen 6 * invRep 1 ∨ w = gen 6 * invRep 1 * gen 0 :=
  Certificates.certificate22603.2.1 w h2 h1 hx hc

theorem classes_CXt (w : SE) (h2 : w * w = 1)
    (hx : w * gen 6 = gen 6 * w) (ht : w * invRep 1 = invRep 1 * w) (h1 : w ≠ 1)
    (hz : w ≠ gen 0) (ht' : w ≠ invRep 1) (htz : w ≠ invRep 1 * gen 0) :
    ∃ s : SE, s⁻¹ * w * s = invRep 5 ∨ s⁻¹ * w * s = invRep 7 ∨ s⁻¹ * w * s = invRep 8 :=
  Certificates.certificate22603.2.2 w h2 hx ht h1 hz ht' htz

end CFSG.ComponentClassification.GHarris.SCert.SE
