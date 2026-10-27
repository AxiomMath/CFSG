module

public import Certificates.Certificate840003

public noncomputable section

namespace CFSG.CGT.Hall82.DModel

open CFSG.CGT.Hall82 CFSG.ComponentClassification.AS81.Hexa

theorem rm_mul (e f : Fin 8) :
    hallRMPerm e * hallRMPerm f = hallRMPerm (xor8 e f) :=
  Certificates.certificate840003.1 e f

theorem rm_inj : Function.Injective hallRMPerm :=
  Certificates.certificate840003.2.1

theorem mem_rm_iff (x : Equiv.Perm (Fin 64)) :
    x ∈ hallRM ↔ ∃ e, hallRMPerm e = x :=
  Certificates.certificate840003.2.2.1 x

theorem rm_le : hallRM ≤ hexaM :=
  Certificates.certificate840003.2.2.2.1

theorem rm_fix (e : Fin 8) : hallRMPerm e 5 = 5 :=
  Certificates.certificate840003.2.2.2.2.1 e

theorem rm_not_le : ¬ hallRM ≤ hexaL :=
  Certificates.certificate840003.2.2.2.2.2.1

theorem le_rm (B : Subgroup (Equiv.Perm (Fin 64)))
    (hB : B ≤ hexaM) (h2 : IsPGroup 2 B) (hfix : ∀ b ∈ B, b 5 = 5)
    (hnorm : ∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ B, a * b * a⁻¹ ∈ B) : B ≤ hallRM :=
  Certificates.certificate840003.2.2.2.2.2.2.1 B hB h2 hfix hnorm

theorem rm_le_or_quad
    (B : Subgroup (Equiv.Perm (Fin 64))) (hB : B ≤ hallRM)
    (hnorm : ∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ B, a * b * a⁻¹ ∈ B) :
    hallRM ≤ B ∨ ∀ a ∈ B, ∀ b ∈ B, ∀ v,
      xorF (xorF (a (b v)) (a v)) (xorF (b v) v) = 0 :=
  Certificates.certificate840003.2.2.2.2.2.2.2.1 B hB hnorm

theorem u_inv :
    ∀ s ∈ hexaM, s 5 = 5 → ∀ v, InHallU v → InHallU (s v) :=
  Certificates.certificate840003.2.2.2.2.2.2.2.2.1

theorem rm_comm_u (e : Fin 8) (v : Fin 64)
    (hv : InHallU v) : xorF (hallRMPerm e v) v = 0 ∨ xorF (hallRMPerm e v) v = 5 :=
  Certificates.certificate840003.2.2.2.2.2.2.2.2.2.1 e v hv

theorem rm_eq_zero_of_fix_u (e : Fin 8)
    (hfix : ∀ v, InHallU v → hallRMPerm e v = v) : e = 0 :=
  Certificates.certificate840003.2.2.2.2.2.2.2.2.2.2.1 e hfix

theorem fix_rm (v : Fin 64)
    (hfix : ∀ e, hallRMPerm e v = v) : v = 0 ∨ v = 5 :=
  Certificates.certificate840003.2.2.2.2.2.2.2.2.2.2.2.1 v hfix

theorem u_maximal
    (W : Set (Fin 64)) (hW : ∀ v ∈ W, ∀ w ∈ W, xorF v w ∈ W)
    (hU : ∀ v, InHallU v → v ∈ W)
    (hInv : ∀ a ∈ hexaL, a 5 = 5 → ∀ w ∈ W, a w ∈ W) :
    W = {v | InHallU v} ∨ W = Set.univ :=
  Certificates.certificate840003.2.2.2.2.2.2.2.2.2.2.2.2 W hW hU hInv

end CFSG.CGT.Hall82.DModel
