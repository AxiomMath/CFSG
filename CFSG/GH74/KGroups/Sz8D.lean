module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic10
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Sz8
public import CFSG.GH74.KGroups.Sz8Tables
public import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.Sz8
public meta import CFSG.GH74.KGroups.Sz8Tables
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.GH74.KGroups.Generic10
public import CFSG.GH74.KGroups.Sz8DInputs
public meta import CFSG.GH74.KGroups.Sz8DInputs
public import Certificates.Certificate5128
public import Certificates.Certificate5129
public import Certificates.Certificate5130

public section

namespace CFSG.GH74.KGroups.Sz8D

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8

@[expose] def S0 : Subgroup (Equiv.Perm (Fin 65)) := QS.originalSubgroup

@[expose] def E0 : Subgroup (Equiv.Perm (Fin 65)) :=
  QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65)))

theorem E0_le : E0 ≤ S0 := inf_le_left

theorem E0_central : ∀ w ∈ E0, ∀ s ∈ S0, w * s = s * w := fun _ hw s hs =>
  (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw).2 s hs).symm

theorem ys_mem : ∀ j, ys j ∈ E0 :=
  Certificates.certificate5129.2.2.1

theorem ys0_ne : ys 0 ≠ 1 :=
  Certificates.certificate5129.2.2.2.1

theorem fix_unique :
    ∀ i : Fin 65, (∀ s ∈ elemsT QS, s i = i) → i = cpt := fun i h =>
  Certificates.certificate5129.2.1 i fun s hs => h s ((mem_elemsT QS QS_ok s).2 hs)

theorem S0_fix :
    ∀ s ∈ elemsT QS, s cpt = cpt := fun s hs =>
  Certificates.certificate5129.1 s ((mem_elemsT QS QS_ok s).1 hs)

theorem hfin_sz8
    (κ : Equiv.Perm (Fin 65) → Equiv.Perm (Fin 65) → ZMod 2)
    (h1 : ∀ x ∈ S0, ∀ x' ∈ S0, ∀ y ∈ E0, κ (x * x') y = κ x y + κ x' y)
    (h2 : ∀ x ∈ S0, ∀ y ∈ E0, ∀ y' ∈ E0, κ x (y * y') = κ x y + κ x y')
    (h3 : ∀ w ∈ E0, ∀ y ∈ E0, κ w y = 0) (h5 : ∀ x ∈ S0, κ x (x ^ 2) = 0)
    (h4t : ∀ s ∈ S0, ∀ t ∈ E0, κ (tt * s * tt⁻¹) (tt * t * tt⁻¹) = κ s t)
    (σ : Equiv.Perm (Fin 65)) (hσA : σ ∈ QA.originalSubgroup) (hσfix : σ cpt = cpt)
    (hσP : σ ∉ QP.originalSubgroup)
    (h4σ : ∀ s ∈ S0, ∀ t ∈ E0, κ (σ * s * σ⁻¹) (σ * t * σ⁻¹) = κ s t) :
    ∀ s ∈ S0, ∀ t ∈ E0, κ s t = 0 :=
  Certificates.certificate5129.2.2.2.2 κ h1 h2 h3 h5 h4t σ hσA hσfix hσP h4σ

end CFSG.GH74.KGroups.Sz8D
