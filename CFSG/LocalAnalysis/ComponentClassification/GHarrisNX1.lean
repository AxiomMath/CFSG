module

public import Certificates.Certificate22610
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32a
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

namespace SCert.SE

theorem f_gen6 : fA (gen 6) = 1 ∧ fB (gen 6) = 0 := by decide

theorem y_mem_LXX : invRep 6 ∈ LXX := by decide

theorem noncomm_LZX : (⟨4, 0, 0, 0⟩ : SE) ∈ LZX ∧ (⟨5, 1, 1, 0⟩ : SE) ∈ LZX ∧
    (⟨4, 0, 0, 0⟩ : SE) * ⟨5, 1, 1, 0⟩ ≠ ⟨5, 1, 1, 0⟩ * ⟨4, 0, 0, 0⟩ := by decide


theorem mem_Xlist : ∀ s : SE, s * gen 6 = gen 6 * s → s ∈ Xlist :=
  Certificates.certificate22610.1

theorem inv_X_cases : ∀ s ∈ Xlist, s * s = 1 → s ≠ 1 →
    s ∈ LZX ∨ s = gen 6 ∨ s ∈ LXZ ∨ s ∈ LXX := Certificates.certificate22610.2.1

theorem LZX_spec : ∀ s ∈ LZX, (∃ c : SE, c⁻¹ * s * c ∈ ZrepsA) ∧
    ∃ c : SE, c⁻¹ * (s * gen 6) * c ∈ Xreps := Certificates.certificate22610.2.2.1

theorem LXZ_spec : ∀ s ∈ LXZ, (∃ c : SE, c⁻¹ * s * c ∈ Xreps) ∧
    ∃ c : SE, c⁻¹ * (s * gen 6) * c ∈ ZrepsA := Certificates.certificate22610.2.2.2.1

theorem LXX_spec : ∀ s ∈ LXX, (∃ c : SE, c⁻¹ * s * c ∈ Xreps) ∧
    ∃ c : SE, c⁻¹ * (s * gen 6) * c ∈ Xreps := Certificates.certificate22610.2.2.2.2.1

theorem LZX_sub : ∀ s ∈ LZX, s ∈ Xlist := Certificates.certificate22610.2.2.2.2.2.1

theorem mem_Xlist_comm : ∀ s ∈ Xlist, s * gen 6 = gen 6 * s :=
  Certificates.certificate22610.2.2.2.2.2.2.1

theorem LZX_inv : ∀ s ∈ LZX, s * s = 1 := Certificates.certificate22610.2.2.2.2.2.2.2.1

theorem fA_mul : ∀ s ∈ Xlist, ∀ t ∈ Xlist, fA (s * t) = fA s + fA t :=
  Certificates.certificate22610.2.2.2.2.2.2.2.2.1

theorem fB_mul : ∀ s ∈ Xlist, ∀ t ∈ Xlist, fB (s * t) = fB s + fB t :=
  Certificates.certificate22610.2.2.2.2.2.2.2.2.2.1

theorem f_LZX : ∀ s ∈ LZX, fA s = 0 ∧ fB s = 0 :=
  Certificates.certificate22610.2.2.2.2.2.2.2.2.2.2.1

theorem f_LXZ : ∀ s ∈ LXZ, fA s = 1 ∧ fB s = 0 :=
  Certificates.certificate22610.2.2.2.2.2.2.2.2.2.2.2.1

theorem f_LXX : ∀ s ∈ LXX, fB s = 1 := Certificates.certificate22610.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem center_LZX : ∀ s ∈ LZX, (∀ u ∈ LZX, s * u = u * s) →
    s = gen 0 ∨ s = invRep 1 ∨ s = invRep 1 * gen 0 :=
  Certificates.certificate22610.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem mem_Tlist : ∀ s : SE, s * invRep 3 = invRep 3 * s → s ∈ Tlist :=
  Certificates.certificate22610.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem commX : ∀ p ∈ Xlist, ∀ q ∈ Xlist, p⁻¹ * q⁻¹ * p * q * (p⁻¹ * q⁻¹ * p * q) = 1 →
    p⁻¹ * q⁻¹ * p * q = 1 ∨ p⁻¹ * q⁻¹ * p * q = gen 0 :=
  Certificates.certificate22610.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem commT : ∀ p ∈ Tlist, ∀ q ∈ Tlist, p⁻¹ * q⁻¹ * p * q * (p⁻¹ * q⁻¹ * p * q) = 1 →
    p⁻¹ * q⁻¹ * p * q = 1 ∨ p⁻¹ * q⁻¹ * p * q = gen 0 ∨ p⁻¹ * q⁻¹ * p * q = invRep 3 ∨
      p⁻¹ * q⁻¹ * p * q = invRep 3 * gen 0 :=
  Certificates.certificate22610.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem a3a4z_conj : ∃ c : SE, c⁻¹ * (invRep 3 * gen 0) * c = invRep 3 :=
  Certificates.certificate22610.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end SCert.SE

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

@[expose] def eS : ↥(D.S : Subgroup G) ≃* SE :=
  ((MonoidHom.ofInjective D.toG_injective).trans (MulEquiv.subgroupCongr D.range_toG)).symm

omit [Finite G] in
theorem toG_eS (g : ↥(D.S : Subgroup G)) : D.toG (D.eS g) = g := by
  have h := (MonoidHom.ofInjective D.toG_injective).trans
    (MulEquiv.subgroupCongr D.range_toG) |>.apply_symm_apply g
  exact congrArg Subtype.val h

omit [Finite G] in
theorem eS_toG (s : SE) : D.eS ⟨D.toG s, D.toG_mem s⟩ = s := D.toG_injective (D.toG_eS _)

omit [Finite G] in
theorem eS_mem_Xlist {g : G} (hg : g ∈ D.X) : D.eS ⟨g, (mem_inf.mp hg).1⟩ ∈ SE.Xlist := by
  apply SE.mem_Xlist
  apply D.toG_injective
  rw [map_mul, map_mul, D.toG_eS]
  exact mem_centralizer_singleton_iff.mp (mem_inf.mp hg).2

@[expose] def phiA : ↥D.X →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (SE.fA (D.eS ⟨g, (mem_inf.mp g.2).1⟩))
  map_one' := by
    rw [show (⟨((1 : ↥D.X) : G), _⟩ : ↥(D.S : Subgroup G)) = 1 from rfl, map_one]
    rfl
  map_mul' g h := by
    rw [show (⟨((g * h : ↥D.X) : G), _⟩ : ↥(D.S : Subgroup G)) =
      ⟨(g : G), (mem_inf.mp g.2).1⟩ * ⟨(h : G), (mem_inf.mp h.2).1⟩ from rfl, map_mul,
      SE.fA_mul _ (D.eS_mem_Xlist g.2) _ (D.eS_mem_Xlist h.2)]
    rfl

@[expose] def phiB : ↥D.X →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (SE.fB (D.eS ⟨g, (mem_inf.mp g.2).1⟩))
  map_one' := by
    rw [show (⟨((1 : ↥D.X) : G), _⟩ : ↥(D.S : Subgroup G)) = 1 from rfl, map_one]
    rfl
  map_mul' g h := by
    rw [show (⟨((g * h : ↥D.X) : G), _⟩ : ↥(D.S : Subgroup G)) =
      ⟨(g : G), (mem_inf.mp g.2).1⟩ * ⟨(h : G), (mem_inf.mp h.2).1⟩ from rfl, map_mul,
      SE.fB_mul _ (D.eS_mem_Xlist g.2) _ (D.eS_mem_Xlist h.2)]
    rfl

omit [Finite G] in
theorem phiA_toG {s : SE} (hs : D.toG s ∈ D.X) :
    D.phiA ⟨D.toG s, hs⟩ = Multiplicative.ofAdd (SE.fA s) := by
  change Multiplicative.ofAdd (SE.fA (D.eS ⟨D.toG s, _⟩)) = _
  rw [D.eS_toG]

omit [Finite G] in
theorem phiB_toG {s : SE} (hs : D.toG s ∈ D.X) :
    D.phiB ⟨D.toG s, hs⟩ = Multiplicative.ofAdd (SE.fB s) := by
  change Multiplicative.ofAdd (SE.fB (D.eS ⟨D.toG s, _⟩)) = _
  rw [D.eS_toG]

end GHSylow

end CFSG.ComponentClassification.GHarris
