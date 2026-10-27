module

public import Certificates.Certificate55121

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem mem_P :
    r0P ∈ P ∧ u0P ∈ P ∧ v0P ∈ P ∧ u1P ∈ P ∧ v1P ∈ P ∧ s01P ∈ P ∧ w0P ∈ P ∧
    y0P ∈ P ∧ ∀ c ∈ gamP, c ∈ P :=
  Certificates.certificate55121.1

theorem rel_facts :
    r0P ≠ 1 ∧ r0P * r0P = 1 ∧ u0P * u0P = r0P ∧ (∀ x, x ∈ K0 ↔ x ∈ L0P) ∧
      u1P * u1P = r0P ∧ (∀ x, x ∈ K1 ↔ x ∈ L1P) ∧ d2P * u0P = u0P * d2P ∧
      d2P * v0P = v0P * d2P ∧ d2P * v1P ≠ v1P * d2P ∧ s01P * s01P = 1 ∧
      s01P * r0P = r0P * s01P ∧ conjSub s01P K1 = K0 ∧ conjSub s01P K0 = K1 ∧
      w0P * r0P = r0P * w0P ∧ (∀ c ∈ gamP, conjSub c K0 = K0) ∧
      y0P * (y0P * y0P) = 1 ∧ y0P * d2P = d2P * y0P ∧ conjSub y0P K0 = K0 ∧
      y0P * u0P ≠ u0P * y0P :=
  Certificates.certificate55121.2.1

theorem ident {K : Subgroup (Equiv.Perm (Fin 820))} (hd : Vtx.AmbientQuatDatum P K r0P) :
    K = K0 ∨ K = K1 :=
  Certificates.certificate55121.2.2 K hd

theorem mem_K1_iff (x : Equiv.Perm (Fin 820)) : x ∈ K1 ↔ x ∈ L1P := rel_facts.2.2.2.2.2.1 x

theorem closure_le_P {a b : Equiv.Perm (Fin 820)} (ha : a ∈ P) (hb : b ∈ P) :
    Subgroup.closure {a, b} ≤ P := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ha
  · exact hb

theorem K0_le_P : K0 ≤ P := closure_le_P mem_P.2.1 mem_P.2.2.1

theorem commute_closure {y a b : Equiv.Perm (Fin 820)} (ha : y * a = a * y) (hb : y * b = b * y) :
    ∀ c ∈ Subgroup.closure {a, b}, y * c = c * y := by
  have hle : Subgroup.closure {a, b} ≤ Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 820))) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · exact ha.symm
    · exact hb.symm
  exact fun c hc => (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm

theorem commute_d2_K0 : ∀ c ∈ K0, d2P * c = c * d2P :=
  commute_closure rel_facts.2.2.2.2.2.2.1 rel_facts.2.2.2.2.2.2.2.1

theorem v1_mem_K1 : v1P ∈ K1 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem u0_mem_K0 : u0P ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem r0_mem_K0 : r0P ∈ K0 := by
  rw [← rel_facts.2.2.1]
  exact K0.mul_mem u0_mem_K0 u0_mem_K0

theorem conjSub_s01 : conjSub s01P K1 = K0 := rel_facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem conjSub_gam {c : Equiv.Perm (Fin 820)} (hc : c ∈ gamP) : conjSub c K0 = K0 :=
  rel_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c hc

theorem conjSub_y0 : conjSub y0P K0 = K0 := rel_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
