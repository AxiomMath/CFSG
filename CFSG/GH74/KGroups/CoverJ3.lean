module

public import CFSG.GH74.KGroups.CoverJ3Check
public import CFSG.GH74.KGroups.CoverE16
public import CFSG.GH74.KGroups.CoverRank
public import CFSG.GH74.KGroups.Generic5
public import CFSG.GH74.Generic.Shapes
public meta import CFSG.GH74.KGroups.CoverJ3Check
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import all CFSG.Blueprint.NativeSporadic
public import CFSG.GH74.KGroups.CoverJ3Inputs
public meta import CFSG.GH74.KGroups.CoverJ3Inputs
public import Certificates.Certificate5111

public section

namespace CFSG.GH74.KGroups.J3

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

set_option compiler.extract_closed false

theorem j3_conjCheck :
    conjCheck (ops2 80) (include_str "../../Blueprint/Data/J3G1-f2r80B0.m1")
      (include_str "../../Blueprint/Data/J3G1-f2r80B0.m2") j3Words (List.range 80) = true :=
  Certificates.certificate5111

theorem exists_e_J3 :
    ∃ e : Fin 4 → NativeSporadic.J3, (∀ i, e i * e i = 1) ∧
    (∀ i j, e i * e j = e j * e i) ∧
    (∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => e i ^ (a i : ℕ)).prod ≠ 1) ∧
    ∀ a : Fin 4 → Fin 2, a ≠ 0 →
      ∃ g : NativeSporadic.J3, g * e 0 * g⁻¹ = (List.ofFn fun i => e i ^ (a i : ℕ)).prod :=
  exists_of_conjCheck (spec2 80) _ _ j3Words (List.range 80) j3_conjCheck

theorem prod_ofFn_four {G : Type*} [Group G] (e : Fin 4 → G) (a : Fin 4 → Fin 2) :
    (List.ofFn fun i => e i ^ (a i : ℕ)).prod =
      e 0 ^ (a 0 : ℕ) * (e 1 ^ (a 1 : ℕ) * (e 2 ^ (a 2 : ℕ) * e 3 ^ (a 3 : ℕ))) := by
  simp [List.ofFn_succ, List.prod_cons]

theorem cover_not_gen4_J3
    (K : Type) [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center K))
    (h : NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J3)
    (hZ : Subgroup.center K ≠ ⊥) : ¬ CFSG.GH74.Gen4 K := by
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  have hJ := center_quotient_eq_bot hperf hsimple
  obtain ⟨eJ⟩ := h
  obtain ⟨e, hsq, hcomm, hker, hconj⟩ := exists_e_J3
  have hE := exists_E16 (G := NativeSporadic.J3) e hsq hcomm hker hconj
  obtain ⟨E, hEcard, hE2, heE, hEconj⟩ := hE
  have hk : ∀ a : Fin 4 → Fin 2, a ≠ 0 →
      e 0 ^ (a 0 : ℕ) * (e 1 ^ (a 1 : ℕ) * (e 2 ^ (a 2 : ℕ) * e 3 ^ (a 3 : ℕ))) ≠ 1 := fun a ha => by
    rw [← prod_ofFn_four]
    exact hker a ha
  exact not_genLE4_of_double_cover hperf hZ2 hZ hJ (fun C _ _ hC ⟨eC⟩ =>
    not_genLE4_double_cover hC (⊤ : Subgroup NativeSporadic.J3)
      ((eC.trans eJ).trans Subgroup.topEquiv.symm) E le_top hEcard hE2 (e 0)
      (fun x hx hx1 => let ⟨g, hg⟩ := hEconj x hx hx1; ⟨g, Subgroup.mem_top g, hg⟩)
      (e 0) (e 1) (e 2) (heE 0) (heE 1) (heE 2)
      (by simpa using hk ![1, 0, 0, 0] (by decide))
      (by simpa using hk ![0, 1, 0, 0] (by decide))
      (by simpa using hk ![0, 0, 1, 0] (by decide))
      (by simpa using hk ![1, 1, 0, 0] (by decide))
      (by simpa using hk ![1, 0, 1, 0] (by decide))
      (by simpa using hk ![0, 1, 1, 0] (by decide))
      (by simpa using hk ![1, 1, 1, 0] (by decide)))

end CFSG.GH74.KGroups.J3
