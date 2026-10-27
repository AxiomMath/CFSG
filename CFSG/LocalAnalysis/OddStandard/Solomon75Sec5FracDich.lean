module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusAmbient
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Cal
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Cover

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem isPCompIn_piece {u s : X} {Lu P : Subgroup X}
    (hLu : IsPCompIn 2 (centralizer ({u} : Set X)) Lu)
    (hPL : P ≤ Lu ⊓ centralizer ({s} : Set X))
    (hPn : (P.subgroupOf (Lu ⊓ centralizer ({s} : Set X))).Normal) (hPq : IsTwoGenQuasi ↥P) :
    IsPCompIn 2 (centralizer ({u} : Set X) ⊓ centralizer ({s} : Set X)) P := by
  set Cu : Subgroup X := centralizer ({u} : Set X) with hCu
  set D : Subgroup X := centralizer ({s} : Set X) with hD
  set A : Subgroup X := Lu ⊓ D with hA
  set H : Subgroup X := Cu ⊓ D with hH
  have hAH : A ≤ H := le_inf (inf_le_left.trans hLu.1) inf_le_right
  have hPH : P ≤ H := hPL.trans hAH
  have hAsub : (A.subgroupOf H).IsSubnormal := by
    have h1 : A.subgroupOf H =
        (Lu.subgroupOf Cu).comap (Subgroup.inclusion (inf_le_left : H ≤ Cu)) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hA, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
    rw [h1]
    exact (isPComponent_two_iff.1 hLu.2).1.comap _
  have hPsub : (P.subgroupOf H).IsSubnormal :=
    isSubnormal_subgroupOf_of_normal_of_subnormal hAH hPL hAsub hPn
  exact ⟨hPH, isPComponent_two_iff.2 ⟨hPsub, (isTwoGenQuasi_subgroupOf_iff hPH).2 hPq⟩⟩

theorem exists_isPCompIn_above_of_comp {u s : X} {E : Subgroup X} (hu2 : u * u = 1)
    (hus : s * u = u * s)
    (hE : IsPCompIn 2 (centralizer ({u} : Set X) ⊓ centralizer ({s} : Set X)) E) (huE : u ∈ E) :
    ∃ M : Subgroup X, IsPCompIn 2 (centralizer ({s} : Set X)) M ∧ E ≤ M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cu : Subgroup X := centralizer ({u} : Set X) with hCu
  set D : Subgroup X := centralizer ({s} : Set X) with hD
  have hEH : E ≤ Cu ⊓ D := hE.1
  have hEcomp : IsPComponent 2 (E.subgroupOf (Cu ⊓ D)) := hE.2
  have hECu : E ≤ Cu := hEH.trans inf_le_left
  have hED : E ≤ D := hEH.trans inf_le_right
  have huD : u ∈ D := Subgroup.mem_centralizer_singleton_iff.2 hus.symm
  set uD : ↥D := ⟨u, huD⟩ with huDdef
  have hcen : centralizer ({uD} : Set ↥D) = Cu.subgroupOf D := centralizer_singleton_subgroup huD
  have hEC_D : E.subgroupOf D ≤ centralizer ({uD} : Set ↥D) := by
    rw [hcen]
    exact Subgroup.subgroupOf_mono D hECu
  have huE' : uD ∈ E.subgroupOf D := huE
  have hu2' : uD ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hu2
  have hE_D : IsPComponent 2 ((E.subgroupOf D).subgroupOf (centralizer ({uD} : Set ↥D))) := by
    rw [hcen]
    exact (isPComponent_subgroupOf_subgroupOf_iff hECu hED).2 hEcomp
  have hEL_D : E.subgroupOf D ≤ pLayer ↥D 2 := by
    have hB : IsPGroup 2 (Subgroup.zpowers uD) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (by simpa using orderOf_dvd_of_pow_eq_one hu2' : orderOf uD ∣ 2 ^ 1)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hbal := layer_balance (Subgroup.zpowers uD) hB
    have hcz : centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D) =
        centralizer ({uD} : Set ↥D) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hEC_D' : E.subgroupOf D ≤
        centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D) := by
      rw [hcz]
      exact hEC_D
    have hE_D' : IsPComponent 2 ((E.subgroupOf D).subgroupOf
        (centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D))) := by
      rw [hcz]
      exact hE_D
    have h1 := le_sSup (s := {L | IsPComponent 2 L}) hE_D'
    have h2 := Subgroup.map_mono (f := (centralizer ((Subgroup.zpowers uD : Subgroup ↥D) :
      Set ↥D)).subtype) h1
    rw [Subgroup.map_subgroupOf_eq_of_le hEC_D'] at h2
    exact h2.trans hbal
  obtain ⟨M_D, hM_D, hEM_D⟩ := exists_isPComponent_le_of_mem_pLayer hEC_D huE' hu2' hE_D hEL_D
  refine ⟨M_D.map D.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · have h := Subgroup.comap_map_eq_self_of_injective D.subtype_injective M_D
    change IsPComponent 2 ((M_D.map D.subtype).comap D.subtype)
    rw [h]
    exact hM_D
  · have h1 := Subgroup.map_mono (f := D.subtype) hEM_D
    rwa [Subgroup.map_subgroupOf_eq_of_le hED] at h1

omit [Finite X] in
theorem comm_mem_of_cover {Lu E : Subgroup X} {u : X} (hEL : E ≤ Lu)
    (hEu : E ≤ centralizer ({u} : Set X)) (huLu : u ∈ Lu)
    (hcov : ∀ c ∈ Lu, ∃ a ∈ E, ∃ o ∈ oddCoreOf Lu, c = a * o) :
    ∀ l ∈ Lu, ⁅l, u⁆ ∈ oddCoreOf Lu := by
  intro l hl
  obtain ⟨a, ha, o, ho, rfl⟩ := hcov l hl
  have hau : ⁅a, u⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hEu ha))
  have hid : ⁅a * o, u⁆ = a * ⁅o, u⁆ * a⁻¹ * ⁅a, u⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hid, hau, mul_one]
  have hun : u ∈ normalizer (oddCoreOf Lu : Set X) := le_normalizer_oddCoreOf Lu huLu
  have hou : ⁅o, u⁆ ∈ oddCoreOf Lu := by
    have h1 : u * o⁻¹ * u⁻¹ ∈ oddCoreOf Lu :=
      (Subgroup.mem_normalizer_iff.1 hun _).1 ((oddCoreOf Lu).inv_mem ho)
    have : ⁅o, u⁆ = o * (u * o⁻¹ * u⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact (oddCoreOf Lu).mul_mem ho h1
  have han : a ∈ normalizer (oddCoreOf Lu : Set X) := le_normalizer_oddCoreOf Lu (hEL ha)
  exact (Subgroup.mem_normalizer_iff.1 han _).1 hou

end CFSG.OddStandard.Solomon75
