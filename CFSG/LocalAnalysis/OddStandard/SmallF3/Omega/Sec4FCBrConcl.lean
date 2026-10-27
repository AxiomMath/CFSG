module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCBrSetU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec4FC_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem Sec4FDConcl.of_oddCent {L : Subgroup G} {s : G} {D E O : Subgroup G} (hDE : D ≤ E)
    (hEO : E ≤ D ⊔ O) (hO : Sec4FOddCent O E) (h : Sec4FDConcl L s E) :
    Sec4FDConcl L s D := by
  obtain ⟨ha, hb, hc, hd, he⟩ := h
  have hU : ∀ v, Asc82SetU D v → Asc82SetU E v :=
    fun v hv => (Asc82SetU.iff_of_oddCent hDE hEO hO).mpr hv
  have hUm : ∀ v, Asc82SetU E v → Asc82SetU D v :=
    fun v hv => (Asc82SetU.iff_of_oddCent hDE hEO hO).mp hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact ha v (hU v hv)
  · intro v v' hv hv' hty
    obtain ⟨e, heE, hev⟩ := hb v v' (hU v hv) (hU v' hv') hty
    have hc' : ∀ o ∈ O, ∀ d ∈ D, o * d = d * o := fun o ho d hd => hO.1 o ho d (hDE hd)
    obtain ⟨d, hd, o, ho, heq⟩ := (sec4FC_mem_sup_iff hc').mp (hEO heE)
    refine ⟨d, hd, ?_⟩
    rw [hev, heq]
    have hov : o * v = v * o := hO.1 o ho v (hDE hv.1)
    calc
      (d * o) * v * (d * o)⁻¹ = d * (o * v * o⁻¹) * d⁻¹ := by group
      _ = d * v * d⁻¹ := by rw [hov]; group
  · obtain ⟨v, hv, hty⟩ := hc
    exact ⟨v, hUm v hv, hty⟩
  · obtain ⟨v, hv, hty⟩ := hd
    exact ⟨v, hUm v hv, hty⟩
  · intro v hv h2
    exact he v (hU v hv) h2

theorem sec4FC_oddCent_odd [Finite G] {L : Subgroup G} (hL : IsOmega7Group L) {E : Subgroup G}
    (hE : E ≤ L) : Sec4FOddCent (Sec4FOdd L) E := by
  have hmodel := hL.2.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
  have hsimple : IsSimpleGroup (↥L ⧸ oddCore ↥L) :=
    (CFSG.LieType.Simplicity.fam_classical_converse (↥L ⧸ oddCore ↥L)
      ⟨.POmegaOdd, 3, 3, 1, hmodel⟩).2.2
  have hne : oddCore ↥L ≠ ⊤ := by
    intro htop
    haveI : Nontrivial (↥L ⧸ oddCore ↥L) := hsimple.toNontrivial
    haveI : Subsingleton (↥L ⧸ oddCore ↥L) := (QuotientGroup.subsingleton_iff).mpr htop
    exact not_subsingleton (↥L ⧸ oddCore ↥L) inferInstance
  have hle : oddCore ↥L ≤ Subgroup.center ↥L := oddCore_le_center_of_isQuasisimple hL.1 hne
  refine ⟨?_, ?_⟩
  · intro o ho x hx
    unfold Sec4FOdd at ho
    rw [Subgroup.mem_map] at ho
    obtain ⟨ô, hô, rfl⟩ := ho
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp (hle hô) ⟨x, hE hx⟩)).symm
  · unfold Sec4FOdd
    rw [Subgroup.card_subtype]
    exact sec4FC_odd_card_oddCore ↥L

theorem sec4FC_inf_conjugate_le_left {t : G} {L : Subgroup G} (ht : t ∈ centralizer (L : Set G))
    (g : G) : L ⊓ CFSG.conjugate L g ≤ L ⊓ centralizer ({g⁻¹ * t * g} : Set G) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hmem : g * x * g⁻¹ ∈ L := (mem_conjugate_iff L g x).mp hx.2
  have hcomm : (g * x * g⁻¹) * t = t * (g * x * g⁻¹) :=
    Subgroup.mem_centralizer_iff.mp ht (g * x * g⁻¹) hmem
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc
    x * (g⁻¹ * t * g) = g⁻¹ * (g * x * g⁻¹ * t) * g := by group
    _ = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [hcomm]
    _ = (g⁻¹ * t * g) * x := by group

theorem sec4FC_inf_conjugate_le_right {t : G} {L : Subgroup G} (ht : t ∈ centralizer (L : Set G))
    (g : G) : L ⊓ CFSG.conjugate L g ≤ CFSG.conjugate L g ⊓ centralizer ({t} : Set G) := by
  intro x hx
  refine ⟨hx.2, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp ht x hx.1)

end CFSG.OddStandard.SmallF3.Omega
