module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkAbs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

namespace Pk

theorem mem_centB_iff {L : List P45} {t x : P45} : x ∈ centB L t ↔ x ∈ L ∧ x * t = t * x := by
  simp [centB]

theorem mem_Cl {x : P45} : x ∈ Cl ↔ x ∈ Cs := by
  have h : x ∈ centB (elemsT QP45) tA ↔ x ∈ elemsT QP45 ∧ x * tA = tA * x := mem_centB_iff
  rw [mem_elemsT QP45 QP45_ok] at h
  rw [Cs, P0, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact h

theorem mem_CBl {x : P45} : x ∈ CBl ↔ x ∈ CBs := by
  have h : x ∈ centB (elemsT QP45) tB ↔ x ∈ elemsT QP45 ∧ x * tB = tB * x := mem_centB_iff
  rw [mem_elemsT QP45 QP45_ok] at h
  rw [CBs, P0, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact h

theorem card_Cs :
    Nat.card Cs = 576 :=
  facts.cardC

theorem card_CBs :
    Nat.card CBs = 96 :=
  facts.cardCB

theorem orderOf_tA : orderOf tA = 2 := facts.ordA

theorem tA_mem : tA ∈ P0 := by
  obtain ⟨-, -, h3, -, A, hA⟩ := rho_props
  exact hA ▸ h3 A

theorem gz_mem : gz ∈ Cs :=
  facts.memG

theorem exists_cover_pk {p : P45}
    (hp : p ∈ P0) (h2 : orderOf p = 2) :
    ∃ c ∈ P0, c * p * c⁻¹ = tA ∨ c * p * c⁻¹ = tB := by
  have hp2 : p * p = 1 := by
    have := pow_orderOf_eq_one p
    rwa [h2, pow_two] at this
  have hp1 : p ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at h2
    omega
  exact facts.cover p hp hp2 hp1

theorem noOdd_Cs :
    ∀ N : Subgroup ↥Cs, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  obtain ⟨h1, h2⟩ := facts.noOddA
  refine noOdd_of_tests (k := 6) (m := 9) (fun x => mem_Cl) (by norm_num)
    (by rw [card_Cs]; norm_num) (fun o ho ho1 ho3 => ?_) fun x hx => h2 x (mem_Cl.1 hx)
  obtain ⟨c, hc, hc3⟩ := h1 o (mem_Cl.1 ho) ho1 ho3
  exact ⟨c, mem_Cl.2 hc, hc3⟩

theorem noOdd_CBs :
    ∀ N : Subgroup ↥CBs, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  obtain ⟨h1, h2⟩ := facts.noOddB
  refine noOdd_of_tests (k := 5) (m := 3) (fun x => mem_CBl) (by norm_num)
    (by rw [card_CBs]; norm_num) (fun o ho ho1 ho3 => ?_) fun x hx => h2 x (mem_CBl.1 hx)
  obtain ⟨c, hc, hc3⟩ := h1 o (mem_CBl.1 ho) ho1 ho3
  exact ⟨c, mem_CBl.2 hc, hc3⟩

end Pk

end CFSG.OddStandard.SmallF3.Omega
