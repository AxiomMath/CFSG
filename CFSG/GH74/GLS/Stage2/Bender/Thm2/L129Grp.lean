module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L129Aux
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L129

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section QP

variable {G : Type} [Group G] [Finite G]

theorem le_pPrimeCoreOf_of_normalized {Y D Y₀ : Subgroup G} (hD : D ≤ Y) (hY₀ : Y₀ ≤ Y)
    (hDodd : ∀ d ∈ D, Odd (orderOf d)) (hnorm : ∀ y ∈ Y₀, ∀ d ∈ D, y * d * y⁻¹ ∈ D)
    (hdec : ∀ y ∈ Y, ∃ y₀ ∈ Y₀, ∃ n ∈ pPrimeCoreOf 2 Y, y = y₀ * n) : D ≤ pPrimeCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥Y →* HBar Y := QuotientGroup.mk' (pPrimeCore 2 ↥Y)
  let DX : Subgroup ↥Y := D.subgroupOf Y
  let Db : Subgroup (HBar Y) := DX.map π
  have hDbn : Db.Normal := by
    constructor
    rintro _ ⟨d, hd, rfl⟩ g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ g
    obtain ⟨y₀, hy₀, n, ⟨n', hn', rfl⟩, hyn⟩ := hdec y y.2
    have hy : y = ⟨y₀, hY₀ hy₀⟩ * n' := Subtype.ext hyn
    have hπn : π n' = 1 := (QuotientGroup.eq_one_iff n').mpr hn'
    have hπy : (QuotientGroup.mk' (pPrimeCore 2 ↥Y) y) = π ⟨y₀, hY₀ hy₀⟩ := by
      show π y = _
      rw [hy, map_mul, hπn, mul_one]
    rw [hπy]
    refine ⟨⟨y₀, hY₀ hy₀⟩ * d * ⟨y₀, hY₀ hy₀⟩⁻¹, ?_, by simp⟩
    exact hnorm y₀ hy₀ d hd
  have hodd : Odd (Nat.card ↥Db) := by
    refine odd_card_of_forall_odd_orderOf fun x => ?_
    obtain ⟨d, hd, hdx⟩ := x.2
    have h1 : orderOf (x : HBar Y) = orderOf x := Subgroup.orderOf_coe x
    have h2 : orderOf (π d) ∣ orderOf d := orderOf_map_dvd π d
    have h3 : orderOf d = orderOf (d : G) := (Subgroup.orderOf_coe d).symm
    have h4 : Odd (orderOf (d : G)) := hDodd _ hd
    rw [← h1, ← hdx]
    exact Odd.of_dvd_nat (h3 ▸ h4) h2
  have hcop : Nat.Coprime 2 (Nat.card ↥Db) := (Nat.coprime_two_left).mpr hodd
  have hle : Db ≤ pPrimeCore 2 (HBar Y) := le_sSup ⟨hDbn, hcop⟩
  have hbot : pPrimeCore 2 (HBar Y) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥Y) 2
  intro d hd
  have hmem : π ⟨d, hD hd⟩ ∈ Db := ⟨⟨d, hD hd⟩, hd, rfl⟩
  have h1 : π ⟨d, hD hd⟩ = 1 := by
    have := hle hmem
    rwa [hbot, Subgroup.mem_bot] at this
  exact ⟨⟨d, hD hd⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

end QP

section P4

variable {G : Type} [Group G] [Finite G]

theorem odd_orderOf_of_mem_pPrimeCoreOf {N : Subgroup G} {x : G} (hx : x ∈ pPrimeCoreOf 2 N) :
    Odd (orderOf x) :=
  Nat.coprime_two_left.mp (coprime_orderOf_of_mem_pPrimeCoreOf Nat.prime_two hx)

end P4

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L129
