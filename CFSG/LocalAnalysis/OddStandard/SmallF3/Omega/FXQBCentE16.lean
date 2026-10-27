module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTransAux1
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem fx_qb_exists_E16 {B : Subgroup G} (hBL : B ≤ L) (hB : IsElemAb2 B 5)
    (hBZ : Nat.card ↥(B ⊓ centerIn L) ≤ 2) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    ∃ U : Subgroup ↥(omegaProj hQ), IsElemAb2 U 4 ∧
      ∀ u ∈ U, ∃ b : ↥L, (b : G) ∈ B ∧ ff6mPhi e b = u := by
  let ψ : ↥B →* ↥(omegaProj hQ) := (ff6mPhi e).comp (Subgroup.inclusion hBL)
  have hsq : ∀ b : ↥B, b ^ 2 = 1 := fun b => Subtype.ext (by simpa using hB.1.2 (b : G) b.2)
  have hker : Nat.card ψ.ker ≤ 2 := by
    have hle : ψ.ker.map B.subtype ≤ B ⊓ centerIn L := by
      rintro _ ⟨b, hb, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨b.2, ?_⟩
      have hcen : Subgroup.inclusion hBL b ∈ Subgroup.center ↥L := by
        rw [← ff6mPhi_ker e]
        exact hb
      exact Subgroup.mem_map_of_mem L.subtype hcen
    have h4 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective B.subtype_injective] at h4
    exact h4.trans hBZ
  have hcard : Nat.card ψ.ker * Nat.card ψ.range = 2 ^ 5 := by
    rw [Subgroup.card_ker_mul_card_range ψ]
    exact hB.2
  have hkpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have h16 : 2 ^ 4 ∣ Nat.card ψ.range := by
    rcases (by omega : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 2) with h | h
    · rw [h] at hcard
      exact ⟨2, by omega⟩
    · rw [h] at hcard
      exact ⟨1, by omega⟩
  haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨U, hUcard, -, hUle⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup ↥(omegaProj hQ))) (L := ψ.range) (n := 4) (by simp) h16 bot_le
  refine ⟨U, ?_, ?_⟩
  · unfold IsElemAb2 CFSG.Open.IsElemAbelian
    refine ⟨⟨?_, ?_⟩, hUcard⟩
    · haveI : IsMulCommutative ↥B := hB.1.1
      haveI : IsMulCommutative ↥ψ.range := inferInstance
      exact isMulCommutative_anti hUle
    · intro x hx
      obtain ⟨b, rfl⟩ := hUle hx
      rw [← map_pow, hsq b, map_one]
  · intro u hu
    obtain ⟨b, rfl⟩ := hUle hu
    exact ⟨Subgroup.inclusion hBL b, b.2, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
