module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OB
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OW

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

namespace E3S3O

section Cit3


theorem stepB_proved {n : ℕ} : StepB n := by
  intro Y _ _ R S t J u L Rd Sd S' R' T W h s hs hsa hW
  obtain ⟨Q₀, hQ₀, w₀, hw₀, hw2, hw4, hw⟩ := h.exists_conj_sylow hs
  have hJa := h.std.xMem_J
  have hQ₀a : Q₀ ≤ Subgroup.centralizer ({u * t} : Set Y) :=
    hQ₀.1.trans h.core_le_centralizer_a
  have hQ₀c : IsSylow2In Q₀ (coreAt (u * t) (tightCore R)) :=
    (isSylow2In_coreAt_iff hJa).mpr ⟨hQ₀, hQ₀a⟩
  have hLY : coreAt (u * t) (tightCore R) ≤
      layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t) := coreAt_le_layerY hJa
  set π := QuotientGroup.mk' (classicalInvolutionOddCore
    ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t))) with hπ
  set Qb := (Q₀.subgroupOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t))).map π
    with hQbdef
  have hQb : IsSylow2In Qb
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore R)) :=
    isSylow2In_map_mk odd_natCard_oddCore_layerY (hQ₀c.subgroupOf hLY)
  have hKW := h.secImg_core_le
  have hw₀Y := hLY (hQ₀c.1 hw₀)
  have hwbQ : π ⟨w₀, hw₀Y⟩ ∈ Qb := ⟨⟨w₀, hw₀Y⟩, Subgroup.mem_subgroupOf.mpr hw₀, rfl⟩
  have hwbW : π ⟨w₀, hw₀Y⟩ ∈ orbW Rd (u * t) := hKW (hQb.1 hwbQ)
  refine ⟨Qb.subgroupOf (orbW Rd (u * t)), hQb.subgroupOf hKW, ⟨π ⟨w₀, hw₀Y⟩, hwbW⟩,
    Subgroup.mem_subgroupOf.mpr hwbQ, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime_pow (p := 2) (n := 1) (fun h1 => hw2 ?_) ?_
    · have h2 : π (⟨w₀, hw₀Y⟩ ^ 2) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val h1
      have h3 := (QuotientGroup.eq_one_iff _).mp h2
      have h4 : w₀ ^ 2 ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t)) :=
        mem_oddCoreOf_iff.mpr ⟨_, h3⟩
      have h5 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h4
        (hQ₀.2.1.to_le (Subgroup.zpowers_le.mpr (Q₀.pow_mem hw₀ 2)))
      rwa [pow_two] at h5
    · apply Subtype.ext
      show π ⟨w₀, hw₀Y⟩ ^ 2 ^ (1 + 1) = 1
      rw [← map_pow]
      have h6 : (⟨w₀, hw₀Y⟩ : ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t))) ^
          2 ^ (1 + 1) = 1 := Subtype.ext (by simpa using hw4)
      rw [h6, map_one]
  · intro x hx
    obtain ⟨x₀, hx₀, hx₀x⟩ := Subgroup.mem_subgroupOf.mp hx
    have hx₀Q : (x₀ : Y) ∈ Q₀ := Subgroup.mem_subgroupOf.mp hx₀
    have hsY := mem_normalizer_layerY (conjInvariant_conjClass (tightCore Rd)) hsa
    have hsx : s * (x₀ : Y) * s⁻¹ ∈ layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t) :=
      (Subgroup.mem_normalizer_iff.mp hsY _).mp x₀.2
    have e := s26Act_mk (layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t)) ⟨s, hsY⟩ x₀
      ⟨s * x₀ * s⁻¹, hsx⟩ rfl
    apply Subtype.ext
    show secAct (conjInvariant_conjClass (tightCore Rd)) hsa (x : SecQuot _ _) =
      π ⟨w₀, hw₀Y⟩ * (x : SecQuot _ _) * (π ⟨w₀, hw₀Y⟩)⁻¹
    rw [← hx₀x]
    show s26Act _ ⟨s, hsY⟩ (x₀ : SecQuot _ _) = _
    rw [e, ← map_inv, ← QuotientGroup.mk'_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hw _ hx₀Q

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
