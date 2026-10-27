module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.A5Basic

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup

open scoped commutatorElement

theorem eq_of_le_of_quasisimple_alt5 {K : Type*} [Group K] [Finite K] {E B : Subgroup K}
    (hq : CFSG.IsQuasisimple ↥E) (hBE : B ≤ E) (eB : ↥B ≃* alternatingGroup (Fin 5))
    (eE : (↥E ⧸ center ↥E) ≃* alternatingGroup (Fin 5)) : B = E := by
  classical
  let Z : Subgroup ↥E := center ↥E
  have hcardB : Nat.card ↥(B.subgroupOf E) = 60 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBE).toEquiv]
    exact PropA.alt5_card eB
  have hcardQ : Nat.card (↥E ⧸ Z) = 60 := by
    simpa [Z] using PropA.alt5_card eE
  have eB' : ↥(B.subgroupOf E) ≃* alternatingGroup (Fin 5) :=
    (Subgroup.subgroupOfEquivOfLe hBE).trans eB
  let f : ↥(B.subgroupOf E) →* (↥E ⧸ Z) :=
    (QuotientGroup.mk' Z).comp (B.subgroupOf E).subtype
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hbZ : (b : ↥E) ∈ Z := by
      rw [← QuotientGroup.eq_one_iff (b : ↥E)]
      simpa [f] using hb
    have hcomm : ∀ h' ∈ B.subgroupOf E, (b : ↥E) * h' = h' * (b : ↥E) := by
      intro h' _
      exact (Subgroup.mem_center_iff.mp hbZ h').symm
    have hb1 : (b : ↥E) = 1 := PropA.alt5_subgroup_center eB' b.2 hcomm
    exact Subtype.ext (by simpa using hb1)
  have hbij : Function.Bijective f :=
    hf_inj.bijective_of_nat_card_le (by rw [hcardQ, hcardB])
  have hdecomp : ∀ x : ↥E, ∃ b : ↥(B.subgroupOf E), ∃ z : ↥E, z ∈ Z ∧ x = b * z := by
    intro x
    obtain ⟨b, hb⟩ := hbij.2 (x : ↥E ⧸ Z)
    refine ⟨b, (b : ↥E)⁻¹ * x, ?_, ?_⟩
    · have hqeq : ((b : ↥E) : ↥E ⧸ Z) = ((x : ↥E) : ↥E ⧸ Z) := by
        simpa [f] using hb
      exact (QuotientGroup.eq).mp hqeq
    · rw [mul_inv_cancel_left]
  have hcomm_mem : ∀ x y : ↥E, ⁅x, y⁆ ∈ B.subgroupOf E := by
    intro x y
    obtain ⟨b₁, z₁, hz₁, rfl⟩ := hdecomp x
    obtain ⟨b₂, z₂, hz₂, rfl⟩ := hdecomp y
    have hz₁c : ∀ w : ↥E, z₁ * w = w * z₁ :=
      fun w => (Subgroup.mem_center_iff.mp hz₁ w).symm
    have hz₂c : ∀ w : ↥E, z₂ * w = w * z₂ :=
      fun w => (Subgroup.mem_center_iff.mp hz₂ w).symm
    have hident : ⁅(b₁ : ↥E) * z₁, (b₂ : ↥E) * z₂⁆ = ⁅(b₁ : ↥E), (b₂ : ↥E)⁆ := by
      calc
        ⁅(b₁ : ↥E) * z₁, (b₂ : ↥E) * z₂⁆
            = (b₁ : ↥E) * ⁅z₁, (b₂ : ↥E) * z₂⁆ * (b₁ : ↥E)⁻¹
                * ⁅(b₁ : ↥E), (b₂ : ↥E) * z₂⁆ :=
              commutatorElement_mul_left_eq_conj_mul _ _ _
        _ = (b₁ : ↥E) * 1 * (b₁ : ↥E)⁻¹ * ⁅(b₁ : ↥E), (b₂ : ↥E) * z₂⁆ := by
              rw [show ⁅z₁, (b₂ : ↥E) * z₂⁆ = 1 from
                (commutatorElement_eq_one_iff_mul_comm).mpr (hz₁c _)]
        _ = ⁅(b₁ : ↥E), (b₂ : ↥E) * z₂⁆ := by group
        _ = ⁅(b₁ : ↥E), (b₂ : ↥E)⁆ * (b₂ : ↥E) * ⁅(b₁ : ↥E), z₂⁆ * (b₂ : ↥E)⁻¹ :=
              commutatorElement_mul_right_eq_mul_conj _ _ _
        _ = ⁅(b₁ : ↥E), (b₂ : ↥E)⁆ := by
              rw [show ⁅(b₁ : ↥E), z₂⁆ = 1 from
                (commutatorElement_eq_one_iff_mul_comm).mpr ((hz₂c _).symm)]
              group
    rw [hident]
    have hmem := Subgroup.commutator_mem_commutator b₁.2 b₂.2
    rwa [PropA.alt5_subgroup_perfect eB'] at hmem
  have hle : commutator ↥E ≤ B.subgroupOf E := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm_mem x y
  have htop : B.subgroupOf E = ⊤ := eq_top_iff.mpr (hq.1.commutator_eq_top ▸ hle)
  have hEB : E ≤ B := (Subgroup.subgroupOf_eq_top).mp htop
  exact le_antisymm hBE hEB

end CFSG.EvenSporadicStandard.M12Std.Rbc
