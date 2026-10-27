module

public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Block
public import CFSG.LieType.Universal.Spin.Generation.Eichler

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge.Twisted CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  QuadraticMap

variable (F : Type) [Field F]

theorem plusVec_coord {F : Type} [Field F] (j : Fin 4) (t : Bool) :
    ∃ x : Coord, cIdx x = j ∧ plusVec 4 F j t = Pi.single x 1 := by
  cases t
  · exact ⟨.inr j, rfl, rfl⟩
  · exact ⟨.inl j, rfl, rfl⟩

theorem rS_mul_self (k : Fin 24) : ((rS k : ℤ) : F) * ((rS k : ℤ) : F) = 1 := by
  rcases (rootData_spec k).2 with h | h <;> rw [h] <;> simp

theorem range_blockRep_le : (blockRep F).range ≤ elementaryGroup (quadPlus 4 F) := by
  rintro _ ⟨g, rfl⟩
  obtain ⟨x, hx⟩ := g
  have hx' : x ∈ Subgroup.closure {g | ∃ γ, IsRoot Tag.D4 γ ∧ ∃ c : F,
      g = d4tData_valid.xu F γ c} := hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ, hγ, c, rfl⟩ := hy
    obtain ⟨k, rfl⟩ := exists_root_eq_d4 hγ
    have := blockRep_xm (F := F) k c
    change blockRep F (d4tData_valid.xm F (Tag.D4.rootCertificate.root k) c) ∈ _
    rw [this]
    exact eichler_mem_elementaryGroup _ _ _
  | one =>
    change blockRep F 1 ∈ _
    rw [map_one]
    exact one_mem _
  | mul y z hy hz ihy ihz =>
    change blockRep F (⟨y, hy⟩ * ⟨z, hz⟩) ∈ _
    rw [map_mul]
    exact mul_mem (ihy hy) (ihz hz)
  | inv y hy ihy =>
    change blockRep F (⟨y, hy⟩⁻¹) ∈ _
    rw [map_inv]
    exact inv_mem (ihy hy)

theorem elementaryGroup_le_range_blockRep : elementaryGroup (quadPlus 4 F) ≤ (blockRep F).range := by
  refine (plusFrame 4 F (by norm_num)).elementaryGroup_le (H := (blockRep F).range) ?_ ?_ ?_
  · intro i j hij s t c
    obtain ⟨x, hx, hxe⟩ := plusVec_coord (F := F) j t
    obtain ⟨y, hy, hye⟩ := plusVec_coord (F := F) i s
    have hxy : cIdx x ≠ cIdx y := by rw [hx, hy]; exact hij.symm
    change eichler (quadPlus 4 F) (plusVec 4 F j t) (c • plusVec 4 F i s) ∈ _
    rw [hxe, hye]
    obtain ⟨k, hk | hk⟩ := rootData_cover x y hxy
    · refine ⟨d4tData_valid.xm F (Tag.D4.rootCertificate.root k) (((rS k : ℤ) : F) * c), ?_⟩
      rw [blockRep_xm, hk.1, hk.2, ← mul_assoc, rS_mul_self, one_mul]
    · refine ⟨d4tData_valid.xm F (Tag.D4.rootCertificate.root k)
        (((rS k : ℤ) : F) * (-c)), ?_⟩
      rw [blockRep_xm, hk.1, hk.2, ← mul_assoc, rS_mul_self, one_mul,
        ← eichler_single_swap hxy c]
  · intro i s v hv
    have : v = 0 := eq_zero_of_polar_plusVec hv
    rw [this]
    change eichler (quadPlus 4 F) _ 0 ∈ _
    rw [eichler_zero_right]
    exact one_mem _
  · exact fun v h _ => eq_zero_of_polar_plusVec h

theorem range_blockRep : (blockRep F).range = elementaryGroup (quadPlus 4 F) :=
  le_antisymm (range_blockRep_le F) (elementaryGroup_le_range_blockRep F)

end CFSG.HardMathSupport.Lang.D4Three
