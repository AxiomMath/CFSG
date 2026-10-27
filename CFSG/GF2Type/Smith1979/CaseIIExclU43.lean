module

public import CFSG.GF2Type.Smith1979.CaseIIExclU43SU

public section

namespace CFSG.GF2Type.Smith1979.Case2

theorem false_of_psu43_frob56 {X : Type} [Group X]
    (hX : CFSG.Open.StatedClassicalModel X .PSU 4 3 1)
    {y : X} (hy : orderOf y = 7) (S : Subgroup X) (hS2 : ∀ s ∈ S, s * s = 1)
    (hS8 : Nat.card S = 8) (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S)
    (hfpf : ∀ s ∈ S, y * s * y⁻¹ = s → s = 1) : False := by
  obtain ⟨-, K, hf, hfin, hK, ⟨e⟩⟩ := hX
  have hK9 : Nat.card K = 9 := by
    rw [hK]
    norm_num
  exact U43SU.false_of_stated hK9 e hy hS2 hS8 hyS hfpf

end CFSG.GF2Type.Smith1979.Case2
