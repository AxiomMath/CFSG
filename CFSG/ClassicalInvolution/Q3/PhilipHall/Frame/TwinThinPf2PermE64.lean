module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2DataE64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

set_option maxRecDepth 100000 in
theorem perm_cover : ∀ p : Equiv.Perm (Fin 7),
    (∀ s ∈ fanoLines, s.map p.toEmbedding ∈ fanoLines ∧ s.map p⁻¹.toEmbedding ∈ fanoLines) →
      Equiv.Perm.sign p = 1 → ∃ t ∈ permWords, pc t.1 = p := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
