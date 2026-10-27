module

public import CFSG.ClassicalInvolution.Q3.TL4AECover
public import CFSG.ClassicalInvolution.Q3.TL4AECoverG

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin

theorem aeCoverElemO2_proved : AECoverElemO2 := by
  intro G _ _ P k I hk hH T hTn hT2 a ha b hb
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hcomm : ∀ L ∈ P, ∀ L' ∈ P, ∀ u u' : G, IsUniqueInvolution L u →
      IsUniqueInvolution L' u' → u * u' = u' * u := fun L hL L' hL' u u' hu hu' =>
    AECov.comm_of_isUniqueInvolution I hk hH.card hH.conj_mem hH.label_inj hH.twin_z hL hL' hu
      hu'
  have hW := AECov.zSpan_elem hcomm
  have hWn := AECov.zSpan_normal hH.conj_mem
  have hUW := AECov.ker_permHom_le_zSpan I (by omega) hH.card hH.conj_mem hH.label_inj
    hH.ker_two hWn hW
  have hTU := AECov.le_ker_permHom_of_normal I hk hTn hT2
  exact hW a (hUW (hTU ha)) b (hUW (hTU hb))

end CFSG.ClassicalInvolution.Q3.TL4
