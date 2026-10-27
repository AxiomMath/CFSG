module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyOutMcL
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyOutClass
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThreeAux

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup Equiv Equiv.Perm CFSG CFSG.Blueprint CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.McLAS CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem lyThreeAOuter_of_mcl
    (hMcL : McLNoThreeNormalized) : LyThreeAOuter := by
  intro Y _ _ hY x hx3 _ A hA hAn W hW hWn hAW
  obtain ⟨e⟩ := hY
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly ⟨e⟩)
  obtain ⟨x₁, x₂, x₃, S⟩ := D.exists_lyStd
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_x₁_of_normalizes_sylow ⟨e⟩ D S hx3 hA hAn)
  have hAn' := map_conj_le_normalizer_zpowers c hAn
  have hWn' := map_conj_le_normalizer_zpowers c hWn
  rw [hc] at hAn' hWn'
  have key := lyThreeA_core_of_mcl hMcL D S (A := A.map (MulAut.conj c).toMonoidHom)
    (by rw [card_map_conj, hA]) hAn' (W := W.map (MulAut.conj c).toMonoidHom)
    (isPGroup_map_conj c hW) hWn' (map_conj_le_normalizer c hAW)
  exact le_zpowers_of_map_conj c x (by rw [hc]; exact key)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
