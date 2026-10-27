module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallG2Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallG2NoCube

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem i141RankG2Char2_holds : I141RankG2Char2 := by
  intro p hp hp2 Γ _ _ L A hcat hA hInn hcard
  obtain ⟨E, hE, hE3, hEA⟩ := i141f_exists_elemAb hp hA hInn hcard
  obtain ⟨n, hn⟩ : ∃ n, catalogIs (PSimple p L) (S10.isG2n n) := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | G2 q => exact ⟨q.exponent, TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩, ⟨hi, rfl⟩, ⟨e⟩⟩
      | _ => exact absurd hi (by simp [onLie])
    | _ => exact absurd hi (by simp [onLie])
  have hinn : E ≤ (MulAut.conj : PSimple p L →* MulAut (PSimple p L)).range := by
    intro ε hε
    obtain ⟨a, ha, haA, rfl⟩ := hEA ε hε
    obtain ⟨s, hs⟩ := i141f_g2_inner hn hInn haA
    exact ⟨s, hs.symm⟩
  have hZ := i141f_center_pSimple (i141f_isPerfect_pQuot hInn)
  obtain ⟨P, hP, hPc⟩ := i141f_elemAb_of_le_inn hZ hE hinn
  exact i141f_g2_noCube hp hp2 hcat hP (hPc ▸ hE3)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
