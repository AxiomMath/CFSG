module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269SSp6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem i269Residual_of_sp6
    (h : ∀ (S : Type) [Group S], catalogIs S
      (fun i => S9.isD4two i ∨ S9.isTD4two i ∨ S9.isU3eight i) → E9Solv S) :
    I269Residual := by
  intro S _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with h1 | h1 | h1 | h1
  · exact e9Solv_sp6two S ⟨i, h1, ⟨e⟩⟩
  · exact h S ⟨i, Or.inl h1, ⟨e⟩⟩
  · exact h S ⟨i, Or.inr (Or.inl h1), ⟨e⟩⟩
  · exact h S ⟨i, Or.inr (Or.inr h1), ⟨e⟩⟩

theorem i269At_of_residual2
    (h : ∀ (S : Type) [Group S], catalogIs S (fun i => S9.isD4two i ∨ S9.isU3eight i) → E9Solv S)
    (hTD4 : ∀ (S : Type) [Group S], catalogIs S S9.isTD4two → E9Solv S)
    (G : Type) [Group G] [Finite G] : I269At G := by
  refine i269At_of_residual (i269Residual_of_sp6 ?_) G
  intro S _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with h1 | h1 | h1
  · exact h S ⟨i, Or.inl h1, ⟨e⟩⟩
  · exact hTD4 S ⟨i, h1, ⟨e⟩⟩
  · exact h S ⟨i, Or.inr h1, ⟨e⟩⟩

end CFSG.LocalAnalysis.GLTheoremA

end
