module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107XChk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X

open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def psiE6 : Fin 16 → (Fin Tag.E6.rank → ℤ) :=
  ![![1, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 1],
    ![1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 0],
    ![1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 0],
    ![1, 1, 1, 2, 1, 1],
    ![1, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 1, 0],
    ![1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1],
    ![1, 2, 2, 3, 2, 1]]

theorem psiE6_ok : PsiOK Tag.E6 (List.ofFn psiE6) = true := by decide +kernel

theorem psiE6_nodup : (List.ofFn psiE6).Nodup := by decide +kernel

theorem psiE6_chain : ∀ γ ∈ List.ofFn psiE6,
    ∃ β β' : Fin Tag.E6.rank → ℤ, chainOK Tag.E6 (List.ofFn psiE6) γ β β' = true := by
  intro γ hγ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hγ
  fin_cases i
  · exact ⟨![0, 1, 1, 2, 2, 1], ![0, 0, 1, 1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 1, 2, 2, 1], ![0, 1, 0, 1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 1, 2, 2, 1], ![0, 0, -1, -1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 1], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, 0, -1], ![0, 1, 0, 1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 1, 2, 2, 1], ![0, -1, -1, -1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -1, -1, 0], ![0, 0, 1, 1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, 0, -1], ![0, 0, 1, 1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -2, -1, 0], ![0, 1, 1, 1, 1, 1], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, 0, -1], ![0, 0, 1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, -1, -1, -1], ![0, 0, 0, 0, -1, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -1, -1, 0], ![0, 1, 0, 1, 1, 1], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, 0, -1], ![0, 0, -1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -1, -1, 0], ![0, 0, -1, -1, -1, -1], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -2, -1, 0], ![0, 0, -1, -1, -1, -1], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -1, -1, 0], ![0, -1, 0, -1, -1, -1], by decide +kernel⟩

@[expose] def psiE7 : Fin 16 → (Fin Tag.E7.rank → ℤ) :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0],
    ![1, 0, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 1, 0],
    ![1, 1, 1, 1, 0, 0, 0],
    ![1, 1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 1, 0],
    ![1, 1, 1, 2, 1, 0, 0],
    ![1, 1, 1, 2, 1, 1, 0],
    ![1, 1, 1, 2, 2, 1, 0],
    ![1, 1, 2, 2, 1, 0, 0],
    ![1, 1, 2, 2, 1, 1, 0],
    ![1, 1, 2, 2, 2, 1, 0],
    ![1, 1, 2, 3, 2, 1, 0],
    ![1, 2, 2, 3, 2, 1, 0]]

theorem psiE7_ok : PsiOK Tag.E7 (List.ofFn psiE7) = true := by decide +kernel

theorem psiE7_nodup : (List.ofFn psiE7).Nodup := by decide +kernel

theorem psiE7_chain : ∀ γ ∈ List.ofFn psiE7,
    ∃ β β' : Fin Tag.E7.rank → ℤ, chainOK Tag.E7 (List.ofFn psiE7) γ β β' = true := by
  intro γ hγ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hγ
  fin_cases i
  · exact ⟨![0, 0, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 1, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 1, 1, 1, 1, 0], ![0, 0, 0, 0, -1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, 0, -1, 0], ![0, 1, 1, 1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 1, 1, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -1, -1, 0, 0], ![0, 0, 1, 1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -2, -1, 0, 0], ![0, 1, 1, 1, 1, 1, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, -1, -1, -1, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, -1, -1, -1, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -1, -1, 0, 0], ![0, 0, 0, 0, 1, 1, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, 1, 0, 0], ![0, 0, -1, 0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -1, -1, 0, 0], ![0, 1, 0, 1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -2, -1, 0, 0], ![0, 0, 0, -1, -1, -1, 0], by decide +kernel⟩
  · exact ⟨![0, -1, -1, -1, -1, 0, 0], ![0, -1, 0, -1, 0, 0, 0], by decide +kernel⟩

@[expose] def psiE8 : Fin 16 → (Fin Tag.E8.rank → ℤ) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 2, 1, 0, 0, 0],
    ![1, 1, 1, 2, 1, 1, 0, 0],
    ![1, 1, 1, 2, 2, 1, 0, 0],
    ![1, 1, 2, 2, 1, 0, 0, 0],
    ![1, 1, 2, 2, 1, 1, 0, 0],
    ![1, 1, 2, 2, 2, 1, 0, 0],
    ![1, 1, 2, 3, 2, 1, 0, 0],
    ![1, 2, 2, 3, 2, 1, 0, 0]]

theorem psiE8_ok : PsiOK Tag.E8 (List.ofFn psiE8) = true := by decide +kernel

theorem psiE8_nodup : (List.ofFn psiE8).Nodup := by decide +kernel

theorem psiE8_chain : ∀ γ ∈ List.ofFn psiE8,
    ∃ β β' : Fin Tag.E8.rank → ℤ, chainOK Tag.E8 (List.ofFn psiE8) γ β β' = true := by
  intro γ hγ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hγ
  fin_cases i
  · exact ⟨![0, 1, 1, 2, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 1, 2, 1, 1, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 1, 1, 1, 1, 0, 0], ![0, 0, -1, -1, 0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 1, 2, 1, 1, 0, 0], ![0, 0, -1, -1, -1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, -1, -1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 1, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 1, 1, 2, 1, 1, 0, 0], ![0, -1, 0, -1, -1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, 0, -1, -1, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, -1, 0, -1, -1, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, 0, -1, 0, 0, 0, 0], ![0, -1, 0, -1, -1, -1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, -1, 0, -1, -1, 0, 0, 0], ![0, 0, 0, 0, -1, -1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, -1, 0, 0], by decide +kernel⟩
  · exact ⟨![0, 0, -1, -1, -1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨![0, -1, 0, -1, -1, 0, 0, 0], ![0, -1, -1, -1, 0, 0, 0, 0], by decide +kernel⟩

end CFSG.LocalAnalysis.GLTheoremA.I107X

end
