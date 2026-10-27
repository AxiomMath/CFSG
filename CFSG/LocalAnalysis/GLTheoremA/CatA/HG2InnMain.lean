module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HG2InnLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HG2InnTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InndiagInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.HG2Inn

section Main


theorem t266G2Inn_holds : ∀ n, T266G2Inn n := by
  intro n Ω _ _ K A hcat hZ hO hInn a ha
  obtain ⟨hA, hM⟩ := hInn
  obtain ⟨hn2, hD⟩ := g2Datum_of_marking hcat hM
  have hlab : GLAInLambda2 (⟨.G2, 0, n⟩ : GLALabel) :=
    show 1 ≤ n ∧ (0 = 0 ∧ 2 ≤ n) from ⟨by omega, rfl, hn2⟩
  have hX := rk2_inndiag_subset_inn_of_notDerived hlab (by simp) (by simp) (by simp) (by simp) _ hD
  obtain ⟨R', _, I', F', hQ'⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hX
  obtain ⟨⟨-, -, θ', hP'⟩, hI'⟩ := hQ'
  obtain ⟨φ, hφI, hφ⟩ := hP' a ha
  obtain ⟨r, rfl⟩ := hI' hφI
  exact exists_conj_of_induces hA hZ hO θ' ha hφ

end Main

end CFSG.LocalAnalysis.GLTheoremA.T266

end
