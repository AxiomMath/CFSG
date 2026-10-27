module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallGlue
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzHyperGoodIn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem i141f_g2_noCube {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (h : catalogIs S rsG2Char2) {E : Subgroup S} (hE : IsElemAbelian p E)
    (h3 : p ^ 3 ≤ Nat.card E) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | G2 q =>
      have hq : q.p = 2 := hi
      haveI : Finite (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.G2 q, hv⟩).Group :=
        Finite.of_equiv S e.toEquiv
      have hEm : IsElemAbelian p (E.map e.toMonoidHom) := isElemAbelian_map e.toMonoidHom hE
      have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
        Subgroup.card_map_of_injective e.injective
      obtain ⟨E₀, -, hE₀, hc₀⟩ := i141f_exists_cube hp hEm (by rw [hcard]; exact h3)
      have hpq : p ≠ q.p := fun hpq => hp2 (hpq.trans hq)
      exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzHyperGoodInAux.no_cube_G2
        (d := ⟨TauCeti.LieTypeIndex.G2 q, hv⟩) ⟨q, rfl⟩ hp hp2 (by simpa using hpq) hE₀ hc₀
    | _ => exact absurd hi (by simp [onLie])
  | _ => exact absurd hi (by simp [onLie])

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
