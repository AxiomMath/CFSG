module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ExcLift
import CFSG.RankThree.PartTwo.Sec4.Census.Symplectic46
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open scoped MatrixGroups

theorem p3At_C_of_four_le {n : ℕ} (hn : 4 ≤ n) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C n Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  set Fd := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C n Q, hv⟩) with hFd
  set E := CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj n Q hv with hE
  set π := QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) Fd).subgroupOf (StatedSp n Fd))
  let idx : Fin 4 → Fin n := fun i => ⟨i, by omega⟩
  have hidx : ∀ i j, i ≠ j → idx i ≠ idx j := fun i j hij h => by
    have h' := congrArg Fin.val h
    exact hij (Fin.ext h')
  refine H.false_of_commuting_SL2_fixedField e hchar
    (fun i => E.symm.toMonoidHom.comp (π.comp (lam (idx i))))
    (fun i => E.symm.injective.comp
      (CFSG.RankThree.PartTwo.Sec4.Census.mk_lam_injective_of_ne (l := idx (i + 1))
        (hidx _ _ ?_)))
    (fun i j hij A B => ?_)
  · intro h
    have := congrArg (fun x : Fin 4 => x - i) h
    simp at this
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, (commute_lam_lam (hidx i j hij) A B).eq]

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
