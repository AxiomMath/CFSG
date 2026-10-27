module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

theorem FrobRootMap.weyl_smul_eq
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {D : LangDatum tau L} {rho : Equiv.Perm (Fin tau.rank → ℤ)}
    (hRho : FrobRootMap D rho) (sigma : L ≃+* L)
    (hPhi : D.Φ = frobGL sigma) (w : WeylGroup tau)
    (hn : D.n = canonicalRep (coxeterSystem tau) L w)
    {alpha : Fin tau.rank → ℤ} (halpha : IsRoot tau alpha) :
    w • alpha = rho alpha := by
  have hm : (rootSubgroup tau L alpha).map D.step = rootSubgroup tau L (w • alpha) := by
    rw [LangDatum.step, hPhi, ← Subgroup.map_map]
    change ((rootSubgroup tau L alpha).map (Units.map (entrywiseHom sigma.toRingHom))).map
      (MulAut.conj D.n).toMonoidHom = _
    rw [map_entrywise_rootSubgroup, hn]
    exact CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup w halpha
  have he : rootSubgroup tau L (rho alpha) = rootSubgroup tau L (w • alpha) :=
    (hRho.map_rootSubgroup alpha halpha).symm.trans hm
  have hmem : pinnedX tau L (w • alpha) 1 ∈ rootSubgroup tau L (rho alpha) := by
    rw [he]
    exact mem_rootSubgroup.mpr ⟨1, rfl⟩
  exact eq_of_pinnedX_one_mem_rootSubgroup (IsRoot.smul halpha w)
    ((hRho.isRoot_iff alpha).mpr halpha) hmem

end CFSG.HardMathSupport.Timmesfeld.LangTorus
