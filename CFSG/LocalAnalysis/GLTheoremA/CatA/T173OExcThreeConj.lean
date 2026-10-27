module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeLevi
public import CFSG.LocalAnalysis.GLTheoremA.S9.ClosingB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OConj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X

section Generic


theorem exists_conj_le_of_stdElt_of_levi (τ : Tag) {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M₀ : Subgroup (ModGL τ K)}
    {A : Subgroup ↥(adjointGroup τ K)} {d : ↥(adjointGroup τ K)} (hAel : IsElemAbelian p A)
    (hd : IsStdElt p A d)
    (hLevi : ∀ J : Set (Fin τ.rank), J ≠ Set.univ → ∀ E : Subgroup (ModGL τ K),
      E ≤ parabolicLevi τ K J → IsElemAbelian p E → Nat.card A ≤ Nat.card E →
        parabolicLevi τ K J ≤ M₀)
    {T : Subgroup ↥(adjointGroup τ K)} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTN : innerClosure A d ⊔ A ≤ Subgroup.normalizer (T : Set ↥(adjointGroup τ K))) :
    ∃ g : ↥(adjointGroup τ K),
      (A.map (MulAut.conj g).toMonoidHom).map (adjointGroup τ K).subtype ≤ M₀ ∧
        (stdLayer (MulAut.conj g d)).map (adjointGroup τ K).subtype ≤ M₀ := by
  haveI : Finite (ModGL τ K) := finite_modGL
  have hK : stdLayer d ≤ Subgroup.normalizer (T : Set ↥(adjointGroup τ K)) :=
    (CFSG.LocalAnalysis.GLTheoremA.S9.Cl.le_closureIn_self (stdLayer d)
      (Subgroup.normalizer (A : Set ↥(adjointGroup τ K)))).trans (le_sup_left.trans hTN)
  have hAN : A ≤ Subgroup.normalizer (T : Set ↥(adjointGroup τ K)) := le_sup_right.trans hTN
  obtain ⟨g, J, hJ, hAL, hKP⟩ := exists_conj_le_parabolicLevi_of_le_normalizer τ hT hT2 hAN hK
    hp hp2 hAel.isPGroup
  have hstd := isStdElt_map (MulAut.conj g) hd
  have hdL : ((MulAut.conj g d : ↥(adjointGroup τ K)) : ModGL τ K) ∈ parabolicLevi τ K J :=
    hAL (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hd.1))
  have hKP' : (stdLayer (MulAut.conj g d)).map (adjointGroup τ K).subtype ≤
      parabolicSubgroup τ K J := by
    rw [stdLayer_map_mulEquiv]
    exact hKP
  have hKL := map_subtype_le_parabolicLevi_of_isComponentOf τ J hstd.2.2.2.1 hdL hKP'
  have hEel : IsElemAbelian p
      ((A.map (MulAut.conj g).toMonoidHom).map (adjointGroup τ K).subtype) :=
    (hAel.map (MulAut.conj g).toMonoidHom).map (adjointGroup τ K).subtype
  have hcard : Nat.card A ≤
      Nat.card ((A.map (MulAut.conj g).toMonoidHom).map (adjointGroup τ K).subtype) := by
    rw [Subgroup.card_map_of_injective (adjointGroup τ K).subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hM := hLevi J hJ _ hAL hEel hcard
  exact ⟨g, hAL.trans hM, hKL.trans hM⟩

end Generic

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
