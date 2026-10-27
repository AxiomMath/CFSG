module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.AltDown
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Main
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Two

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def L34SporBranch (s : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ α : MulAut Y, α ^ 3 = 1 → ∀ J : Subgroup Y,
      GLAPComponent 3 (Lemma510Ns.fixSub α) J → ¬ IsLThreeFour (barOf 3 J)

@[expose] def L34LieBranch : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    ∀ idx : TauCeti.ValidLieTypeIndex,
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ α : MulAut Y, α ^ 3 = 1 → ∀ J : Subgroup Y,
      GLAPComponent 3 (Lemma510Ns.fixSub α) J → IsLThreeFour (barOf 3 J) →
        IsCharTwoLieIndex idx.1

theorem chevTwo_of_branches (hS : ∀ s, L34SporBranch s) (hL : L34LieBranch)
    (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hKK : CFSG.Open.IsKGroup ↥K) (hK3 : GLAPPrimeCore 3 ↥K = ⊥) (b : Y)
    (hb : b ∈ Subgroup.normalizer (K : Set Y)) (hb3 : b ^ 3 ∈ Subgroup.centralizer (K : Set Y))
    (J : Subgroup Y) (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) J)
    (hJL : IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J)) : IsChevTwo (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨α, J', hα, hJ', ⟨eJ⟩⟩ := component_to_aut K hb hb3 hJ
  have hJL' : IsLThreeFour (barOf 3 J') := IsLThreeFour.of_mulEquiv eJ.symm hJL
  obtain ⟨hnab, i, ⟨e⟩⟩ := I1420.catalog_of_quasisimple hKq hKK
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, c, hac⟩ := hnab
    apply hac
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact absurd hJL' (l34Alt_holds ↥K hKq ⟨n, ⟨e⟩⟩ α hα J' hJ')
  | lie idx => exact ⟨idx, hL ↥K hKq hK3 idx ⟨e⟩ α hα J' hJ' hJL', ⟨e⟩⟩
  | sporadic s => exact absurd hJL' (hS s ↥K hKq hK3 ⟨e⟩ α hα J' hJ')

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
