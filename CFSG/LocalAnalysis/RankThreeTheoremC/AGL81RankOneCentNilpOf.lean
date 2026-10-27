module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

theorem prime_of_isStepThreeIndex {p : ℕ} {i : TauCeti.CFSGIndex} (h : IsStepThreeIndex p i) :
    p.Prime := by
  cases i with
  | cyclic _ _ => exact h.elim
  | alternating n _ => rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  | lie d => rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  | sporadic s => rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num

theorem StepThreeGroup.prime {p : ℕ} {K : Type*} [Group K] (h : StepThreeGroup p K) :
    p.Prime := by
  obtain ⟨_, hi, -⟩ := h
  exact prime_of_isStepThreeIndex hi

theorem kFactStepThreeCentNilp_of_centSylow (h5 : KFactStepThreeCentSylow) :
    KFactStepThreeCentNilp := by
  intro p A _ _ K S hKn hC hK hS
  haveI : Fact p.Prime := ⟨hK.prime⟩
  obtain ⟨P⟩ : Nonempty (Sylow p ↥(Subgroup.centralizer (S : Set A))) := inferInstance
  refine CFSG.hasNormalPComplement_of_sylow_le_center_normalizer p P fun x hx => ?_
  refine ⟨Subgroup.le_normalizer hx, Subgroup.mem_centralizer_iff.2 fun y _ => ?_⟩
  obtain ⟨n, hn⟩ := P.isPGroup' ⟨x, hx⟩
  have hxn : (x : A) ^ (p ^ n) = 1 := by
    have h := congrArg (fun g : ↥(P : Subgroup ↥(Subgroup.centralizer (S : Set A))) =>
      ((g : ↥(Subgroup.centralizer (S : Set A))) : A)) hn
    simpa using h
  have hxS : (x : A) ∈ S := h5 p A K S hKn hC hK hS x x.2 n hxn
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 y.2 _ hxS).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
