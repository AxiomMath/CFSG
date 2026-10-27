module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Main

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Levi

variable {p e : ℕ} [Fact p.Prime]

theorem map_stdRankOne_e8 [NeZero e] :
    (stdRankOne (Generic.modelUniv .E8 0 p e Fact.out).D thetaE8).map (excEmbed .E8 p e) =
      rootRankOneGroup .E8 (GaloisField p e) thetaE8 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨A, hA⟩ := (mem_stdRankOne_e8_iff x).1 hx
    exact ⟨A, hA.symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨⟨rootSL2 .E8 (GaloisField p e) thetaE8 A, rootSL2_mem_adjointGroup _ _⟩,
      (mem_stdRankOne_e8_iff _).2 ⟨A, rfl⟩, rfl⟩

theorem orthBranch_e8 (hadm : StatedLieAdmissible .E8 0 p e) : OrthBranch p .E8 0 e := by
  intro hp2 hq
  have : NeZero e := ⟨by rintro rfl; simp at hq⟩
  have hlong : ∀ k : Fin (Generic.modelUniv .E8 0 p e Fact.out).D.rank,
      Generic.IsLongestRoot (Generic.modelUniv .E8 0 p e Fact.out).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .E8 0 p e Fact.out trivial hadm k trivial
  have hθ : Generic.IsLongestRoot (Generic.modelUniv .E8 0 p e Fact.out).D thetaE8 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl hlong (mem_adjDatum_roots.2 isRoot_thetaE8)
  refine (orthBranch_of_adjointEmbedding (t := .E8) hp2 hq trivial (by decide) (by decide) hadm
    (excEmbed .E8 p e) (fun x => x.2) ?_ (excSignGroup .E8 p e)
    (fun c hc => mem_excSignGroup.1 hc) (pairFrame_e8 hp2 hadm)
    (fundamentalSingleClass .E8 0 p e Fact.out trivial hadm (by decide) (by decide))
    (Rθ := stdRankOne (Generic.modelUniv .E8 0 p e Fact.out).D thetaE8)
    ⟨1, thetaE8, Or.inl hθ, (Generic.conjSub_one _).symm⟩
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inr rfl)) isRoot_thetaE8) map_stdRankOne_e8
    fun _ γ hγ _ => isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inr rfl)) hγ.1) hp2 hq
  change (adjointGroup .E8 (GaloisField p e)).subtype.ker ≤ _
  rw [Subgroup.ker_subtype]
  exact bot_le

end CFSG.ClassicalInvolution.ModelFacts
