module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Levi

variable {p e : ℕ} [Fact p.Prime]

theorem isLongRoot_f4_of_iform_eq_four {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ)
    (h : iform γ γ = 4) : IsLongRoot .F4 γ :=
  ⟨hγ, fun δ hδ => by rcases iform_self_F4 hδ with h' | h' <;> omega⟩

theorem isLongRoot_f4_of_class_eq (b : Fin Tag.F4.rank → (GaloisField p e)ˣ)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b)))
    (hclass : componentRootSpan (GaloisField p e) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
      rootRankOneGroup .F4 (GaloisField p e) γ) : IsLongRoot .F4 γ := by
  refine isLongRoot_f4_of_iform_eq_four hγ.1 ?_
  rcases iform_self_F4 hγ.1 with h2 | h4
  · exfalso
    obtain ⟨δ, hδ, hδγ, hδγ', hδker, hδ0⟩ :=
      F4_short_root_has_nonorthogonal_kernel_root (signTupleBits b) hγ.1 h2 hγ.2
    have hcls : (⟦⟨γ, hγ⟩⟧ : KernelComponent (maskChar (signTupleBits b))) =
        ⟦⟨δ, ⟨hδ, hδker⟩⟩⟧ := mk_eq_of_iform_ne_zero hδ0
    have hle := rootSubgroup_le_componentRootSpan (GaloisField p e)
      (⟨δ, ⟨hδ, hδker⟩⟩ : kernelRoots (maskChar (signTupleBits b)))
    rw [← hcls, hclass, rootRankOneGroup_eq_sup hγ.1] at hle
    exact not_rootSubgroup_le_rootSubgroup_sup hγ.1 hδ hδγ hδγ' hle
  · exact h4

theorem map_stdRankOne_f4 [NeZero e] :
    (stdRankOne (Generic.modelUniv .F4 0 p e Fact.out).D thetaF4).map (excEmbed .F4 p e) =
      rootRankOneGroup .F4 (GaloisField p e) thetaF4 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨A, hA⟩ := (mem_stdRankOne_f4_iff x).1 hx
    exact ⟨A, hA.symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨⟨rootSL2 .F4 (GaloisField p e) thetaF4 A, rootSL2_mem_adjointGroup _ _⟩,
      (mem_stdRankOne_f4_iff _).2 ⟨A, rfl⟩, rfl⟩

theorem orthBranch_f4 (hadm : StatedLieAdmissible .F4 0 p e) : OrthBranch p .F4 0 e := by
  intro hp2 hq
  have : NeZero e := ⟨by rintro rfl; simp at hq⟩
  have hθ : Generic.IsLongestRoot (Generic.modelUniv .F4 0 p e Fact.out).D thetaF4 :=
    isLongestRoot_f4Datum_of_iform_eq_four isRoot_thetaF4 iform_thetaF4_self
  refine (orthBranch_of_adjointEmbedding (t := .F4) hp2 hq trivial (by decide) (by decide) hadm
    (excEmbed .F4 p e) (fun x => x.2) ?_ (excSignGroup .F4 p e)
    (fun c hc => mem_excSignGroup.1 hc) (pairFrame_f4 hp2 hadm)
    (fundamentalSingleClass .F4 0 p e Fact.out trivial hadm (by decide) (by decide))
    (Rθ := stdRankOne (Generic.modelUniv .F4 0 p e Fact.out).D thetaF4)
    ⟨1, thetaF4, Or.inl hθ, (Generic.conjSub_one _).symm⟩
    (isLongRoot_f4_of_iform_eq_four isRoot_thetaF4 iform_thetaF4_self) map_stdRankOne_f4
    fun b _ hγ hclass => isLongRoot_f4_of_class_eq b hγ hclass) hp2 hq
  change (adjointGroup .F4 (GaloisField p e)).subtype.ker ≤ _
  rw [Subgroup.ker_subtype]
  exact bot_le

end CFSG.ClassicalInvolution.ModelFacts
