module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralFive
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeylSeven

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality

variable {τ : Tag}


theorem monomialToralAt_seven_of_chainBlock (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    (hblk : ChainBlockToral τ 6) : MonomialToralAt τ 7 := by
  intro L _ _ hL M _ χ n hn hw h7
  obtain ⟨B, hB, hpair, hprod⟩ := exists_a6Blocks hSL hw h7
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_chains hSL hblk hL B
    (fun β hβ => (hB β hβ).1) hpair n hn hprod
  refine ⟨g, ?_, hgn⟩
  refine (Subgroup.closure_le _).2 ?_ hg
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨β, hβ, hx⟩ := hx
  exact iSup₂_le (fun γ hγ => le_iSup₂_of_le (f := fun δ (_ : δ ∈ kernelRoots χ) =>
    rootSubgroup τ L δ) γ ((hB β hβ).2 hγ) le_rfl) hx

theorem planesToralBar_seven_of_chainBlock (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    (hblk : ChainBlockToral τ 6)
    (hstab : ∀ (L : Type) [Field L] (a : Fin τ.rank → Lˣ), (∀ i, a i ^ 7 = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    PlanesToralBar τ 7 :=
  planesToralBar_of_monomialToral (by norm_num) (monomialToralAt_seven_of_chainBlock hSL hblk)
    hstab

end CFSG.HardMathSupport.Timmesfeld.CrossChar
