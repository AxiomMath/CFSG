module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.PPartCyclic
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CoprimeSubgroupCyclic
public import CFSG.GroupTheory.CoprimeActionSupport.FiniteAbelianPrimaryComplement
public import CFSG.GroupTheory.CyclicSubgroup.CoprimeJoin

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem actor_isCyclic {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) : IsCyclic B := by
  have hab := h.oddPrimeClassTwoAction.setting.abelian
  obtain ⟨A, hAB, hAp, hsup, hcop⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.FiniteAbelianPrimaryComplement.exists_complement h.oddPrimeClassTwoAction.setting.prime hab
  have hD := actor_primeCore_isCyclic h
  have hA := isCyclic_of_le_actor_of_coprime_card h A hAB hAp
  have hDB : CFSG.Open.pCoreOf p B ≤ B := by
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le p B
  have hc : ∀ a ∈ CFSG.Open.pCoreOf p B, ∀ d ∈ A, Commute a d := fun a ha d hd =>
    hab.is_comm.comm ⟨a, hDB ha⟩ ⟨d, hAB hd⟩ |> fun x => by
      simpa [Commute, SemiconjBy, Subtype.ext_iff] using congrArg Subtype.val x
  have := CFSG.GroupTheory.CyclicSubgroup.isCyclic_sup_of_coprime _ _ hD hA hc hcop
  rw [hsup] at this
  exact this

end Section5
end CFSG.LocalAnalysis.RankThreeUC
