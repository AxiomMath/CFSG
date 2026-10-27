module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.McL
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.RankThree.PartTwo.KFacts.K426McL

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.RankThree.PartTwo.KFacts.K426

private theorem no_surj_alt6_of_mulEquiv
    {G : Type*} [Group G] (φ : G ≃* NativeSporadic.McL) {s : G} (hs : orderOf s = 3)
    {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({s} : Set G))
    (f : ↥K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f) : False := by
  have hKc : K.map (φ : G →* NativeSporadic.McL) ≤
      Subgroup.centralizer ({φ s} : Set NativeSporadic.McL) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hK hk)
    show φ k * φ s = φ s * φ k
    rw [← map_mul, ← map_mul, h]
  have hφs : orderOf (φ s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs
  have ψ : ↥K ≃* ↥(K.map (φ : G →* NativeSporadic.McL)) :=
    Subgroup.equivMapOfInjective K (φ : G →* NativeSporadic.McL) φ.injective
  exact mclThreeCentralizer (φ s) hφs _ hKc (f.comp (ψ.symm : _ →* _))
    (hf.comp ψ.symm.surjective)

theorem sporNoPumpup_McL
    (hSpM : SporadicMultipliers)
    (hOG : UniquenessMaximal.InputONGroup) (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    SporNoPumpup .McL := by
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (hbr .McL).some.toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  · exact OPrimeCoreTrivialAt.of_mulEquiv (hbr .McL).some.symm oPrimeCoreTrivialAt_McL
  · intro s hs K hK h
    rcases h with ⟨_, _, ⟨f⟩⟩ | ⟨h, _⟩
    · exact no_surj_alt6_of_mulEquiv (hbr .McL).some.symm hs hK.1
        (f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))
        (f.surjective.comp (QuotientGroup.mk'_surjective _))
    · exact absurd h (by decide)
  · intro _ s hs K hK ⟨f⟩
    exact (no_surj_alt6_of_mulEquiv (hbr .McL).some.symm hs hK.1 f.toMonoidHom f.surjective).elim

end CFSG.HardMathSupport.Solomon.Coordinator
