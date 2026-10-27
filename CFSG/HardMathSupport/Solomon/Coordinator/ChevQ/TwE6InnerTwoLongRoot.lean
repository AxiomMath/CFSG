module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootDefs
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootHolds
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLongRoot

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree


theorem eq_top_of_longRoot_le {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    {X Xm : Subgroup (twistedE6RootGroup K σ)} (hpair : IsTwE6LongRootPair K σ X Xm)
    {H R : Subgroup (twistedE6RootGroup K σ)} (hSH : twE6LongRootSL2 X Xm ≤ H)
    (hJH : twE6LongRootLevi X Xm ≤ H) (hRQ : R ≤ twE6LongRootRadical X) (hRH : R ≤ H)
    (hRX : ¬ R ≤ X) : H = ⊤ := by
  classical
  have hXQ := twE6LongRootParabolicStructure_holds K σ q hK3 hσ hK X Xm hpair
  obtain ⟨n, hnS, hn⟩ := twE6LongRootGenerates_holds K σ q hK3 hσ hK X Xm hpair
  have hXS : X ≤ twE6LongRootSL2 X Xm := fun u hu => Subgroup.subset_closure (Or.inl hu)
  have hTS : twE6LongRootTorus X Xm ≤ twE6LongRootSL2 X Xm := inf_le_left.trans inf_le_left
  have hJP : twE6LongRootLevi X Xm ≤ twE6LongRootParabolic X := by
    have h1 : twE6LongRootLevi X Xm ≤
        Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ)) := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    have h2 : Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ)) ≤
        Subgroup.centralizer (X : Set (twistedE6RootGroup K σ)) :=
      Subgroup.centralizer_le fun u hu => hXS hu
    exact h1.trans (h2.trans (Subgroup.centralizer_le_normalizer _))
  have hTP : twE6LongRootTorus X Xm ≤ twE6LongRootParabolic X := inf_le_left.trans inf_le_right
  have hJTP : twE6LongRootLevi X Xm ⊔ twE6LongRootTorus X Xm ≤ twE6LongRootParabolic X :=
    sup_le hJP hTP
  have hJTH : twE6LongRootLevi X Xm ⊔ twE6LongRootTorus X Xm ≤ H :=
    sup_le hJH (hTS.trans hSH)
  have hMnorm : ∀ g ∈ twE6LongRootLevi X Xm ⊔ twE6LongRootTorus X Xm,
      (H ⊓ twE6LongRootRadical X).map (MulAut.conj g).toMonoidHom = H ⊓ twE6LongRootRadical X := by
    intro g hg
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_eq_of_mem H (hJTH hg)]
    congr 1
    exact map_conj_pCoreOf_eq (twE6LongRootParabolic X) (ringChar K) (hJTP hg)
  have hXM : X ≤ H ⊓ twE6LongRootRadical X := le_inf (hXS.trans hSH) hXQ
  rcases twE6LongRootIrreducible_holds K σ q hK3 hσ hK X Xm hpair (H ⊓ twE6LongRootRadical X) hXM
      inf_le_right hMnorm with hMX | hMQ
  · refine absurd (fun u hu => ?_) hRX
    have hu' : u ∈ H ⊓ twE6LongRootRadical X := ⟨hRH hu, hRQ hu⟩
    rw [hMX] at hu'
    exact hu'
  · have hQH : twE6LongRootRadical X ≤ H := by
      intro u hu
      have : u ∈ H ⊓ twE6LongRootRadical X := by
        rw [hMQ]
        exact hu
      exact this.1
    rw [← top_le_iff, ← hn, Subgroup.closure_le]
    rintro u (hu | ⟨v, hv, rfl⟩)
    · exact hQH hu
    · exact H.mul_mem (H.mul_mem (hSH hnS) (hQH hv)) (H.inv_mem (hSH hnS))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
