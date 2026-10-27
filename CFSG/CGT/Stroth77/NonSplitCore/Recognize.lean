module

public import CFSG.CGT.Stroth77.NonSplitCore.Core
public import CFSG.CGT.Stroth77.NonSplit.Recognition

public section

namespace CFSG.CGT.Stroth77

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm Function
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
  CFSG.Permutation.SymmetricCoxeter

theorem exists_mulEquiv_Mns_of_nonsplit
    {G : Type*} [Group G] (θ : G →* Perm (Fin 6))
    (hθ : Surjective θ) (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hconj : ∀ (g : G) (v : Multiplicative (altHeart 6)), g * (ψ v : G) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : G))
    (hns : ¬ ∃ K : Subgroup G, θ.ker ⊓ K = ⊥ ∧ θ.ker ⊔ K = ⊤) :
    ∃ e : Mns ≃* G, (∀ v, e (ψns v : Mns) = (ψ v : G)) ∧ ∀ m, θ (e m) = θns m := by
  obtain ⟨t, hθt, hsq, hbr, hcm⟩ := Core.exists_tits_lifts θ hθ ψ hconj hns
  exact exists_mulEquiv_Mns θ hθ ψ hconj t hθt hsq hbr hcm

theorem map_Qns_eq_ker {G : Type*} [Group G] (θ : G →* Perm (Fin 6)) (e : Mns ≃* G)
    (he : ∀ m, θ (e m) = θns m) : Qns.map e.toMonoidHom = θ.ker := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    show θ (e m) = 1
    rw [he]; exact hm
  · intro hg
    refine ⟨e.symm g, ?_, by simp⟩
    show θns (e.symm g) = 1
    rw [← he, MulEquiv.apply_symm_apply]; exact hg

end CFSG.CGT.Stroth77
