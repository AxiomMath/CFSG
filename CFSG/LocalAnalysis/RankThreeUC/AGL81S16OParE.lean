module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParD
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParW

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n p : ℕ} {M L V : Subgroup G}

theorem O6NatData.parabolic (d : O6NatData G n L V) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hn : 1 ≤ n) (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T M →
      ∃ P R : Subgroup G, P ≤ L ∧ R ≤ T ∧ 2 ≤ CFSG.Open.pRank p P ∧
        ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
          (∀ B : Subgroup G, B ≤ A → B.relIndex A < 2 ^ (2 * n) →
            V ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G)) →
          A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) → ∀ a ∈ A, ∀ x ∈ P, ⁅x, a⁆ ∈ R :=
  d.parabolic_of_inputs hn hLM hML hMV
    (fun hli hw hu hwu => exists_gl_isometry_pair d.irred hli hw hu hwu)
    (fun Y hY2 hYs => d.exists_lift_stab_plane hp hpq hn hLM Y hY2 hYs)

end CFSG.LocalAnalysis.RankThreeUC
