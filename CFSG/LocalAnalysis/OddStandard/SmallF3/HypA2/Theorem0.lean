module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.PropV
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaD

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem residual_of_violation (hI : Phase1Inputs) (hL : Leaves1) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) → Assembly.KProper Catalog G → ¬ Catalog G →
    (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
    ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x * y = y * x →
    ∀ X K : Subgroup G,
      X ≤ centralizer ({x, y} : Set G) →
      IsPComponent 2 (X.subgroupOf (centralizer ({x, y} : Set G))) →
      K ≤ centralizer ({y} : Set G) → IsPComponent 2 (K.subgroupOf (centralizer ({y} : Set G))) →
      X ≤ K ⊔ K.map (MulAut.conj x).toMonoidHom → IsFStar ↥X → ¬ IsFStar ↥K →
      IsResidualA2 ↥K := by
  intro G _ _ _ hnonab hKP hcat hbal x y ox oy comm X K hXle hXc hKle hKc hXKK hX hK
  have hcfg : A2Config G x y X K :=
    ⟨ox, oy, comm, hXle, hXc, hKle, hKc, hXKK⟩
  have hKcomp : Omega.IsComponentIn K (centralizer ({y} : Set G)) :=
    (a2Config_cases (hbal y oy) hcfg).1
  rcases residual_or_kDatum_of_violation hI hL hnonab hKP hbal hcfg hX hK with hres | hdat
  · exact hres
  · exfalso
    exact false_of_kDatum hI hL.twoA7RankOne G hnonab hKP hcat hbal y K oy hKcomp hdat

theorem hypA2_of_smallF3Cyclic (hI : Phase1Inputs) (hL : Leaves1) (G : Type) [Group G]
    [Finite G] (L : Subgroup G) (h : SmallF3Cyclic G L) (hcat : ¬ Catalog G)
    (hres : NoResidualA2 G) : HypA2 G := by
  intro x y X K hcfg hX
  by_contra hK
  haveI := h.simple
  exact hres x y X K hcfg hX
    (residual_of_violation hI hL G h.nonab h.kProper hcat h.balanced x y hcfg.ox hcfg.oy
      hcfg.comm X K hcfg.X_le hcfg.X_comp hcfg.K_le hcfg.K_comp hcfg.X_le_KK hX hK)

end CFSG.OddStandard.SmallF3.HypA2
