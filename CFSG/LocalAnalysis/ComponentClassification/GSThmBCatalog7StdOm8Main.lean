module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8JCase
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8KCase

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer Module

theorem omegaMinus8_holds :
    ∀ (H : Type) [Group H] [Finite H], IsSimpleGroup ↥(generalizedFitting H) →
      centralizer (generalizedFitting H : Set H) = ⊥ →
      ∀ r e : ℕ, r.Prime → r ≠ 2 → 1 ≤ e →
      Blueprint.LieModel ↥(generalizedFitting H) .POmegaMinus 4 r e →
      ∀ a b : H, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      ∀ J K : Subgroup H, J ≤ centralizer ({a} : Set H) →
        IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H))) →
        K ≤ centralizer ({b} : Set H) →
        IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H))) →
        (∀ M : Subgroup H, M ≤ centralizer ({b} : Set H) →
          IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set H))) → M = K) →
        b ∈ coreActionKernel J →
        ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
          Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f →
          ¬ Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p (2 * f) := by
  intro H _ _ _ hC r e hr hr2 he hm a b ha hb _ J Kc hJC hJ hKC hK huniq hbJ p f hp hp2 _ h5
    hJm hKm
  have : (generalizedFitting H).Normal := (LocalCores.generalized_fitting_characteristic (G := H)).2
  obtain ⟨F, _, _, Q, Θ, hF, hQ, hnp, hinv⟩ := exists_model hC hr hr2 he hm
  have : Group.IsSolvable (OuterAutomorphisms.Outer (generalizedFitting H)) :=
    outer_solvable hm (by norm_num)
  have hJG := pComponent_le_of_outer_solvable (generalizedFitting H) hC hJC hJ
  have hKG := pComponent_le_of_outer_solvable (generalizedFitting H) hC hKC hK
  obtain ⟨Da⟩ := hinv a ha
  obtain ⟨Db⟩ := hinv b hb
  have hdim : finrank F (Fin (2 * 4) → F) = 8 := by simp
  obtain ⟨hnsb, hpf⟩ := k_analysis hr hr2 he hF hQ hdim hnp Db Kc hKC hKG hK huniq hp hp2 h5 hKm
  exact j_analysis hr hr2 he hF hQ hdim hnp Da Db hnsb J hJC hJG hJ hbJ hp hp2 hJm hpf

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
