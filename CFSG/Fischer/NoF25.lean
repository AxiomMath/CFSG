module

public import CFSG.Fischer.NoF25.Main
public import CFSG.Sporadic.Fi24.StarRigid
public import CFSG.Sporadic.Fi24.Octads

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

theorem not_F25
    {X : Type} [Group X] {E : Set X} (hP : Pair X E) {e : X} (he : e ∈ E)
    (hT : F24 (LocalQuotient E e) (LocalImages E e))
    (hZe : Subgroup.center (LocalQuotient E e) = ⊥)
    (hSe : IsSimpleGroup (commutator (LocalQuotient E e))) : False := by
  have hFF := Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts
  exact false_of_strongPoints hP Sporadic.Fi24.pair_R
    (Sporadic.Fi24.tauGroup_D24_eq_range polarFacts hyperovalFacts hFF
      (Sporadic.Fi23.fi23Facts hFF))
    (fun hq hp θ hθ => Sporadic.Fi24.exists_conj_of_star_equiv_D24 hq hp θ hθ)
    Sporadic.Fi24.Bbar Sporadic.Fi24.Bbar_subset_D24 Sporadic.Fi24.ncard_Bbar
    Sporadic.Fi24.Bbar_commute (by rw [ncard_Oset]; exact Sporadic.Fi24.ncard_fixSets_Bbar) he
    (nonempty_strongPoints_D24 hP he hT hZe hSe)

end CFSG.Fischer
