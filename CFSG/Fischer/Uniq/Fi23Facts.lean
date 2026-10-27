module

public import CFSG.Fischer.Uniq.F24Hyperoval
public import CFSG.Sporadic.Fi23.Centralizer

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer CFSG.Sporadic.Fi23

structure Fi23Facts (tr cs : Set (Set D23)) (r : tr) : Prop where
  classify : ∀ T : Set D23, IsLocally351 D23 (Subtype.val '' T) → T.Nonempty → T ∈ cs ∨ T ∈ tr
  cs_not_inj : ∀ Ω ∈ cs, ∃ v w, v ∉ Ω ∧ w ∉ Ω ∧ v ≠ w ∧
    (pairModel pair_J).tv v '' Ω = (pairModel pair_J).tv w '' Ω
  ncard_of_mem_tr : ∀ T ∈ tr, T.ncard = 3240
  ncard_tr : tr.ncard = 137632
  injOn_tv_image : ∀ T ∈ tr, Set.InjOn (fun f => (pairModel pair_J).tv f '' T) Tᶜ
  tv_image_ne : ∀ T ∈ tr, ∀ f ∉ T, (pairModel pair_J).tv f '' T ≠ T
  exists_not_commute : ∀ T ∈ tr, ∀ f ∉ T, ∃ x ∈ T, ¬ ((f : J) * x = x * f)
  xi24_D2 : ∀ v, v ≠ r → ¬ ((pairModel pair_J).xi tr).Adj r v →
    ∃ x, ((pairModel pair_J).xi tr).Adj r x ∧ ((pairModel pair_J).xi tr).Adj x v
  xi24_MU : ∀ v, v ≠ r → ¬ ((pairModel pair_J).xi tr).Adj r v →
    (((pairModel pair_J).xi tr).induce
      {x | ((pairModel pair_J).xi tr).Adj r x ∧ ((pairModel pair_J).xi tr).Adj x v}).Connected
  xi24_ED : ∀ v w, v ≠ r → ¬ ((pairModel pair_J).xi tr).Adj r v → w ≠ r →
    ¬ ((pairModel pair_J).xi tr).Adj r w → ((pairModel pair_J).xi tr).Adj v w →
    ∃ x, ((pairModel pair_J).xi tr).Adj r x ∧ ((pairModel pair_J).xi tr).Adj x v ∧
      ((pairModel pair_J).xi tr).Adj x w

end CFSG.Fischer
