module

public import CFSG.GH74.GLS.Bg.Iii2.Statements
public import CFSG.GH74.Generic.OuterInvolution

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

private theorem exists_sylow_of_isSylowOf_top {T : Subgroup G} (h : IsSylowOf 2 T ⊤) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  have h' := isSylowOf_iff.1 h
  refine ⟨h'.2.1.toSylow ?_, rfl⟩
  rw [← Subgroup.relIndex_top_right]; exact h'.2.2

theorem false_of_isolated (hG : IsKProperSimple G) {x : G} {T : Subgroup G} (E : ExtData G x T)
    (hiso : ∀ y ∈ T, IsConj x y → y = x) : False := by
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowOf_top E.sylow
  have hxc : ∀ t ∈ (S : Subgroup G), t * x = x * t := fun t ht => by
    rw [hS] at ht
    exact Subgroup.mem_centralizer_singleton_iff.1 (E.le_cent ht)
  obtain ⟨g, hg, hne⟩ := CFSG.GH74.Generic.exists_conj_in_sylow_ne hG.1 hG.2.1 E.ord S
    (hS ▸ E.mem) hxc
  refine hne (hiso _ (hS ▸ hg) ?_)
  exact isConj_iff.2 ⟨g⁻¹, by simp⟩

end CFSG.GH74.GLS.Bg.Iii2
