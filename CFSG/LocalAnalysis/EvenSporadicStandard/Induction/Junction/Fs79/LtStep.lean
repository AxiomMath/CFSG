module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Swap
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Defs

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup Relation CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem ltF_conn (hcor : ∀ (G : Type) [Group G] [Finite G],
      CFSG.SignalizerFunctorTheorem.IsSectionOf G H → Nat.card G < Nat.card H → Cor23SAt G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {A B : Subgroup H} (h : LtF A B) (hA : NotExc A) : LConn A B := by
  obtain ⟨s, t, hs, ht, hst, hA', hB', hAB⟩ := h
  by_cases hne : B.map (MulAut.conj s).toMonoidHom = B
  · have hAB' : A ≤ B := by rwa [hne, sup_idem] at hAB
    have hss : s * s = 1 := Solomon78.mul_self_eq_one_of_orderOf_eq_two hs
    have ht2 : IsPGroup 2 ↥(zpowers t) := isPGroup_zpowers_of_orderOf_two ht
    have hsN : s ∈ normalizer ((zpowers t : Subgroup H) : Set H) :=
      mem_normalizer_zpowers_of_commute hst
    have hsT : s ^ 2 ∈ zpowers t := by
      rw [pow_two, hss]
      exact one_mem _
    have hT : zpowers t ≠ ⊥ := fun h => by
      rw [Subgroup.zpowers_eq_bot] at h
      rw [h, orderOf_one] at ht
      omega
    have hM : IsCompIn B (centralizer ((zpowers t : Subgroup H) : Set H)) := by
      rw [centralizer_zpowers_eq]
      exact hB'
    have htB : t ∈ normalizer (B : Set H) :=
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun b hb =>
        mem_centralizer_singleton_iff.1 (hB'.1 hb))
    have hsB : s ∈ normalizer (B : Set H) := Solomon78.mem_normalizer_iff_map_conj_eq.2 hne
    have hK : IsCompIn A (centralizer ((zpowers t ⊔ zpowers s : Subgroup H) : Set H)) := by
      rw [centralizer_sup_zpowers_eq]
      exact isCompIn_of_le hA' (le_inf (hAB'.trans hB'.1) hA'.1) inf_le_right
    exact (junction_base hcor hkp hT ht2 hM (isPGroup_sup_zpowers ht2 hsN hsT) le_sup_left
      (sup_le Subgroup.le_normalizer (zpowers_le.2 hsN))
      (sup_le (zpowers_le.2 htB) (zpowers_le.2 hsB)) hK hAB' hA).toLConn
  · exact ⟨1, _, _, _, ltF_links_swap hs ht hst hA' hB' hAB hne, by simp, by simp,
      fun _ _ _ => trivial⟩

theorem transGen_ltF_conn (hD : Sol78ExcClosed)
    (hcor : ∀ (G : Type) [Group G] [Finite G],
      CFSG.SignalizerFunctorTheorem.IsSectionOf G H → Nat.card G < Nat.card H → Cor23SAt G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {K M : Subgroup H} (h : TransGen LtF K M) (hK : NotExc K) : LConn K M := by
  induction h with
  | single h => exact ltF_conn hcor hkp h hK
  | tail _ h ih => exact ih.trans (ltF_conn hcor hkp h (ih.notExc hD hK))

end CFSG.EvenSporadicStandard.Induction.Junction
