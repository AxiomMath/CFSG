module

public import CFSG.CGT.T75E.UtiRoot
public import CFSG.CGT.Timmesfeld75.ListWCBasic

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {K : Type} [Group K] {T : Subgroup K}

theorem hyp_normalizer_transitive (h : Lemma26Hyp K T) :
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set K), g * x * g⁻¹ = y :=
  h.1.transitive_of_isConj fun _ hx hx1 _ hy hy1 =>
    hyp_isConj_of_mem_classD h (mem_classD_of_mem hx hx1) (mem_classD_of_mem hy hy1)

theorem hyp_centralizer_le_normalizer (h : Lemma26Hyp K T) {t : K} (ht : t ∈ T) (ht1 : t ≠ 1) :
    Subgroup.centralizer ({t} : Set K) ≤ Subgroup.normalizer (T : Set K) :=
  h.1.centralizer_le_normalizer ht ht1

theorem hyp_false_of_isCoatom_centralizer [Finite K] [IsSimpleGroup K] (h : Lemma26Hyp K T)
    {a : K} (ha : a ∈ T) (ha1 : a ≠ 1) (hmax : IsCoatom (Subgroup.centralizer ({a} : Set K))) :
    False := by
  have hCN := hyp_centralizer_le_normalizer h ha ha1
  rcases hmax.le_iff.1 hCN with hN | hN
  swap
  ·
    have hsub : (T : Set K) ⊆ {1, a} := fun b hb => by
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · obtain ⟨g, hg, hga⟩ := hyp_normalizer_transitive h a ha ha1 b hb hb1
        rw [hN, Subgroup.mem_centralizer_singleton_iff] at hg
        refine Or.inr ?_
        rw [← hga]
        rw [hg, mul_assoc, mul_inv_cancel, mul_one]
        exact Set.mem_singleton a
    have h1 : (T : Set K).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le 1 {a}).trans (by rw [Set.ncard_singleton]))
    have h2 : Nat.card T = (T : Set K).ncard := Nat.card_coe_set_eq (T : Set K)
    have h3 := h.2.1
    omega
  ·
    have hTn : T.Normal := ⟨fun n hn g => by
      have hg : g ∈ Subgroup.normalizer (T : Set K) := by rw [hN]; exact Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with hT | hT
    · exact hyp_ne_bot h hT
    · exact hyp_ne_top h hT

end CFSG.CGT.T75E
