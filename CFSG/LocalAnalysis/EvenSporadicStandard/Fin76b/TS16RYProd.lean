module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UTool

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem card_sup_commuting_two {G : Type} [Group G] [Finite G] {S E : Subgroup G} {t : G}
    (hSE : S ≤ centralizer (E : Set G)) (hint : ∀ x ∈ S, x ∈ E → x = 1 ∨ x = t)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htS : t ∈ S) (htE : t ∈ E) :
    Nat.card ↥(S ⊔ E) * 2 = Nat.card ↥S * Nat.card ↥E := by
  have hx2 : ((⟨t, htS⟩, ⟨t, htE⟩) : ↥S × ↥E) * (⟨t, htS⟩, ⟨t, htE⟩) = 1 :=
    Prod.ext (Subtype.ext ht2) (Subtype.ext ht2)
  have hker : (mulHom S E hSE).ker ≤ zpowers ((⟨t, htS⟩, ⟨t, htE⟩) : ↥S × ↥E) := by
    rintro ⟨s, e⟩ hp
    have h1 : (s : G) * (e : G) = 1 := hp
    have hse : (s : G) ∈ E := by
      have := E.inv_mem e.2
      rwa [← eq_inv_of_mul_eq_one_left h1] at this
    have he : (e : G) = (s : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rcases hint (s : G) s.2 hse with h | h
    · have hs1 : s = 1 := Subtype.ext h
      have he1 : e = 1 := Subtype.ext (by simp [he, h])
      rw [hs1, he1]
      exact one_mem _
    · have hs1 : s = ⟨t, htS⟩ := Subtype.ext h
      have he1 : e = ⟨t, htE⟩ :=
        Subtype.ext (by rw [he, h]; exact inv_eq_of_mul_eq_one_right ht2)
      rw [hs1, he1]
      exact mem_zpowers _
  have hord : orderOf ((⟨t, htS⟩, ⟨t, htE⟩) : ↥S × ↥E) ≤ 2 :=
    orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hx2)
  have hker2 : Nat.card (mulHom S E hSE).ker ≤ 2 := by
    have h3 := Subgroup.card_le_of_le hker
    rw [Nat.card_zpowers] at h3
    exact h3.trans hord
  have hne : (mulHom S E hSE).ker ≠ ⊥ := by
    intro h
    have hmem : ((⟨t, htS⟩ : S), (⟨t, htE⟩ : E)) ∈ (mulHom S E hSE).ker := by
      rw [MonoidHom.mem_ker]; exact ht2
    rw [h, Subgroup.mem_bot] at hmem
    exact ht1 (congrArg (fun p : ↥S × ↥E => (p.1 : G)) hmem)
  have h2 : 2 ≤ Nat.card (mulHom S E hSE).ker :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hK := card_ker_mul_card_range S E hSE
  have hr1 : Nat.card ↥(S ⊔ E) ≤ Nat.card (mulHom S E hSE).range :=
    Subgroup.card_le_of_le (sup_le_range_mulHom S E hSE)
  have hr2 : Nat.card (mulHom S E hSE).range ≤ Nat.card ↥(S ⊔ E) :=
    Subgroup.card_le_of_le (range_mulHom_le S E hSE)
  have hk : Nat.card (mulHom S E hSE).ker = 2 := le_antisymm hker2 h2
  have hr : Nat.card (mulHom S E hSE).range = Nat.card ↥(S ⊔ E) := le_antisymm hr2 hr1
  rw [hk, hr] at hK
  omega

end CFSG.EvenSporadicStandard.Fin76b
