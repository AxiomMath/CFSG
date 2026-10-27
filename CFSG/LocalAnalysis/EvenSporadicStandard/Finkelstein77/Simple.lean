module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
public import CFSG.CGT.PushingUpLit.SolK.GenFour

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77

open Subgroup CFSG.GH74 CFSG.CGT.PushingUpLit.SolK

theorem not_inZStar_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {x : G} (hx : orderOf x = 4) : ¬ InZStar (x ^ 2) := by
  rintro ⟨N, hN, hodd, hcomm⟩
  have hz1 : x ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hx] at this
    omega
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · have hcen : x ^ 2 ∈ center G := by
      rw [mem_center_iff]
      intro g
      have h := hcomm g
      rw [mem_bot] at h
      calc g * x ^ 2 = g * x ^ 2 * g⁻¹ * (x ^ 2)⁻¹ * x ^ 2 * g := by group
        _ = x ^ 2 * g := by rw [h, one_mul]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · rw [h, mem_bot] at hcen
      exact hz1 hcen
    · obtain ⟨a, b, hab⟩ := hnonab
      have hb : b ∈ center G := h ▸ mem_top b
      exact hab (mem_center_iff.mp hb a)
  · rw [Subgroup.card_top] at hodd
    have h4 : 4 ∣ Nat.card G := hx ▸ orderOf_dvd_natCard x
    have h2 : 2 ∣ Nat.card G := (by norm_num : 2 ∣ 4).trans h4
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem sectionalTwoRankLE_normalClosure_of_lemma25 (h25 : Asc76Lemma25) {G : Type} [Group G]
    [Finite G] {x : G} (hx : orderOf x = 4) (hW : WeaklyClosedInNormalizer (zpowers x))
    (hZ : ¬ InZStar (x ^ 2)) : SectionalTwoRankLE (normalClosure {x ^ 2} : Subgroup G) 2 := by
  rcases h25 G x hx hW with h | hD | hSD
  · exact absurd h hZ
  · exact gen2_of_dihedral_or_semidihedral (Or.inl hD)
  · exact gen2_of_dihedral_or_semidihedral (Or.inr hSD)

theorem sectionalTwoRankLE_of_lemma25 (h25 : Asc76Lemma25) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {x : G} (hx : orderOf x = 4)
    (hW : WeaklyClosedInNormalizer (zpowers x)) : SectionalTwoRankLE G 2 := by
  have hz1 : x ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hx] at this
    omega
  have hX : (normalClosure {x ^ 2} : Subgroup G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (normalClosure {x ^ 2} : Subgroup G) with h | h
    · exfalso
      have hmem : x ^ 2 ∈ (normalClosure {x ^ 2} : Subgroup G) :=
        subset_normalClosure (Set.mem_singleton _)
      rw [h, mem_bot] at hmem
      exact hz1 hmem
    · exact h
  exact SectionalTwoRankLE.of_mulEquiv ((MulEquiv.subgroupCongr hX).trans topEquiv)
    (sectionalTwoRankLE_normalClosure_of_lemma25 h25 hx hW (not_inZStar_of_simple hnonab hx))

end CFSG.EvenSporadicStandard.Finkelstein77
